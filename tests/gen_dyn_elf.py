#!/usr/bin/env python3
"""Generate linked SBPF programs exercising the precompile rules.

Each program has a .rodata section holding IDs, an exported `entrypoint`, and
calls to `sol_memcmp_` through R_BPF_64_32 dynamic relocations, as deployed
(stripped) programs do. The memcmp wrapper copies the shape of the toolchain's
memcmp found on mainnet (Zynko1Dup7Cv2quEqLRuCs9Ds8vwELrWZk4eTLFXVCL, from
instruction 78726): save s2 in r8, branch on a size computed from n, and on the
large-size path restore r2 from r8, point r4 at a stack slot and call
sol_memcmp_; the small-size path compares inline (here simply returns).

  rule_compare_via_wrapper.so   entrypoint: memcmp(key, ED25519, 32) through
                                the wrapper. Expected: Ed25519 id_compared
                                (dependent), sysvar not compared.
  rule_compare_with_sysvar.so   as above, then memcmp(acct, INSTRUCTIONS_SYSVAR, 32).
                                Expected: Ed25519 id_compared, sysvar compared.
  rule_wrapper_rearranged.so    the wrapper adds 8 to r2 before sol_memcmp_, so
                                it does not forward its arguments unchanged.
                                Expected: Ed25519 id_passed (review).
  rule_id_passed.so             ED25519 and 32 passed to a function that only
                                logs. Expected: Ed25519 id_passed (review).
  rule_unreferenced.so          ED25519 in .rodata, never loaded.
                                Expected: bytes_unreferenced (not dependent).
  rule_compare_direct_syscall.so  sol_memcmp_(key, ED25519, 32, &out) called
                                directly, no wrapper. Expected: id_compared.

usage: gen_rule_fixtures.py OUT_DIR
"""
import struct
import sys
from pathlib import Path

B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
EM_BPF, ET_DYN = 247, 3
R_BPF_64_RELATIVE, R_BPF_64_32 = 8, 10


def b58decode(s):
    n = 0
    for c in s:
        n = n * 58 + B58.index(c)
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    return b"\0" * (len(s) - len(s.lstrip("1"))) + body


ED25519 = b58decode("Ed25519SigVerify111111111111111111111111111")
SYSVAR = b58decode("Sysvar1nstructions1111111111111111111111111")


def ins(opc, dst=0, src=0, off=0, imm=0):
    return [struct.pack("<BBhi", opc, (src << 4) | dst, off, imm)]


def lddw(dst, v):
    return [struct.pack("<BBhI", 0x18, dst, 0, v & 0xFFFFFFFF), struct.pack("<BBhI", 0, 0, 0, v >> 32)]


MOV_IMM, MOV_REG, ADD_IMM, CALL, EXIT, JGT_IMM = 0xB7, 0xBF, 0x07, 0x85, 0x95, 0x25


def build(text_fn, rodata_items, syscalls):
    """text_fn(rodata_addr: dict name->vaddr, call_to: fn(from, to)->insn) -> (list of
    8-byte slots, {slot: syscall name})."""
    off_text = 0x40 + 2 * 0x38
    # Lay out rodata after text; text size depends only on slot count, so build twice.
    probe, _ = text_fn({k: 0 for k, _ in rodata_items})
    off_rodata = off_text + 8 * len(probe)
    addrs, rodata = {}, b""
    for name, blob in rodata_items:
        addrs[name] = off_rodata + len(rodata)
        rodata += blob
    slots, sys_at = text_fn(addrs)
    text = b"".join(slots)

    names = ["entrypoint"] + syscalls
    dynstr = b"\0" + b"".join(n.encode() + b"\0" for n in names)
    sym_name = {n: dynstr.index(n.encode() + b"\0") for n in names}
    shstr = b"\0.text\0.rodata\0.dynsym\0.dynstr\0.rel.dyn\0.dynamic\0.shstrtab\0"
    sname = lambda s: shstr.index(s.encode() + b"\0")

    off_dynsym = off_rodata + len(rodata)
    off_dynsym += (-off_dynsym) % 8
    dynsym_len = 24 * (1 + len(names))
    off_dynstr = off_dynsym + dynsym_len
    off_rel = off_dynstr + len(dynstr)
    off_rel += (-off_rel) % 8
    rels = []
    for slot, name in sorted(sys_at.items()):
        rels.append(struct.pack("<QQ", off_text + 8 * slot, ((2 + syscalls.index(name)) << 32) | R_BPF_64_32))
    # lddw instructions pointing into .rodata carry R_BPF_64_RELATIVE, as in legacy programs.
    for i in range(len(slots) - 1):
        if slots[i][0] == 0x18 and off_rodata <= struct.unpack_from("<I", slots[i], 4)[0] < off_dynsym:
            rels.append(struct.pack("<QQ", off_text + 8 * i, R_BPF_64_RELATIVE))
    rel = b"".join(rels)
    off_dyn = off_rel + len(rel)
    dyn_len = 8 * 16
    off_shstr = off_dyn + dyn_len
    off_sh = off_shstr + len(shstr)
    off_sh += (-off_sh) % 8
    nsec = 8
    total = off_sh + nsec * 64

    sym = lambda n, info, shndx, value: struct.pack("<IBBHQQ", n, info, 0, shndx, value, 0)
    GLOBAL_FUNC = (1 << 4) | 2
    dynsym = sym(0, 0, 0, 0) + sym(sym_name["entrypoint"], GLOBAL_FUNC, 1, off_text)
    dynsym += b"".join(sym(sym_name[n], (1 << 4), 0, 0) for n in syscalls)
    dyn = b"".join(struct.pack("<qQ", t, v) for t, v in [
        (6, off_dynsym), (5, off_dynstr), (10, len(dynstr)), (11, 24),
        (17, off_rel), (18, len(rel)), (19, 16), (0, 0)])
    phdrs = (struct.pack("<IIQQQQQQ", 1, 5, 0, 0, 0, total, total, 8)
             + struct.pack("<IIQQQQQQ", 2, 6, off_dyn, off_dyn, off_dyn, dyn_len, dyn_len, 8))
    sh = lambda n, t, flags, off, size, link=0, info=0, ent=0, addr=None: struct.pack(
        "<IIQQQQIIQQ", n, t, flags, off if addr is None else addr, off, size, link, info, 8, ent)
    shdrs = (sh(0, 0, 0, 0, 0)
             + sh(sname(".text"), 1, 6, off_text, len(text))
             + sh(sname(".rodata"), 1, 2, off_rodata, len(rodata))
             + sh(sname(".dynsym"), 11, 2, off_dynsym, dynsym_len, link=4, info=1, ent=24)
             + sh(sname(".dynstr"), 3, 2, off_dynstr, len(dynstr))
             + sh(sname(".rel.dyn"), 9, 2, off_rel, len(rel), link=3, ent=16)
             + sh(sname(".dynamic"), 6, 3, off_dyn, dyn_len, link=4, ent=16)
             + sh(sname(".shstrtab"), 3, 0, off_shstr, len(shstr), addr=0))
    ident = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
    header = ident + struct.pack("<HHIQQQIHHHHHH", ET_DYN, EM_BPF, 1, off_text, 0x40, off_sh,
                                 0, 64, 0x38, 2, 64, nsec, nsec - 1)
    out = bytearray(total)
    for off, blob in [(0, header), (0x40, phdrs), (off_text, text), (off_rodata, rodata),
                      (off_dynsym, dynsym), (off_dynstr, dynstr), (off_rel, rel),
                      (off_dyn, dyn), (off_shstr, shstr), (off_sh, shdrs)]:
        out[off:off + len(blob)] = blob
    return bytes(out)


def assemble(parts):
    """parts: list of (label or None, slots or ('call', label) or ('syscall', name))."""
    pos, slot = {}, 0
    for label, item in parts:
        if label:
            pos[label] = slot
        slot += 1 if isinstance(item, tuple) else len(item)
    slots, sys_at, slot = [], {}, 0
    for _, item in parts:
        if isinstance(item, tuple) and item[0] == "call":
            slots += ins(CALL, src=1, imm=pos[item[1]] - slot - 1)
            slot += 1
        elif isinstance(item, tuple) and item[0] == "syscall":
            slots += ins(CALL, imm=-1)
            sys_at[slot] = item[1]
            slot += 1
        else:
            slots += item
            slot += len(item)
    return slots, sys_at


def memcmp_wrapper(label, rearrange=False):
    """The toolchain memcmp's structure (slots relative to the wrapper's start):
       0  r8 = r2            save s2
       1  r5 = r3            n
       2  if r5 > 15 goto 5  large sizes take the syscall path
       3  r0 = 0             small sizes: compared inline (elided here)
       4  exit
       5  r4 = r10           result slot on the stack
       6  r4 += -4
       7  r2 = r8            restore s2  (rearranged variant: then r2 += 8)
       .  call sol_memcmp_
       .  exit
    """
    return [
        (label, ins(MOV_REG, 8, 2)),
        (None, ins(MOV_REG, 5, 3)),
        (None, ins(JGT_IMM, 5, 0, 2, 15)),
        (None, ins(MOV_IMM, 0, imm=0) + ins(EXIT)),
        (None, ins(MOV_REG, 4, 10) + ins(ADD_IMM, 4, imm=-4)),
        (None, ins(MOV_REG, 2, 8) + (ins(ADD_IMM, 2, imm=8) if rearrange else [])),
        (None, ("syscall", "sol_memcmp_")),
        (None, ins(EXIT)),
    ]


def caller(id_name, target, extra=lambda addr: []):
    """entrypoint: r1 = r10 - 64 (a key on the stack); r2 = &ID; r3 = 32; call target."""
    def parts(addr):
        return [
            ("entrypoint", ins(MOV_REG, 1, 10) + ins(ADD_IMM, 1, imm=-64)),
            (None, lddw(2, addr[id_name])),
            (None, ins(MOV_IMM, 3, imm=32)),
            (None, ("call", target)),
            *extra(addr),
            (None, ins(EXIT)),
        ]
    return parts


def program(parts_fn, rodata, syscalls):
    return build(lambda addr: assemble(parts_fn(addr)), rodata, syscalls)


def main():
    d = Path(sys.argv[1])
    d.mkdir(parents=True, exist_ok=True)
    rodata = [("ed25519", ED25519), ("sysvar", SYSVAR)]

    def with_wrapper(rearrange=False, extra=lambda a: []):
        return lambda a: caller("ed25519", "memcmp", extra)(a) + memcmp_wrapper("memcmp", rearrange)

    (d / "rule_compare_via_wrapper.so").write_bytes(program(with_wrapper(), rodata, ["sol_memcmp_"]))

    second = lambda a: [
        (None, ins(MOV_REG, 1, 10) + ins(ADD_IMM, 1, imm=-128)),
        (None, lddw(2, a["sysvar"])),
        (None, ins(MOV_IMM, 3, imm=32)),
        (None, ("call", "memcmp")),
    ]
    (d / "rule_compare_with_sysvar.so").write_bytes(program(with_wrapper(extra=second), rodata, ["sol_memcmp_"]))
    (d / "rule_wrapper_rearranged.so").write_bytes(program(with_wrapper(rearrange=True), rodata, ["sol_memcmp_"]))

    logger = lambda a: caller("ed25519", "log_it")(a) + [
        ("log_it", ins(MOV_REG, 1, 2) + ins(MOV_IMM, 2, imm=32)),
        (None, ("syscall", "sol_log_")),
        (None, ins(EXIT)),
    ]
    (d / "rule_id_passed.so").write_bytes(program(logger, rodata, ["sol_log_"]))

    unref = lambda a: [("entrypoint", ins(MOV_IMM, 0, imm=0) + ins(EXIT))]
    (d / "rule_unreferenced.so").write_bytes(program(unref, rodata, []))

    direct = lambda a: [
        ("entrypoint", ins(MOV_REG, 1, 10) + ins(ADD_IMM, 1, imm=-64)),
        (None, lddw(2, a["ed25519"])),
        (None, ins(MOV_IMM, 3, imm=32)),
        (None, ins(MOV_REG, 4, 10) + ins(ADD_IMM, 4, imm=-8)),
        (None, ("syscall", "sol_memcmp_")),
        (None, ins(EXIT)),
    ]
    (d / "rule_compare_direct_syscall.so").write_bytes(program(direct, rodata, ["sol_memcmp_"]))


if __name__ == "__main__":
    main()
