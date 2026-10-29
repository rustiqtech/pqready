#!/usr/bin/env python3
"""Generate minimal Solana-style ET_DYN SBPF ELFs for parser tests.

Each program does `r1 = 1; call sol_curve_group_op; exit`, with the call
patched by an R_BPF_64_32 dynamic relocation against an undefined symbol.

  unmapped.so: .dynsym/.dynstr/.rel.dyn lie outside every PT_LOAD segment, so
               DT_SYMTAB/DT_STRTAB/DT_REL addresses cannot be mapped to file
               offsets through program headers (goblin then reads offset 0).
  mapped.so:   one PT_LOAD covers the whole file (control).
  lddw64.so:   `lddw r2, 0x10` patched by R_BPF_64_64 against a defined data
               symbol `ID` (st_value = 0x2000), so the loaded value is 0x2010.
  reldata.so:  a function pointer in .data.rel.ro patched by R_BPF_64_RELATIVE,
               stored as the loader reads it (32-bit address at r_offset + 4).
               The pointed-to function calls sol_curve_group_op(1, ...) and is
               reachable only through that pointer.

usage: gen_dyn_elf.py OUT_DIR
"""
import struct
import sys
from pathlib import Path

EM_BPF, ET_DYN = 247, 3
PT_LOAD, PT_DYNAMIC = 1, 2
SHT_PROGBITS, SHT_STRTAB, SHT_DYNAMIC, SHT_REL, SHT_DYNSYM = 1, 3, 6, 9, 11
R_BPF_64_32 = 10


def insn(opc, dst=0, src=0, off=0, imm=0):
    return struct.pack("<BBhi", opc, (src << 4) | dst, off, imm)


def build(mapped: bool, lddw64: bool = False) -> bytes:
    if lddw64:
        # lddw r2, imm_lo = 0x10 (implicit addend), imm_hi = 0x77 (ignored by the loader)
        text = insn(0x18, dst=2, imm=0x10) + insn(0, imm=0x77) + insn(0x95)
        dynstr = b"\0entrypoint\0ID\0"
    else:
        text = insn(0xB7, dst=1, imm=1) + insn(0x85, imm=-1) + insn(0x95)
        dynstr = b"\0entrypoint\0sol_curve_group_op\0"
    shstr = b"\0.text\0.dynsym\0.dynstr\0.rel.dyn\0.dynamic\0.shstrtab\0"
    name = lambda s: shstr.index(s.encode() + b"\0")

    off_text = 0x40 + 2 * 0x38                       # after header + 2 phdrs
    off_dynsym = off_text + len(text)
    dynsym_len = 3 * 24
    off_dynstr = off_dynsym + dynsym_len
    off_rel = off_dynstr + len(dynstr)
    off_rel += (-off_rel) % 8
    off_dyn = off_rel + 16
    dyn_len = 8 * 16
    off_shstr = off_dyn + dyn_len
    off_sh = off_shstr + len(shstr)
    off_sh += (-off_sh) % 8
    nsec = 7
    total = off_sh + nsec * 64

    sym = lambda n, info, shndx, value: struct.pack("<IBBHQQ", n, info, 0, shndx, value, 0)
    STB_GLOBAL_FUNC = (1 << 4) | 2
    STB_GLOBAL_OBJECT = (1 << 4) | 1
    if lddw64:
        dynsym = (sym(0, 0, 0, 0)
                  + sym(dynstr.index(b"entrypoint"), STB_GLOBAL_FUNC, 1, off_text)
                  + sym(dynstr.index(b"ID"), STB_GLOBAL_OBJECT, 3, 0x2000))
        rel = struct.pack("<QQ", off_text, (2 << 32) | 1)  # R_BPF_64_64 at the lddw
    else:
        dynsym = (sym(0, 0, 0, 0)
                  + sym(dynstr.index(b"entrypoint"), STB_GLOBAL_FUNC, 1, off_text)
                  + sym(dynstr.index(b"sol_curve_group_op"), STB_GLOBAL_FUNC, 0, 0))
        rel = struct.pack("<QQ", off_text + 8, (2 << 32) | R_BPF_64_32)
    dyn = b"".join(struct.pack("<qQ", t, v) for t, v in [
        (6, off_dynsym), (5, off_dynstr), (10, len(dynstr)), (11, 24),
        (17, off_rel), (18, 16), (19, 16), (0, 0)])

    load_size = total if mapped else len(text)
    load_off = 0 if mapped else off_text
    phdrs = (struct.pack("<IIQQQQQQ", PT_LOAD, 5, load_off, load_off, load_off, load_size, load_size, 8)
             + struct.pack("<IIQQQQQQ", PT_DYNAMIC, 6, off_dyn, off_dyn, off_dyn, dyn_len, dyn_len, 8))

    sh = lambda n, t, flags, off, size, link=0, info=0, ent=0: struct.pack(
        "<IIQQQQIIQQ", n, t, flags, off, off, size, link, info, 8, ent)
    shdrs = (sh(0, 0, 0, 0, 0)
             + sh(name(".text"), SHT_PROGBITS, 6, off_text, len(text))
             + sh(name(".dynsym"), SHT_DYNSYM, 2, off_dynsym, dynsym_len, link=3, info=1, ent=24)
             + sh(name(".dynstr"), SHT_STRTAB, 2, off_dynstr, len(dynstr))
             + sh(name(".rel.dyn"), SHT_REL, 2, off_rel, 16, link=2, ent=16)
             + sh(name(".dynamic"), SHT_DYNAMIC, 3, off_dyn, dyn_len, link=3, ent=16)
             + sh(name(".shstrtab"), SHT_STRTAB, 0, off_shstr, len(shstr)))
    # .shstrtab section header has sh_addr = 0 in real files
    shdrs = shdrs[:-64] + struct.pack("<IIQQQQIIQQ", name(".shstrtab"), SHT_STRTAB, 0, 0,
                                      off_shstr, len(shstr), 0, 0, 1, 0)

    ident = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
    header = ident + struct.pack("<HHIQQQIHHHHHH", ET_DYN, EM_BPF, 1, off_text, 0x40, off_sh,
                                 0, 64, 0x38, 2, 64, nsec, nsec - 1)
    out = bytearray(total)
    for off, blob in [(0, header), (0x40, phdrs), (off_text, text), (off_dynsym, dynsym),
                      (off_dynstr, dynstr), (off_rel, rel), (off_dyn, dyn),
                      (off_shstr, shstr), (off_sh, shdrs)]:
        out[off:off + len(blob)] = blob
    return bytes(out)


def build_reldata() -> bytes:
    # entrypoint: r0 = 0; exit.  handler: r1 = 1; call sol_curve_group_op; exit
    text = (insn(0xB7, dst=0, imm=0) + insn(0x95)
            + insn(0xB7, dst=1, imm=1) + insn(0x85, imm=-1) + insn(0x95))
    dynstr = b"\0entrypoint\0sol_curve_group_op\0"
    shstr = b"\0.text\0.data.rel.ro\0.dynsym\0.dynstr\0.rel.dyn\0.dynamic\0.shstrtab\0"
    name = lambda s: shstr.index(s.encode() + b"\0")

    off_text = 0x40 + 2 * 0x38
    off_handler = off_text + 16
    off_data = off_text + len(text)
    off_dynsym = off_data + 8
    off_dynstr = off_dynsym + 3 * 24
    off_rel = off_dynstr + len(dynstr)
    off_rel += (-off_rel) % 8
    off_dyn = off_rel + 32
    dyn_len = 8 * 16
    off_shstr = off_dyn + dyn_len
    off_sh = off_shstr + len(shstr)
    off_sh += (-off_sh) % 8
    nsec = 8
    total = off_sh + nsec * 64

    sym = lambda n, info, shndx, value: struct.pack("<IBBHQQ", n, info, 0, shndx, value, 0)
    STB_GLOBAL_FUNC = (1 << 4) | 2
    dynsym = (sym(0, 0, 0, 0)
              + sym(dynstr.index(b"entrypoint"), STB_GLOBAL_FUNC, 1, off_text)
              + sym(dynstr.index(b"sol_curve_group_op"), STB_GLOBAL_FUNC, 0, 0))
    data = bytes(4) + struct.pack("<I", off_handler)       # address at r_offset + 4
    rel = (struct.pack("<QQ", off_data, 8)                  # R_BPF_64_RELATIVE, no symbol
           + struct.pack("<QQ", off_text + 24, (2 << 32) | R_BPF_64_32))
    dyn = b"".join(struct.pack("<qQ", t, v) for t, v in [
        (6, off_dynsym), (5, off_dynstr), (10, len(dynstr)), (11, 24),
        (17, off_rel), (18, 32), (19, 16), (0, 0)])
    phdrs = (struct.pack("<IIQQQQQQ", PT_LOAD, 5, 0, 0, 0, total, total, 8)
             + struct.pack("<IIQQQQQQ", PT_DYNAMIC, 6, off_dyn, off_dyn, off_dyn, dyn_len, dyn_len, 8))
    sh = lambda n, t, flags, off, size, link=0, info=0, ent=0, addr=None: struct.pack(
        "<IIQQQQIIQQ", n, t, flags, off if addr is None else addr, off, size, link, info, 8, ent)
    shdrs = (sh(0, 0, 0, 0, 0)
             + sh(name(".text"), SHT_PROGBITS, 6, off_text, len(text))
             + sh(name(".data.rel.ro"), SHT_PROGBITS, 3, off_data, 8)
             + sh(name(".dynsym"), SHT_DYNSYM, 2, off_dynsym, 3 * 24, link=4, info=1, ent=24)
             + sh(name(".dynstr"), SHT_STRTAB, 2, off_dynstr, len(dynstr))
             + sh(name(".rel.dyn"), SHT_REL, 2, off_rel, 32, link=3, ent=16)
             + sh(name(".dynamic"), SHT_DYNAMIC, 3, off_dyn, dyn_len, link=4, ent=16)
             + sh(name(".shstrtab"), SHT_STRTAB, 0, off_shstr, len(shstr), addr=0))
    ident = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
    header = ident + struct.pack("<HHIQQQIHHHHHH", ET_DYN, EM_BPF, 1, off_text, 0x40, off_sh,
                                 0, 64, 0x38, 2, 64, nsec, nsec - 1)
    out = bytearray(total)
    for off, blob in [(0, header), (0x40, phdrs), (off_text, text), (off_data, data),
                      (off_dynsym, dynsym), (off_dynstr, dynstr), (off_rel, rel),
                      (off_dyn, dyn), (off_shstr, shstr), (off_sh, shdrs)]:
        out[off:off + len(blob)] = blob
    return bytes(out)


if __name__ == "__main__":
    d = Path(sys.argv[1])
    d.mkdir(parents=True, exist_ok=True)
    (d / "unmapped.so").write_bytes(build(False))
    (d / "mapped.so").write_bytes(build(True))
    (d / "lddw64.so").write_bytes(build(True, lddw64=True))
    (d / "reldata.so").write_bytes(build_reldata())
