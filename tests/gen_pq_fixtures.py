#!/usr/bin/env python3
"""Generate the synthetic programs in tests/fixtures/pq/*.so.

usage: gen_pq_fixtures.py OUT_DIR

Each is a minimal linked SBPF ELF without section headers: one executable
PT_LOAD with the code at the V3 code address 0x1_0000_0000, and one read-only
PT_LOAD with the data at 0x1000. The code is a sequence of `lddw r1, VALUE`
followed by `exit`, so a table is "referenced by code" exactly when one of the
values points into it.

  mldsa_plain_natural_u32.so  32 filler bytes, then the ML-DSA table in plain
                              values, natural order (1753^k mod q), 4-byte
                              entries, as a const fn might compute it. Loaded
                              by code (lddw 0x1020). Expected: one hit, 1 ref.
  mlkem_mont_u64.so           the ML-KEM table, bit-reversed, Montgomery 2^16,
                              8-byte entries. Not loaded. Expected: one hit, 0 refs.
  mlkem_gamma_plain_u16.so    the second ML-KEM table of FIPS 203 Appendix A,
                              17^(2 brv7(k) + 1) mod q, plain, 2-byte entries,
                              as RustCrypto ml-kem stores GAMMA. Loaded by code.
                              Expected: one hit, 1 ref.
  decoy_small_ints.so         0..4095 as u16 then 0..2047 as u32. Expected: no hit.
"""
import struct
import sys
from pathlib import Path

CODE_VA = 0x1_0000_0000
DATA_VA = 0x1000


def brv(x, bits):
    return int(f"{x:0{bits}b}"[::-1], 2)


def ntt_table(q, zeta, n, bits, order):
    if order == "bitrev":
        return [pow(zeta, brv(k, bits), q) for k in range(n)]
    if order == "gamma":
        return [pow(zeta, 2 * brv(k, bits) + 1, q) for k in range(n)]
    return [pow(zeta, k, q) for k in range(n)]


def lddw(dst, v):
    return struct.pack("<BBhI", 0x18, dst, 0, v & 0xFFFFFFFF) + struct.pack("<BBhI", 0, 0, 0, v >> 32)


def program(data, loads, size):
    """An ELF of `size` bytes: header, two program headers, data at file offset
    0x1000, code right after the data plus 0x100."""
    code = b"".join(lddw(1, v) for v in loads) + struct.pack("<BBhi", 0x95, 0, 0, 0)
    f = bytearray(size)
    data_off = 0x1000
    code_off = data_off + len(data) + 0x100
    f[0:4] = b"\x7fELF"
    f[4], f[5], f[6] = 2, 1, 1          # 64-bit, little-endian, version 1
    struct.pack_into("<HHIQQQIHHHHHH", f, 16, 3, 247, 1, CODE_VA, 0x40, 0, 3, 64, 0x38, 2, 64, 0, 0)
    struct.pack_into("<IIQQQQQQ", f, 0x40, 1, 5, code_off, CODE_VA, CODE_VA, len(code), len(code), 8)
    struct.pack_into("<IIQQQQQQ", f, 0x78, 1, 4, data_off, DATA_VA, DATA_VA, len(data), len(data), 8)
    f[data_off:data_off + len(data)] = data
    f[code_off:code_off + len(code)] = code
    return bytes(f)


def main():
    d = Path(sys.argv[1])
    d.mkdir(parents=True, exist_ok=True)

    t = ntt_table(8380417, 1753, 256, 8, "natural")
    data = b"\0" * 32 + b"".join(v.to_bytes(4, "little") for v in t)
    (d / "mldsa_plain_natural_u32.so").write_bytes(program(data, [DATA_VA + 32], 0x1000 + len(data) + 0x3000))

    q = 3329
    t = [(x << 16) % q for x in ntt_table(q, 17, 128, 7, "bitrev")]
    data = b"".join(v.to_bytes(8, "little") for v in t)
    (d / "mlkem_mont_u64.so").write_bytes(program(data, [], 0x1000 + len(data) + 0x3000))

    t = ntt_table(q, 17, 128, 7, "gamma")
    data = b"".join(v.to_bytes(2, "little") for v in t)
    (d / "mlkem_gamma_plain_u16.so").write_bytes(program(data, [DATA_VA], 0x3000))

    data = b"".join(i.to_bytes(2, "little") for i in range(4096)) + b"".join(i.to_bytes(4, "little") for i in range(2048))
    (d / "decoy_small_ints.so").write_bytes(program(data, [DATA_VA], 0x1000 + len(data) + 0x3000))


if __name__ == "__main__":
    main()
