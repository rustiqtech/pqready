//! Post-quantum implementations found by their constant tables.
//!
//! Solana has no PQ syscall or precompile, so a program verifying ML-DSA,
//! Falcon/FN-DSA or ML-KEM does it in its own code, and that code carries fixed,
//! public tables. The tables are derived here from their definitions:
//!
//! - ML-DSA (FIPS 204): zeta = 1753, q = 8380417, 256 entries, zeta^brv8(k);
//! - ML-KEM (FIPS 203): zeta = 17, q = 3329, 128 entries, zeta^brv7(k), and the
//!   second table of Appendix A, zeta^(2 brv7(k) + 1);
//! - Falcon / FN-DSA: g = 7, q = 12289, 1024 entries, g^brv10(k);
//! - Keccak-f[1600]: the 24 round constants (FIPS 202), present in any software
//!   SHA-3/SHAKE. ML-DSA and Falcon need SHAKE, which `sol_keccak256` does not
//!   provide; but Keccak-256 in software (e.g. Ethereum code) has them too, so
//!   they support a lattice hit and are not PQ evidence on their own.
//!
//! The derivations are checked in the tests against checksums of the tables in
//! maintained implementations: pq-code-package mldsa-native (`mld_zetas`) and
//! mlkem-native (`mlk_zetas`, Keccak round constants), and rust-fn-dsa (`GM`).
//!
//! Implementations store tables in different forms, so each NTT table is
//! searched in every combination of order (bit-reversed, natural, and for ML-KEM
//! the gamma table), domain (plain or Montgomery: 2^32 for ML-DSA and FN-DSA,
//! 2^16 for ML-KEM and the Falcon reference code), range ([0, q) or centred) and
//! entry width (2, 4 or 8 bytes, little-endian, where every value fits).
//!
//! A table matches when a window of `WINDOW` consecutive entries is found in
//! loaded data (32 bytes or more in every form). Three windows spread over the
//! table are tried and the number found is reported. `code_refs` counts the
//! reachable `lddw` values pointing into the matched table. As with the
//! precompile IDs, presence is not use.

use crate::precompile::DataRegion;
use memchr::memmem;
use std::collections::{BTreeMap, BTreeSet};

pub const WINDOW: usize = 8;

/// Base of the program region in SBPF V3, where code may refer to read-only data
/// by its run-time address.
const V3_BASE: u64 = 1 << 32;

fn brv(x: usize, bits: u32) -> usize {
    x.reverse_bits() >> (usize::BITS - bits)
}

fn pow_mod(mut b: u64, mut e: u64, q: u64) -> u64 {
    let mut r = 1 % q;
    b %= q;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % q;
        }
        b = b * b % q;
        e >>= 1;
    }
    r
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Order {
    BitRev,
    Natural,
    /// zeta^(2 brv(k) + 1), the second table of FIPS 203 Appendix A.
    Gamma,
}

impl Order {
    fn name(self) -> &'static str {
        match self {
            Order::BitRev => "bitrev",
            Order::Natural => "natural",
            Order::Gamma => "gamma",
        }
    }
}

fn ntt_table(q: u64, zeta: u64, n: usize, bits: u32, order: Order) -> Vec<u64> {
    (0..n)
        .map(|k| match order {
            Order::BitRev => pow_mod(zeta, brv(k, bits) as u64, q),
            Order::Natural => pow_mod(zeta, k as u64, q),
            Order::Gamma => pow_mod(zeta, 2 * brv(k, bits) as u64 + 1, q),
        })
        .collect()
}

/// FIPS 202, Algorithms 5 (rc) and 6: the round constants of Keccak-f[1600].
pub fn keccak_round_constants() -> [u64; 24] {
    fn rc(t: usize) -> u64 {
        if t % 255 == 0 {
            return 1;
        }
        let mut r: u32 = 1;
        for _ in 0..t % 255 {
            r <<= 1;
            if r & 0x100 != 0 {
                r ^= 0x171;
            }
        }
        u64::from(r & 1)
    }
    let mut out = [0u64; 24];
    for (ir, v) in out.iter_mut().enumerate() {
        for j in 0..7 {
            if rc(j + 7 * ir) == 1 {
                *v |= 1 << ((1 << j) - 1);
            }
        }
    }
    out
}

struct Scheme {
    name: &'static str,
    q: u64,
    zeta: u64,
    n: usize,
    bits: u32,
    radices: &'static [u32],
    orders: &'static [Order],
}

const SCHEMES: &[Scheme] = &[
    Scheme {
        name: "ml-dsa",
        q: 8_380_417,
        zeta: 1753,
        n: 256,
        bits: 8,
        radices: &[32],
        orders: &[Order::BitRev, Order::Natural],
    },
    Scheme {
        name: "ml-kem",
        q: 3329,
        zeta: 17,
        n: 128,
        bits: 7,
        radices: &[16],
        orders: &[Order::BitRev, Order::Natural, Order::Gamma],
    },
    Scheme {
        name: "falcon",
        q: 12289,
        zeta: 7,
        n: 1024,
        bits: 10,
        radices: &[16, 32],
        orders: &[Order::BitRev, Order::Natural],
    },
];

/// One storage form of one constant table (e.g. ML-DSA, bit-reversed,
/// Montgomery 2^32, centred, 4-byte entries), with windows of its packed bytes
/// to search for.
pub struct TableForm {
    pub scheme: &'static str,
    /// "order,domain,range,width", e.g. "bitrev,mont32,centred,4B".
    pub name: String,
    /// Bytes per entry.
    width: usize,
    /// Entries in the whole table.
    entries: usize,
    /// (index of the window's first entry, the window's packed bytes)
    windows: Vec<(usize, Vec<u8>)>,
}

fn pack(vals: &[i64], width: usize, signed: bool) -> Option<Vec<u8>> {
    let bits = 8 * width as u32;
    let fits = |v: i64| {
        if signed {
            let lim = 1i128 << (bits - 1);
            (-lim..lim).contains(&i128::from(v))
        } else {
            v >= 0 && (bits == 64 || (v as u64) < (1u64 << bits))
        }
    };
    vals.iter().all(|&v| fits(v)).then(|| {
        vals.iter()
            .flat_map(|&v| v.to_le_bytes()[..width].to_vec())
            .collect()
    })
}

fn windows_of(packed: &[u8], width: usize, n: usize) -> Vec<(usize, Vec<u8>)> {
    // Spread over the table, skipping entry 0 (often 0 or R).
    [1, n / 2, n - WINDOW]
        .iter()
        .map(|&i| (i, packed[i * width..(i + WINDOW) * width].to_vec()))
        .collect()
}

pub fn table_forms() -> Vec<TableForm> {
    let mut out = Vec::new();
    for s in SCHEMES {
        for &order in s.orders {
            let base = ntt_table(s.q, s.zeta, s.n, s.bits, order);
            let mut domains: Vec<(String, Vec<u64>)> = vec![("plain".into(), base.clone())];
            for &r in s.radices {
                domains.push((
                    format!("mont{r}"),
                    base.iter()
                        .map(|&x| ((u128::from(x) << r) % u128::from(s.q)) as u64)
                        .collect(),
                ));
            }
            for (dom, vals) in domains {
                let unsigned: Vec<i64> = vals.iter().map(|&v| v as i64).collect();
                let centred: Vec<i64> = vals
                    .iter()
                    .map(|&v| {
                        if v > s.q / 2 {
                            v as i64 - s.q as i64
                        } else {
                            v as i64
                        }
                    })
                    .collect();
                for (range, vs, signed) in
                    [("unsigned", &unsigned, false), ("centred", &centred, true)]
                {
                    for width in [2usize, 4, 8] {
                        if let Some(packed) = pack(vs, width, signed) {
                            out.push(TableForm {
                                scheme: s.name,
                                name: format!("{},{dom},{range},{width}B", order.name()),
                                width,
                                entries: s.n,
                                windows: windows_of(&packed, width, s.n),
                            });
                        }
                    }
                }
            }
        }
    }
    let rc: Vec<u8> = keccak_round_constants()
        .iter()
        .flat_map(|v| v.to_le_bytes())
        .collect();
    out.push(TableForm {
        scheme: "keccak-f1600",
        name: "round constants,8B".into(),
        width: 8,
        entries: 24,
        windows: [0usize, 8, 16]
            .iter()
            .map(|&i| (i, rc[i * 8..(i + WINDOW) * 8].to_vec()))
            .collect(),
    });
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableHit {
    pub scheme: &'static str,
    pub form: String,
    /// Address of the table's first entry.
    pub address: u64,
    pub windows_matched: usize,
    pub windows_tried: usize,
    /// Reachable `lddw` values pointing into the table.
    pub code_refs: usize,
}

/// Search loaded data (`(address, bytes)` per region) for every table form.
/// `lddw_values` are the values of reachable `lddw`s, for `code_refs`.
pub fn find_tables(
    regions: &[DataRegion<'_>],
    forms: &[TableForm],
    lddw_values: &[i64],
) -> Vec<TableHit> {
    let mut hits = Vec::new();
    for form in forms {
        // Table start address -> indexes of the windows found for it.
        let mut starts: BTreeMap<u64, BTreeSet<usize>> = BTreeMap::new();
        for &DataRegion { bytes, address } in regions {
            for (window_index, (first_entry, window)) in form.windows.iter().enumerate() {
                for pos in memmem::find_iter(bytes, window) {
                    let found_at = address + pos as u64;
                    if let Some(start) = found_at.checked_sub((*first_entry * form.width) as u64) {
                        starts.entry(start).or_default().insert(window_index);
                    }
                }
            }
        }
        for (start, windows_found) in starts {
            let end = start + (form.entries * form.width) as u64;
            let code_refs = lddw_values
                .iter()
                .filter(|&&v| {
                    let v = v as u64;
                    (start..end).contains(&v)
                        || v.checked_sub(V3_BASE)
                            .is_some_and(|t| (start..end).contains(&t))
                })
                .count();
            hits.push(TableHit {
                scheme: form.scheme,
                form: form.name.clone(),
                address: start,
                windows_matched: windows_found.len(),
                windows_tried: form.windows.len(),
                code_refs,
            });
        }
    }
    hits
}

/// Distinct Keccak round constants among `lddw` values: software Keccak with the
/// constants unrolled into code rather than stored as a table.
pub fn keccak_constants_inline(lddw_values: &[i64]) -> usize {
    let rc: BTreeSet<u64> = keccak_round_constants().into_iter().collect();
    lddw_values
        .iter()
        .map(|&v| v as u64)
        .filter(|v| rc.contains(v))
        .collect::<BTreeSet<_>>()
        .len()
}

/// Weak signals: moduli and related constants among instruction immediates
/// (32-bit) and `lddw` values (64-bit). Never a verdict on their own.
pub const WEAK_IMM32: &[(i64, &str)] = &[
    (8_380_417, "ml-dsa q"),
    (58_728_449, "ml-dsa qinv (2^32)"),
    (3329, "ml-kem q"),
    (62209, "ml-kem qinv (2^16)"),
    (12289, "falcon q"),
    (0x7800_0001, "babybear p"),
    (0x7F00_0001, "koalabear p"),
];
pub const WEAK_IMM64: &[(u64, &str)] = &[(0xFFFF_FFFF_0000_0001, "goldilocks p")];

pub fn weak_signals(
    imm32s: impl Iterator<Item = i32>,
    lddw_values: &[i64],
) -> BTreeMap<&'static str, usize> {
    let mut out = BTreeMap::new();
    for imm in imm32s {
        if let Some((_, name)) = WEAK_IMM32
            .iter()
            .find(|(v, _)| *v == i64::from(imm) || *v == i64::from(imm as u32))
        {
            *out.entry(*name).or_default() += 1;
        }
    }
    for &v in lddw_values {
        if let Some((_, name)) = WEAK_IMM64.iter().find(|(w, _)| *w == v as u64) {
            *out.entry(*name).or_default() += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    fn sha(vals: &[i64], width: usize, signed: bool) -> String {
        hex::encode(Sha256::digest(pack(vals, width, signed).unwrap()))
    }
    fn centre(v: &[u64], q: u64) -> Vec<i64> {
        v.iter()
            .map(|&x| {
                if x > q / 2 {
                    x as i64 - q as i64
                } else {
                    x as i64
                }
            })
            .collect()
    }
    fn mont(v: &[u64], r: u32, q: u64) -> Vec<u64> {
        v.iter()
            .map(|&x| ((u128::from(x) << r) % u128::from(q)) as u64)
            .collect()
    }

    // SHA-256 of each reference table, packed little-endian, computed from the
    // source arrays at: mldsa-native beb27b5 (mldsa/src/zetas.inc),
    // mlkem-native 08e1f38 (mlkem/src/zetas.inc, fips202/keccakf1600.c),
    // rust-fn-dsa 0629bb1 (fn-dsa-comm/src/mq.rs, GM).

    #[test]
    fn ml_dsa_matches_mldsa_native() {
        let q = 8_380_417;
        let mut t = centre(&mont(&ntt_table(q, 1753, 256, 8, Order::BitRev), 32, q), q);
        t[0] = 0; // unused entry, 0 in the reference
        assert_eq!(&t[..4], &[0, 25847, -2_608_894, -518_909]);
        assert_eq!(
            sha(&t, 4, true),
            "53f2a64af214b39b80717c930c811f14e55f7c3552be64306d1355d13be8e51a"
        );
    }

    #[test]
    fn ml_kem_matches_mlkem_native() {
        let q = 3329;
        let t = centre(&mont(&ntt_table(q, 17, 128, 7, Order::BitRev), 16, q), q);
        assert_eq!(&t[..4], &[-1044, -758, -359, -1517]);
        assert_eq!(
            sha(&t, 2, true),
            "054b2d8c8f004a6a8260985767c455f352ab543fd1d14ee6895f9a3d10503248"
        );
    }

    #[test]
    fn falcon_matches_fn_dsa_gm() {
        let q = 12289;
        // GM is in [1, q]; no entry is 0, so the [0, q) form is the same table.
        let t: Vec<i64> = mont(&ntt_table(q, 7, 1024, 10, Order::BitRev), 32, q)
            .iter()
            .map(|&x| x as i64)
            .collect();
        assert_eq!(&t[..4], &[10952, 11183, 10651, 1669]);
        assert_eq!(
            sha(&t, 2, false),
            "449f988551efbb32b3553a3a8bcc0f537815324bc7a3a1daec24b1cdc5251fc6"
        );
    }

    #[test]
    fn keccak_round_constants_match_mlkem_native() {
        let rc = keccak_round_constants();
        assert_eq!(
            &rc[..4],
            &[0x1, 0x8082, 0x8000_0000_0000_808a, 0x8000_0000_8000_8000]
        );
        // Reinterpreted as i64 (the bytes are the same); several have the top bit set.
        let t: Vec<i64> = rc.iter().map(|&v| v as i64).collect();
        assert_eq!(
            sha(&t, 8, true),
            "f8e6964adffc257265537256d21e93496a17b9271dc5d64f40869eeeaaff6fbb"
        );
    }

    #[test]
    fn every_storage_form_is_listed_once() {
        let all = table_forms();
        let forms: BTreeSet<(&str, &str)> =
            all.iter().map(|f| (f.scheme, f.name.as_str())).collect();
        assert_eq!(forms.len(), all.len(), "duplicate forms");
        for (scheme, form) in [
            ("ml-dsa", "bitrev,mont32,centred,4B"),
            ("ml-dsa", "bitrev,plain,unsigned,4B"),
            ("ml-kem", "bitrev,mont16,centred,2B"),
            ("ml-kem", "gamma,plain,unsigned,2B"),
            ("falcon", "bitrev,mont32,unsigned,2B"),
            ("falcon", "bitrev,mont16,unsigned,2B"),
        ] {
            assert!(forms.contains(&(scheme, form)), "{scheme} {form}");
        }
    }

    #[test]
    fn window_found_at_offset_gives_table_start() {
        let all = table_forms();
        let gamma = all
            .iter()
            .find(|f| f.scheme == "ml-kem" && f.name == "gamma,plain,unsigned,2B")
            .unwrap();
        let q = 3329;
        let t: Vec<i64> = ntt_table(q, 17, 128, 7, Order::Gamma)
            .iter()
            .map(|&x| x as i64)
            .collect();
        let mut data = vec![0xAAu8; 40];
        data.extend(pack(&t, 2, false).unwrap());
        let hits = find_tables(
            &[DataRegion {
                bytes: &data,
                address: 0x1000,
            }],
            &all,
            &[0x1000 + 40, 0x5000],
        );
        let h = hits.iter().find(|h| h.form == gamma.name).unwrap();
        assert_eq!(
            (h.address, h.windows_matched, h.code_refs),
            (0x1000 + 40, 3, 1)
        );
    }

    #[test]
    fn small_integers_match_nothing() {
        let data: Vec<u8> = (0u16..4096).flat_map(|i| i.to_le_bytes()).collect();
        assert!(
            find_tables(
                &[DataRegion {
                    bytes: &data,
                    address: 0,
                }],
                &table_forms(),
                &[]
            )
            .is_empty()
        );
    }
}
