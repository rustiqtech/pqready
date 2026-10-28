//! Locator of programs that verify signatures through precompiles

use std::collections::BTreeSet;

use memchr::memmem;

#[derive(Debug, Clone)]
pub struct Ref {
    pub id: &'static str,
    pub name: &'static str,
    /// true if referencing it implies a quantum-relevant dependency on its own.
    pub vulnerable: bool,
}

/// Precompiles can't be called through CPI. A program depends on one by inspecting the
/// transaction's other instructions through the Instructions sysvar and comparing their program ID
/// with the precompile's. The ZK ElGamal proof program can be called through CPI, so for it a
/// copied ID (an instruction being built) is also evidence.
pub static REFS: &[Ref] = &[
    Ref {
        id: "Ed25519SigVerify111111111111111111111111111",
        name: "ed25519_precompile",
        vulnerable: true,
    },
    Ref {
        id: "KeccakSecp256k11111111111111111111111111111",
        name: "secp256k1_precompile",
        vulnerable: true,
    },
    Ref {
        id: "Secp256r1SigVerify1111111111111111111111111",
        name: "secp256r1_precompile",
        vulnerable: true,
    },
    Ref {
        id: "ZkE1Gama1Proof11111111111111111111111111111",
        name: "zk_elgamal_proof_program",
        vulnerable: true,
    },
    Ref {
        id: "Sysvar1nstructions1111111111111111111111111",
        name: "instructions_sysvar",
        vulnerable: false,
    },
];

#[derive(Debug, Clone)]
pub struct RefBytes {
    pub r: &'static Ref,
    pub bytes: [u8; 32],
}

pub fn decoded_refs() -> Vec<RefBytes> {
    REFS.iter()
        .map(|r| {
            let v = bs58::decode(r.id)
                .into_vec()
                .expect("valid base58 program id");
            let bytes: [u8; 32] = v.try_into().expect("program id is 32 bytes");
            RefBytes { r, bytes }
        })
        .collect()
}

/// Returns (ref, occurrence count) for every reference found in `elf`.
pub fn find_refs<'a>(elf: &[u8], ref_bytes: &'a [RefBytes]) -> Vec<(&'a Ref, usize)> {
    ref_bytes
        .iter()
        .filter_map(|n| {
            let count = memmem::find_iter(elf, &n.bytes).count();
            (count > 0).then_some((n.r, count))
        })
        .collect()
}

#[derive(Debug, Clone)]
pub struct LocatedId {
    pub r: &'static Ref,
    pub addresses: BTreeSet<u64>,
    pub chunks: [i64; 4],
    pub in_file: bool,
}

pub struct DataRegion<'a> {
    pub bytes: &'a [u8],
    pub address: u64,
}

pub fn locate_ids(
    regions: &[DataRegion<'_>],
    elf_bytes: &[u8],
    rbs: &[RefBytes],
) -> Vec<LocatedId> {
    rbs.iter()
        .map(|rb| {
            let addresses: BTreeSet<u64> = regions
                .iter()
                .flat_map(|reg| {
                    memmem::find_iter(reg.bytes, &rb.bytes)
                        .flat_map(move |pos| reg.address.checked_add(pos as u64))
                })
                .collect();
            let (words, _) = rb.bytes.as_chunks::<8>();
            let chunks: [i64; 4] = std::array::from_fn(|i| i64::from_le_bytes(words[i]));
            let in_file = memmem::find(elf_bytes, &rb.bytes).is_some();
            LocatedId {
                r: rb.r,
                addresses,
                chunks,
                in_file,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ED25519: usize = 0;
    const SYSVAR: usize = 4;

    #[test]
    fn ids_decode_to_32_bytes() {
        assert_eq!(decoded_refs().len(), REFS.len());
    }

    #[test]
    fn finds_embedded_id() {
        let ns = decoded_refs();
        let mut blob = vec![0xAAu8; 100];
        blob.extend_from_slice(&ns[2].bytes);
        blob.extend_from_slice(&[0u8; 7]);
        let hits = find_refs(&blob, &ns);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].0.name, "secp256r1_precompile");
    }

    /// A file of `len` filler bytes with the given IDs written at the given offsets.
    fn file_with(len: usize, ids: &[(usize, &RefBytes)]) -> Vec<u8> {
        let mut f = vec![0xAA; len];
        for (off, rb) in ids {
            f[*off..*off + 32].copy_from_slice(&rb.bytes);
        }
        f
    }

    fn addrs(l: &LocatedId) -> Vec<u64> {
        l.addresses.iter().copied().collect()
    }

    #[test]
    fn empty_input_gives_every_id_not_found() {
        let refs = decoded_refs();
        let out = locate_ids(&[], &[], &refs);
        assert_eq!(out.len(), REFS.len());
        for (l, r) in out.iter().zip(REFS) {
            assert_eq!(l.r.name, r.name, "output keeps REFS order");
            assert!(l.addresses.is_empty());
            assert!(!l.in_file);
        }
    }

    #[test]
    fn one_match_in_one_region() {
        let refs = decoded_refs();
        let f = file_with(400, &[(100, &refs[ED25519])]);
        let regions = [DataRegion {
            bytes: &f[..],
            address: 0x3000,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert_eq!(addrs(&out[ED25519]), vec![0x3000 + 100]);
        assert!(out[ED25519].in_file);
        for (i, l) in out.iter().enumerate().filter(|(i, _)| *i != ED25519) {
            assert!(l.addresses.is_empty() && !l.in_file, "id {i} not present");
        }
    }

    #[test]
    fn match_position_is_relative_to_the_region_not_the_file() {
        let refs = decoded_refs();
        let f = file_with(400, &[(250, &refs[ED25519])]);
        // Region covers file bytes 200..400 and is loaded at 0x3000.
        let regions = [DataRegion {
            bytes: &f[200..],
            address: 0x3000,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert_eq!(addrs(&out[ED25519]), vec![0x3000 + 50]);
    }

    #[test]
    fn two_copies_in_one_region() {
        let refs = decoded_refs();
        let f = file_with(400, &[(0, &refs[ED25519]), (200, &refs[ED25519])]);
        let regions = [DataRegion {
            bytes: &f[..],
            address: 0x1000,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert_eq!(addrs(&out[ED25519]), vec![0x1000, 0x1000 + 200]);
    }

    #[test]
    fn two_regions_use_their_own_addresses() {
        let refs = decoded_refs();
        let f = file_with(400, &[(10, &refs[ED25519]), (210, &refs[ED25519])]);
        let regions = [
            DataRegion {
                bytes: &f[..200],
                address: 0x1000,
            },
            DataRegion {
                bytes: &f[200..],
                address: 0x9000,
            },
        ];
        let out = locate_ids(&regions, &f, &refs);
        assert_eq!(addrs(&out[ED25519]), vec![0x1000 + 10, 0x9000 + 10]);
    }

    #[test]
    fn in_file_but_outside_every_region() {
        let refs = decoded_refs();
        // ID at 300; the only region is 0..200 (e.g. the ID sits in code).
        let f = file_with(400, &[(300, &refs[SYSVAR])]);
        let regions = [DataRegion {
            bytes: &f[..200],
            address: 0x1000,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert!(out[SYSVAR].addresses.is_empty());
        assert!(out[SYSVAR].in_file);
    }

    #[test]
    fn id_crossing_a_region_boundary_is_not_an_address() {
        let refs = decoded_refs();
        // ID at 190..222 straddles the boundary at 200 between two adjacent regions.
        let f = file_with(400, &[(190, &refs[ED25519])]);
        let regions = [
            DataRegion {
                bytes: &f[..200],
                address: 0x1000,
            },
            DataRegion {
                bytes: &f[200..],
                address: 0x1000 + 200,
            },
        ];
        let out = locate_ids(&regions, &f, &refs);
        assert!(out[ED25519].addresses.is_empty());
        assert!(out[ED25519].in_file);
    }

    #[test]
    fn synthetic_section_address() {
        let refs = decoded_refs();
        let f = file_with(0x200, &[(0x120, &refs[ED25519])]);
        let regions = [DataRegion {
            bytes: &f[..],
            address: 4u64 << 32,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert_eq!(addrs(&out[ED25519]), vec![0x4_0000_0120]);
    }

    #[test]
    fn address_overflow_is_skipped_not_wrapped() {
        let refs = decoded_refs();
        let f = file_with(64, &[(16, &refs[ED25519])]);
        let regions = [DataRegion {
            bytes: &f[..],
            address: u64::MAX - 8,
        }];
        let out = locate_ids(&regions, &f, &refs);
        assert!(out[ED25519].addresses.is_empty());
        assert!(out[ED25519].in_file);
    }

    #[test]
    fn chunks_are_little_endian_words_of_the_id() {
        let refs = decoded_refs();
        let out = locate_ids(&[], &[], &refs);
        for (l, rb) in out.iter().zip(&refs) {
            for k in 0..4 {
                let word: [u8; 8] = rb.bytes[8 * k..8 * k + 8].try_into().unwrap();
                assert_eq!(
                    l.chunks[k],
                    i64::from_le_bytes(word),
                    "{} chunk {k}",
                    l.r.name
                );
            }
        }
    }

    #[test]
    fn chunks_are_usable_fingerprints() {
        // One-time check on the real IDs: no chunk is 0 and all 20 are distinct.
        let refs = decoded_refs();
        let out = locate_ids(&[], &[], &refs);
        let all: Vec<i64> = out.iter().flat_map(|l| l.chunks).collect();
        assert!(all.iter().all(|&c| c != 0), "zero chunk: {out:?}");
        assert_eq!(
            all.iter().collect::<BTreeSet<_>>().len(),
            all.len(),
            "duplicate chunk: {out:?}"
        );
    }
}
