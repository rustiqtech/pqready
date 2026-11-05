//! Locator of programs that verify signatures through precompiles

use crate::{
    constprop::{ConstSet, FnSnapshots, Val},
    sbpf::Call,
};
use memchr::memmem;
use std::collections::{BTreeMap, BTreeSet, HashMap};

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

/// Entry instruction indexes of the functions in this code region that forward their arguments to
/// `sol_memcmp_`.
pub fn forwarding_wrappers(
    snapshots: &BTreeMap<usize, FnSnapshots>,
    calls: &HashMap<usize, Call>,
) -> BTreeSet<usize> {
    let mut entries: BTreeSet<usize> = BTreeSet::new();
    loop {
        let found: Vec<usize> = snapshots
            .iter()
            .filter(|(e, fs)| !entries.contains(*e) && forwards_to_memcmp(fs, calls, &entries))
            .map(|(e, _)| *e)
            .collect();
        if found.is_empty() {
            return entries;
        }
        entries.extend(found);
    }
}

/// Whether some call in `fs` reaches `sol_memcmp_`, directly or through one of `wrappers`, with
/// this function's own r1, r2 (in either order) and r3.
fn forwards_to_memcmp(
    fs: &FnSnapshots,
    calls: &HashMap<usize, Call>,
    wrappers: &BTreeSet<usize>,
) -> bool {
    fs.raw_calls.iter().any(|(site, regs)| {
        let is_memcmp = match calls.get(site) {
            Some(Call::Syscall { name, .. }) => name == "sol_memcmp_",
            Some(Call::Internal(i)) => wrappers.contains(i),
            _ => false,
        };
        is_memcmp
            && regs[2] == Val::Entry(3)
            && ((regs[0] == Val::Entry(1) && regs[1] == Val::Entry(2))
                || (regs[0] == Val::Entry(2) && regs[1] == Val::Entry(1)))
    })
}

/// The rule an ID ended up with, in priority order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rule {
    KeyList,
    IdCompared,
    IdPassed,
    Referenced,
    BytesUnreferenced,
}

impl Rule {
    /// The `evidence` string in dependencies.csv.
    pub fn as_str(self) -> &'static str {
        match self {
            Rule::KeyList => "key_list",
            Rule::IdCompared => "id_compared",
            Rule::IdPassed => "id_passed",
            Rule::Referenced => "referenced",
            Rule::BytesUnreferenced => "bytes_unreferenced",
        }
    }
}

/// What one code region's reachable functions do with one ID. Counts are sites; merged across
/// regions by adding.
#[derive(Debug, Clone, Default)]
pub struct IdFacts {
    /// Calls to sol_memcmp_ or a forwarding wrapper where r1 or r2 is one of the ID's data
    /// addresses and r3 is exactly 32.
    pub compared_sites: usize,
    /// Functions in which all four inline chunks of the ID are operands of conditional jumps or
    /// xors.
    pub chunk_compared_functions: usize,
    /// Calls to any other internal function with one of the ID's data addresses in an argument
    /// register and 32 in another.
    pub passed_sites: usize,
    /// Reachable instructions that load, pass or store one of the ID's data addresses, whether or
    /// not a rule above applies.
    pub referencing_instructions: usize,
    /// Some reachable instruction refers to an address within the ID's own 32 bytes (lddw values,
    /// load addresses, call or store arguments).
    pub points_into_own_entry: bool,
    /// Some inline chunk of the ID appears as a jump operand, xor operand or lddw value.
    pub chunks_seen: bool,
    /// Call sites where a needed argument is not constant on every path.
    pub unknown_argument_sites: usize,
}

impl IdFacts {
    pub fn merge(&mut self, other: &IdFacts) {
        self.compared_sites += other.compared_sites;
        self.chunk_compared_functions += other.chunk_compared_functions;
        self.passed_sites += other.passed_sites;
        self.referencing_instructions += other.referencing_instructions;
        self.points_into_own_entry |= other.points_into_own_entry;
        self.chunks_seen |= other.chunks_seen;
        self.unknown_argument_sites += other.unknown_argument_sites;
    }
}

/// Facts for `id` in one code region. Called in scan_elf's region loop, after `analyze_range` and
/// `forwarding_wrappers`.
pub fn region_facts(
    id: &LocatedId,
    snapshots: &BTreeMap<usize, FnSnapshots>,
    calls: &HashMap<usize, Call>,
    wrappers: &BTreeSet<usize>,
) -> IdFacts {
    let mut facts: IdFacts = Default::default();
    let addresses: ConstSet = id.addresses.iter().map(|&a| a as i64).collect();
    let holds_address =
        |r: &Option<ConstSet>| r.as_ref().is_some_and(|s| !s.is_disjoint(&addresses));
    let chunk_set: ConstSet = id.chunks.into();
    for (e, fs) in snapshots {
        let operands: BTreeSet<&[Option<ConstSet>; 2]> =
            fs.jumps.values().chain(fs.xors.values()).collect();
        let seen_chunks: BTreeSet<i64> = operands
            .iter()
            .filter_map(|[a, b]| match (a, b) {
                (Some(c), None) | (None, Some(c)) => Some(c),
                _ => None,
            })
            .flat_map(|c| c.intersection(&chunk_set).copied())
            .collect();
        let fact = IdFacts {
            compared_sites: fs
                .calls
                .iter()
                .filter(|(site, regs)| match calls.get(site) {
                    Some(Call::Syscall { name, .. }) => name == "sol_memcmp_",
                    Some(Call::Internal(i)) => wrappers.contains(i),
                    _ => false,
                } && ([0, 1].into_iter().any(|r| holds_address(&regs[r])))
                        && regs[2].as_ref() == Some(&ConstSet::from([32]))
                )
                .count(),
            chunk_compared_functions: usize::from(chunk_set.is_subset(&seen_chunks)),
            ..Default::default()
        };

        facts.merge(&fact);
    }
    facts
}

/// Length of the longest run of consecutive 32-byte entries from `builtin` (keys::builtin()) that
/// contains one of the ID's addresses. Data only, no code.
pub fn key_list_run(
    id: &LocatedId,
    regions: &[DataRegion<'_>],
    builtin: &HashMap<[u8; 32], &'static str>,
) -> usize {
    todo!()
}

/// Rule order. No ELF needed, so it's tested on hand-made facts.
pub fn rule_for(facts: &IdFacts, key_list_run: usize) -> Rule {
    todo!()
}

/// One row per located ID, for ElfReport.
#[derive(Debug, Clone)]
pub struct IdVerdict {
    pub name: &'static str, // from RefBytes.r
    pub vulnerable: bool,
    pub rule: Rule,
    pub sites: usize, // the sites behind `rule`
    pub unknown_argument_sites: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constprop::ConstSet;
    use Val::{Entry, Unknown};

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

    const FORWARDS: [Val; 3] = [Entry(1), Entry(2), Entry(3)];

    fn memcmp() -> Call {
        Call::Syscall {
            name: "sol_memcmp_".into(),
            via_reloc: true,
        }
    }
    fn consts(v: i64) -> Val {
        Val::Consts(ConstSet::from([v]))
    }

    /// A function: its entry and, per call site, (site, callee, r1..r3).
    type Function<'a> = (usize, &'a [(usize, Call, [Val; 3])]);

    fn region(fns: &[Function]) -> (BTreeMap<usize, FnSnapshots>, HashMap<usize, Call>) {
        let mut snapshots = BTreeMap::new();
        let mut calls = HashMap::new();
        for (entry, sites) in fns {
            let mut f = FnSnapshots::default();
            for (site, callee, regs) in sites.iter().cloned() {
                f.raw_calls.insert(site, regs);
                calls.insert(site, callee);
            }
            snapshots.insert(*entry, f);
        }
        (snapshots, calls)
    }

    fn wrappers(fns: &[Function]) -> BTreeSet<usize> {
        let (s, c) = region(fns);
        forwarding_wrappers(&s, &c)
    }

    #[test]
    fn direct_forwarding_to_the_syscall() {
        assert_eq!(wrappers(&[(10, &[(14, memcmp(), FORWARDS)])]), [10].into());
    }

    #[test]
    fn r1_and_r2_may_be_swapped() {
        assert_eq!(
            wrappers(&[(10, &[(14, memcmp(), [Entry(2), Entry(1), Entry(3)])])]),
            [10].into()
        );
    }

    #[test]
    fn wrapper_of_a_wrapper_at_a_lower_index() {
        // 0 calls 10 calls 20 calls sol_memcmp_: the map is visited 0, 10, 20,
        // so each outer wrapper is checked before the one it calls is known.
        let found = wrappers(&[
            (0, &[(3, Call::Internal(10), FORWARDS)]),
            (
                10,
                &[(13, Call::Internal(20), [Entry(2), Entry(1), Entry(3)])],
            ),
            (20, &[(24, memcmp(), FORWARDS)]),
        ]);
        assert_eq!(found, [0, 10, 20].into());
    }

    #[test]
    fn caller_passing_constants_is_not_a_wrapper() {
        // 0 is the rules' typical caller: memcmp(key, &ID, 32) through wrapper 10.
        let found = wrappers(&[
            (
                0,
                &[(
                    3,
                    Call::Internal(10),
                    [Entry(1), consts(0x1000), consts(32)],
                )],
            ),
            (10, &[(14, memcmp(), FORWARDS)]),
        ]);
        assert_eq!(found, [10].into());
    }

    #[test]
    fn changed_or_missing_arguments_do_not_forward() {
        for regs in [
            [Entry(1), Unknown, Entry(3)], // r2 changed (rule_wrapper_rearranged)
            [Entry(1), Entry(2), consts(32)], // fixed length
            [Entry(1), Entry(1), Entry(3)], // same pointer twice
            [Entry(3), Entry(2), Entry(1)], // length moved
        ] {
            assert!(
                wrappers(&[(10, &[(14, memcmp(), regs.clone())])]).is_empty(),
                "{regs:?}"
            );
        }
    }

    #[test]
    fn other_callees_do_not_count() {
        let memcpy = Call::Syscall {
            name: "sol_memcpy_".into(),
            via_reloc: true,
        };
        assert!(wrappers(&[(10, &[(14, memcpy, FORWARDS)])]).is_empty());
        // Forwarding to a function that is not a wrapper (it only logs).
        let found = wrappers(&[
            (0, &[(3, Call::Internal(10), FORWARDS)]),
            (
                10,
                &[(
                    14,
                    Call::Syscall {
                        name: "sol_log_".into(),
                        via_reloc: true,
                    },
                    FORWARDS,
                )],
            ),
        ]);
        assert!(found.is_empty());
        for c in [Call::Indirect, Call::Unknown, Call::Unresolved(0x1234)] {
            assert!(wrappers(&[(10, &[(14, c, FORWARDS)])]).is_empty());
        }
    }

    #[test]
    fn one_forwarding_site_is_enough() {
        // A memcmp with a short inline path and a forwarding call, like the
        // toolchain's memcmp (Zynko..., instruction 78726).
        let found = wrappers(&[(
            10,
            &[
                (12, memcmp(), [Entry(1), Unknown, Entry(3)]),
                (18, memcmp(), FORWARDS),
            ],
        )]);
        assert_eq!(found, [10].into());
    }

    #[test]
    fn call_site_missing_from_calls_is_ignored() {
        let (s, mut c) = region(&[(10, &[(14, memcmp(), FORWARDS)])]);
        c.clear();
        assert!(forwarding_wrappers(&s, &c).is_empty());
    }

    #[test]
    fn recursion_terminates() {
        // 10 forwards to itself only: never a wrapper, and the loop ends.
        assert!(wrappers(&[(10, &[(14, Call::Internal(10), FORWARDS)])]).is_empty());
    }
}
