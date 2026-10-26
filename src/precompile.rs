//! Heuristic: programs that verify signatures through the precompiles embed the precompile's
//! program ID (and usually the instructions sysvar ID) in their read-only data, because they
//! inspect the transaction's other instructions. A byte match is evidence, not proof.

use memchr::memmem;

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

#[cfg(test)]
mod tests {
    use super::*;

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
}
