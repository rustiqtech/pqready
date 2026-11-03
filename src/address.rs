//! Solana address derivation: program-derived addresses and addresses with a
//! seed, as in the `solana-address` crate (`create_program_address`,
//! `find_program_address`, `create_with_seed`). Used to locate a program's IDL
//! accounts.

use curve25519_dalek::edwards::CompressedEdwardsY;
use sha2::{Digest, Sha256};

pub type Address = [u8; 32];

const PDA_MARKER: &[u8] = b"ProgramDerivedAddress";
const MAX_SEED_LEN: usize = 32;
const MAX_SEEDS: usize = 16;

/// Whether 32 bytes decode to a point on the Ed25519 curve. A program-derived
/// address must not, so that no private key can exist for it.
fn is_on_curve(a: &Address) -> bool {
    CompressedEdwardsY(*a).decompress().is_some()
}

/// sha256(seeds || program_id || "ProgramDerivedAddress"), or None if a seed is
/// too long, there are too many seeds, or the result lies on the curve.
pub fn create_program_address(seeds: &[&[u8]], program_id: &Address) -> Option<Address> {
    if seeds.len() > MAX_SEEDS || seeds.iter().any(|s| s.len() > MAX_SEED_LEN) {
        return None;
    }
    let mut h = Sha256::new();
    for s in seeds {
        h.update(s);
    }
    h.update(program_id);
    h.update(PDA_MARKER);
    let a: Address = h.finalize().into();
    (!is_on_curve(&a)).then_some(a)
}

/// The first valid program-derived address with a bump seed from 255 down,
/// and that bump.
pub fn find_program_address(seeds: &[&[u8]], program_id: &Address) -> Option<(Address, u8)> {
    (0..=255u8).rev().find_map(|bump| {
        let b = [bump];
        let mut with_bump: Vec<&[u8]> = seeds.to_vec();
        with_bump.push(&b);
        create_program_address(&with_bump, program_id).map(|a| (a, bump))
    })
}

/// sha256(base || seed || owner), or None if the seed is too long or the owner
/// ends with the PDA marker.
pub fn create_with_seed(base: &Address, seed: &str, owner: &Address) -> Option<Address> {
    if seed.len() > MAX_SEED_LEN || owner.ends_with(PDA_MARKER) {
        return None;
    }
    let mut h = Sha256::new();
    h.update(base);
    h.update(seed.as_bytes());
    h.update(owner);
    Some(h.finalize().into())
}

pub fn from_base58(s: &str) -> Option<Address> {
    bs58::decode(s).into_vec().ok()?.try_into().ok()
}

pub fn to_base58(a: &Address) -> String {
    bs58::encode(a).into_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(s: &str) -> Address {
        from_base58(s).unwrap()
    }

    // Vectors from the solana-address 2.9.0 test suite (test_create_with_seed,
    // test_create_program_address).
    #[test]
    fn create_with_seed_matches_solana_address() {
        assert_eq!(
            create_with_seed(&[0; 32], "limber chicken: 4/45", &[0; 32])
                .map(|x| to_base58(&x))
                .as_deref(),
            Some("9h1HyLCW5dZnBVap8C5egQ9Z6pHyjsh5MNy83iPqqRuq")
        );
    }

    #[test]
    fn create_program_address_matches_solana_address() {
        let program = a("BPFLoaderUpgradeab1e11111111111111111111111");
        assert_eq!(
            create_program_address(&[b"", &[1]], &program)
                .map(|x| to_base58(&x))
                .as_deref(),
            Some("BwqrghZA2htAcqq8dzP1WDAhTXYTYWj7CHxF5j7TDBAe")
        );
        assert_eq!(
            create_program_address(&["☉".as_bytes(), &[0]], &program)
                .map(|x| to_base58(&x))
                .as_deref(),
            Some("13yWmRpaTR4r5nAktwLqMpRNr28tnVUZw26rTvPSSB19")
        );
        assert_eq!(create_program_address(&[&[0u8; 33]], &program), None);
    }

    // Reference values computed with solana-address 2.9.0 itself
    // (find_program_address, create_with_seed) for these programs; they cover
    // bumps from 255 down to 247.
    #[test]
    fn idl_addresses_match_solana_address() {
        let pmp = a("ProgM6JCCvbYkfKqJYHePx4xxSUSqJp7rh8Lyv7nk7S");
        let mut seed = [0u8; 16];
        seed[..3].copy_from_slice(b"idl");
        for (program, signer, bump, idl, meta, meta_bump) in [
            (
                "JUP6LkbZbjS1jKKwapdHNy74zcZ3tLUZoi5QNyVTaV4",
                "GPJkEFWhjnpQADAtoiSQ2upCDSPp7qCNeYtiy8ty2KcF",
                254,
                "C88XWfp26heEmDkmfSzeXP7Fd7GQJ2j9dDTUsyiZbUTa",
                "FDDfotwLyeLhUQ62ugzgTjwTvF3r64tPRVsKwsqRrbbC",
                251,
            ),
            (
                "whirLbMiicVdio4qvUfM5KAg6Ct8VwpYzGff3uctyCc",
                "HqXLYaUXkfdGhWMuciBEN9MouqLu5wJYWdepP5TspmXj",
                255,
                "2KFqE4RWoPVbvodo8vbggCFeHPS8TDvgpwp79ALMrcyn",
                "9fQgUeE2BpGXLHopvZhDKTskXV2druezgX6hpmscbya5",
                247,
            ),
            (
                "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb",
                "Fe8aMBYn6JbsZUByp3xH59ZynqKN8dp2uB9jdWbp5HVh",
                252,
                "AiJmxqFSfSmPTXK9DDLcmnYnrEBZiXcUPbPA2ema6cXU",
                "8GHhnGA5PDsgJY7SgXmDXnRSbvteSQq4jDixpPGWR3qH",
                253,
            ),
        ] {
            let id = a(program);
            let (s, b) = find_program_address(&[], &id).unwrap();
            assert_eq!((to_base58(&s).as_str(), b), (signer, bump), "{program}");
            assert_eq!(
                to_base58(&create_with_seed(&s, "anchor:idl", &id).unwrap()),
                idl,
                "{program}"
            );
            let (m, mb) = find_program_address(&[&id, &[], &seed], &pmp).unwrap();
            assert_eq!((to_base58(&m).as_str(), mb), (meta, meta_bump), "{program}");
        }
    }
}
