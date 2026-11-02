//! Addresses of Solana's built-in programs and sysvars, and a few ubiquitous
//! program addresses, for labelling 32-byte entries in program data.
//!
//! Lists of these addresses are linked into many programs, typically to check
//! whether an account is a built-in (the SDK's reserved-account-keys list).
//! An ID found inside such a list is a list entry, not a dependency on it.

use std::collections::HashMap;

/// (base58 address, label). Built-in programs and sysvars first; then programs
/// that are common but not built in, which do not count towards a built-in list.
pub const BUILTIN_KEYS: &[(&str, &str)] = &[
    ("11111111111111111111111111111111", "System program"),
    ("Vote111111111111111111111111111111111111111", "Vote program"),
    ("Stake11111111111111111111111111111111111111", "Stake program"),
    ("StakeConfig11111111111111111111111111111111", "Stake config program"),
    ("Config1111111111111111111111111111111111111", "Config program"),
    ("BPFLoader1111111111111111111111111111111111", "BPF loader v1"),
    ("BPFLoader2111111111111111111111111111111111", "BPF loader v2"),
    ("BPFLoaderUpgradeab1e11111111111111111111111", "BPF upgradeable loader"),
    ("LoaderV411111111111111111111111111111111111", "Loader v4"),
    ("NativeLoader1111111111111111111111111111111", "Native loader"),
    ("ComputeBudget111111111111111111111111111111", "Compute budget program"),
    ("AddressLookupTab1e1111111111111111111111111", "Address lookup table program"),
    ("Feature111111111111111111111111111111111111", "Feature program"),
    ("ZkTokenProof1111111111111111111111111111111", "ZK token proof program"),
    ("Ed25519SigVerify111111111111111111111111111", "Ed25519 precompile"),
    ("KeccakSecp256k11111111111111111111111111111", "secp256k1 precompile"),
    ("Secp256r1SigVerify1111111111111111111111111", "secp256r1 precompile"),
    ("ZkE1Gama1Proof11111111111111111111111111111", "ZK ElGamal proof program"),
    ("Sysvar1111111111111111111111111111111111111", "Sysvar owner"),
    ("SysvarC1ock11111111111111111111111111111111", "Clock sysvar"),
    ("SysvarEpochRewards1111111111111111111111111", "Epoch rewards sysvar"),
    ("SysvarEpochSchedu1e111111111111111111111111", "Epoch schedule sysvar"),
    ("SysvarFees111111111111111111111111111111111", "Fees sysvar"),
    ("Sysvar1nstructions1111111111111111111111111", "Instructions sysvar"),
    ("SysvarLastRestartS1ot1111111111111111111111", "Last restart slot sysvar"),
    ("SysvarRecentB1ockHashes11111111111111111111", "Recent blockhashes sysvar"),
    ("SysvarRent111111111111111111111111111111111", "Rent sysvar"),
    ("SysvarRewards111111111111111111111111111111", "Rewards sysvar"),
    ("SysvarS1otHashes111111111111111111111111111", "Slot hashes sysvar"),
    ("SysvarS1otHistory11111111111111111111111111", "Slot history sysvar"),
    ("SysvarStakeHistory1111111111111111111111111", "Stake history sysvar"),
];

/// Common programs that are not built in: labelled, but not counted as part of
/// a built-in list.
pub const OTHER_KEYS: &[(&str, &str)] = &[
    ("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA", "SPL Token"),
    ("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb", "SPL Token-2022"),
    ("ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL", "Associated token account program"),
    ("So11111111111111111111111111111111111111112", "Wrapped SOL mint"),
];

fn decode(list: &'static [(&'static str, &'static str)]) -> HashMap<[u8; 32], &'static str> {
    list.iter()
        .map(|(b58, label)| {
            let v = bs58::decode(b58).into_vec().expect("valid base58");
            (v.try_into().expect("32-byte address"), *label)
        })
        .collect()
}

/// Built-in programs and sysvars, by their 32 bytes.
#[expect(dead_code, reason = "used by the key_list rule")]
pub fn builtin() -> HashMap<[u8; 32], &'static str> {
    decode(BUILTIN_KEYS)
}

/// Every labelled address (built-in and other), by its 32 bytes.
pub fn all() -> HashMap<[u8; 32], &'static str> {
    let mut m = decode(BUILTIN_KEYS);
    m.extend(decode(OTHER_KEYS));
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_key_is_a_distinct_32_byte_address() {
        assert_eq!(builtin().len(), BUILTIN_KEYS.len());
        assert_eq!(all().len(), BUILTIN_KEYS.len() + OTHER_KEYS.len());
        // Round-trip: the label table holds canonical base58 strings.
        for (b58, _) in BUILTIN_KEYS.iter().chain(OTHER_KEYS) {
            let v = bs58::decode(b58).into_vec().unwrap();
            assert_eq!(&bs58::encode(&v).into_string(), b58);
        }
    }

    #[test]
    fn builtin_list_contains_the_precompiles_and_the_instructions_sysvar() {
        let labels: Vec<&str> = builtin().into_values().collect();
        for l in ["Ed25519 precompile", "secp256k1 precompile", "secp256r1 precompile",
                  "ZK ElGamal proof program", "Instructions sysvar"] {
            assert!(labels.contains(&l), "{l}");
        }
    }
}
