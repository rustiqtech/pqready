//! Syscall names the scanner recognises, their classification, and the murmur3 hashes used by SBPF
//! static syscalls.
//!
//! VERIFY this list against Agave's syscall registry for the scanned release
//! (`create_program_runtime_environment` in the bpf_loader / syscalls crate). A missing name only
//! means its calls are reported as "unresolved static call hashes" or "unknown imports" instead of
//! being classified, so nothing is silently dropped.

use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// Elliptic-curve or RSA-style primitive broken by a quantum adversary.
    QuantumVulnerable,
    /// May or may not be used for something quantum-vulnerable; needs review.
    Review,
    /// Not vulnerable itself, but marks a design that usually is (e.g. Poseidon over BN254 implies
    /// a BN254 SNARK circuit).
    Marker,
    /// Known, irrelevant to PQ.
    Benign,
}

impl Class {
    pub fn as_str(self) -> &'static str {
        match self {
            Class::QuantumVulnerable => "quantum_vulnerable",
            Class::Review => "review",
            Class::Marker => "marker",
            Class::Benign => "benign",
        }
    }
}

pub struct Syscall {
    pub name: &'static str,
    pub class: Class,
    /// What register r1 means at the call site, if useful for classification.
    pub r1_meaning: &'static str,
}

const fn s(name: &'static str, class: Class, r1_meaning: &'static str) -> Syscall {
    Syscall {
        name,
        class,
        r1_meaning,
    }
}

use Class::*;

pub const SYSCALLS: &[Syscall] = &[
    // --- quantum-relevant ---
    s("sol_secp256k1_recover", QuantumVulnerable, ""),
    s("sol_curve_validate_point", QuantumVulnerable, "curve id"),
    s("sol_curve_group_op", QuantumVulnerable, "curve id"),
    s("sol_curve_multiscalar_mul", QuantumVulnerable, "curve id"),
    s("sol_curve_pairing_map", QuantumVulnerable, "curve id"),
    s(
        "sol_alt_bn128_group_op",
        QuantumVulnerable,
        "op (add/sub/mul/pairing)",
    ),
    s("sol_alt_bn128_compression", QuantumVulnerable, "op"),
    s("sol_big_mod_exp", Review, ""),
    s("sol_poseidon", Marker, "parameters"),
    // --- benign (listed so static calls to them resolve to a name) ---
    s("abort", Benign, ""),
    s("sol_panic_", Benign, ""),
    s("sol_log_", Benign, ""),
    s("sol_log_64_", Benign, ""),
    s("sol_log_pubkey", Benign, ""),
    s("sol_log_compute_units_", Benign, ""),
    s("sol_log_data", Benign, ""),
    s("sol_create_program_address", Benign, ""),
    s("sol_try_find_program_address", Benign, ""),
    s("sol_sha256", Benign, ""),
    s("sol_keccak256", Benign, ""),
    s("sol_blake3", Benign, ""),
    s("sol_get_clock_sysvar", Benign, ""),
    s("sol_get_epoch_schedule_sysvar", Benign, ""),
    s("sol_get_fees_sysvar", Benign, ""),
    s("sol_get_rent_sysvar", Benign, ""),
    s("sol_get_epoch_rewards_sysvar", Benign, ""),
    s("sol_get_last_restart_slot", Benign, ""),
    s("sol_get_sysvar", Benign, ""),
    s("sol_get_epoch_stake", Benign, ""),
    s("sol_memcpy_", Benign, ""),
    s("sol_memmove_", Benign, ""),
    s("sol_memcmp_", Benign, ""),
    s("sol_memset_", Benign, ""),
    s("sol_invoke_signed_c", Benign, ""),
    s("sol_invoke_signed_rust", Benign, ""),
    s("sol_alloc_free_", Benign, ""),
    s("sol_set_return_data", Benign, ""),
    s("sol_get_return_data", Benign, ""),
    s("sol_get_processed_sibling_instruction", Benign, ""),
    s("sol_get_stack_height", Benign, ""),
    s("sol_remaining_compute_units", Benign, ""),
];

pub fn by_name(name: &str) -> Option<&'static Syscall> {
    SYSCALLS.iter().find(|s| s.name == name)
}

/// murmur3_32 with seed 0, as used by SBPF to hash symbol names.
pub fn murmur3_32(data: &[u8], seed: u32) -> u32 {
    const C1: u32 = 0xcc9e_2d51;
    const C2: u32 = 0x1b87_3593;
    let mut h = seed;
    let blocks = data.len() / 4;
    for i in 0..blocks {
        let mut k = u32::from_le_bytes(data[4 * i..4 * i + 4].try_into().unwrap());
        k = k.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
        h ^= k;
        h = h.rotate_left(13).wrapping_mul(5).wrapping_add(0xe654_6b64);
    }
    let tail = &data[4 * blocks..];
    let mut k1 = 0u32;
    if tail.len() >= 3 {
        k1 ^= (tail[2] as u32) << 16;
    }
    if tail.len() >= 2 {
        k1 ^= (tail[1] as u32) << 8;
    }
    if !tail.is_empty() {
        k1 ^= tail[0] as u32;
        k1 = k1.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
        h ^= k1;
    }
    h ^= data.len() as u32;
    h ^= h >> 16;
    h = h.wrapping_mul(0x85eb_ca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2_ae35);
    h ^= h >> 16;
    h
}

pub fn syscall_hash(name: &str) -> u32 {
    murmur3_32(name.as_bytes(), 0)
}

/// hash -> syscall, for resolving static-syscall call immediates.
pub fn hash_table() -> HashMap<u32, &'static Syscall> {
    SYSCALLS.iter().map(|s| (syscall_hash(s.name), s)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn murmur3_reference_vectors() {
        assert_eq!(murmur3_32(b"", 0), 0);
        assert_eq!(murmur3_32(b"hello", 0), 0x248b_fa47);
        assert_eq!(
            murmur3_32(b"The quick brown fox jumps over the lazy dog", 0),
            0x2e4f_f723
        );
    }

    #[test]
    fn known_syscall_hashes() {
        // Cross-checked against Python mmh3 (seed 0) and Solana's published values.
        assert_eq!(syscall_hash("abort"), 0xb6fc_1a11);
        assert_eq!(syscall_hash("sol_log_"), 0x2075_59bd);
        assert_eq!(syscall_hash("sol_secp256k1_recover"), 0x17e4_0350);
        assert_eq!(syscall_hash("sol_alt_bn128_group_op"), 0xae0c_318b);
        assert_eq!(syscall_hash("sol_curve_group_op"), 0xdd1c_41a6);
    }

    #[test]
    fn hash_table_has_no_collisions() {
        assert_eq!(hash_table().len(), SYSCALLS.len());
    }
}
