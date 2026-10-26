# pqready

Finds Solana on-chain programs that depend on elliptic-curve and other quantum-vulnerable public-key cryptography (curve syscalls, RSA-style modular exponentiation and signature precompiles).

## Usage

```sh
cargo build --release

# 1. Pull program metadata and ELFs from your node (resumable: existing ELFs are skipped)
./target/release/pqready fetch --rpc http://127.0.0.1:8899 --out data/raw
#    metadata only, fast first pass:
./target/release/pqready fetch --rpc http://127.0.0.1:8899 --out data/raw --skip-elfs

# 2. Scan
./target/release/pqready scan --raw data/raw --out data/scans/$(date +%F)

# Validate on a single binary
./target/release/pqready scan-one data/raw/elf/<program-id>.so
```

Node requirement: `--account-index program-id`, otherwise `getProgramAccounts` on the loaders scans the whole accounts DB and may time out.

## Outputs

- `data/raw/programs.csv`: program ID, loader, ProgramData address, deploy slot, `upgradeable`, upgrade authority, status (deployed/closed/retracted/finalized), ELF length and SHA-256, fetch slot.
- `data/raw/elf/<program-id>.so`: the ELFs.
- `scans/<date>/dependencies.csv`: one row per program & dependency: kind (`syscall` / `precompile_ref`), name, class, evidence, count, r1 hints.
- `scans/<date>/scan_summary.csv`: one row per program: parse status, counts, unresolved static-call hashes, unknown imports.

## How detection works

- **Call sites**: code is decoded into instructions and a control-flow graph per function (`sbpf.rs`). Syscall calls are identified by relocation (legacy: `R_BPF_64_32` against an undefined symbol) or by static-syscall hash (`call` with src = 0, imm = murmur3_32(name)). Unknown hash-like immediates are reported, not dropped.
- **Selectors** (`constprop.rs`): for `sol_curve_*` (curve id) and `sol_alt_bn128_*` (operation), the set of constant values r1 can hold on every path into the call, by constant propagation within functions and across direct calls (so selectors passed through non-inlined wrappers are traced to their callers). A site where any path gives a non-constant value counts as `unknown_selector_sites`. Values are never guessed.
- **Reachability**: roots are the entry point, exported functions and functions whose address is taken (relocations, `lddw` constants). Syscall sites not reachable from a root through direct calls count as `unreachable_sites` (possible dead code). `indirect_calls` (`callx`) marks programs where missed address-taken functions could make selector sets incomplete.
- **Precompile references**: the 32-byte program IDs of the Ed25519, secp256k1 and secp256r1 precompiles, the ZK ElGamal proof program and the Instructions sysvar, found in the ELF bytes. A candidate signal, neither necessary nor sufficient for a dependency: establish it by source review or differential simulation.

## Verify before trusting counts

- Cross-reference the syscall name list in `src/syscalls.rs` against Agave's registry for the scanned release. Missing names surface as `unknown_imports` or unresolved hashes, not as silent misses.
- Double-check account layouts in `src/fetch.rs` (upgradeable ProgramData header = 45 bytes; loader-v4 header = 48 bytes, status codes).
- Confirm curve-id and alt_bn128 operation constants, to interpret r1 hints.
- Verify static-syscall encoding for the SBPF versions in use (`e_flags` is recorded).
- Check for known positives: a ZK Compression program (alt_bn128), a bridge core (secp256k1), a passkey wallet (secp256r1), Token-2022 (ZK ElGamal ref).

## Tested so far

Unit tests: murmur3 reference vectors, known syscall hashes, ProgramData header parsing, precompile matching, and the analysis (straight-line constants, branch merges, values from memory, calls clobbering r1-r5, selectors through wrappers, exported wrappers, unreachable sites, `lddw` slot counting, unknown hashes, `callx`). End-to-end on clang-compiled BPF objects: selectors through a non-inlined wrapper ({0, 1}), a branch-chosen BN254 operation ({2, 3}), an exported wrapper (unknown), and a kept-but-uncalled function (unreachable).
