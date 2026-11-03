//! pqready: census of Solana programs depending on quantum-vulnerable crypto.
//!
//!   pqready fetch --rpc http://127.0.0.1:8899 --out data/raw
//!   pqready scan --raw data/raw --out data/scans/2026-11-03
//!   pqready scan-one path/to/program.so

mod address;
mod constprop;
mod elf;
mod fetch;
mod identity;
mod keys;
mod pqtables;
mod precompile;
mod profile;
mod sbpf;
mod syscalls;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use rayon::prelude::*;
use serde::Serialize;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Download program metadata and ELFs from an RPC node.
    Fetch {
        #[arg(long, default_value = "http://127.0.0.1:8899")]
        rpc: String,
        #[arg(long, default_value = "data/raw")]
        out: PathBuf,
        /// Accounts per getMultipleAccounts call (max 100).
        #[arg(long, default_value_t = 100)]
        batch: usize,
        /// Metadata only (upgradeability, authorities); no ELF download.
        #[arg(long)]
        skip_elfs: bool,
    },
    /// Scan downloaded ELFs and write dependency tables.
    Scan {
        #[arg(long, default_value = "data/raw")]
        raw: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    /// Scan a single ELF and print what was found (for validation).
    ScanOne { path: PathBuf },
    /// Show the 32-byte entries around an address in a program's data, labelled where they are
    /// built-in programs or sysvars, and the instructions that load addresses in that range. For
    /// reviewing precompile and key-list rows.
    Inspect {
        path: PathBuf,
        /// Address as printed by scan-one, e.g. 0x15e0.
        #[arg(value_parser = parse_address)]
        address: u64,
        #[arg(long, default_value_t = 12)]
        before: u64,
        #[arg(long, default_value_t = 12)]
        after: u64,
    },
    /// One row per flagged program (classes quantum_vulnerable, review, pq_implementation): name
    /// from security.txt or the on-chain IDL, what the crypto is used for, the upgrade authority
    /// and how many programs it controls, joined with optional labels, reviews and activity CSVs.
    Profile {
        #[arg(long, default_value = "data/raw")]
        raw: PathBuf,
        /// Directory with dependencies.csv from `scan`.
        #[arg(long)]
        scan: PathBuf,
        #[arg(long)]
        out: PathBuf,
        /// Fetch IDL accounts (legacy Anchor, Program Metadata) from this RPC.
        #[arg(long)]
        rpc: Option<String>,
        /// CSV with `label` and `program_id` or `authority`; other columns are copied.
        #[arg(long)]
        labels: Option<PathBuf>,
        /// CSV keyed by `program_id`; columns copied with a `review_` prefix.
        #[arg(long)]
        reviews: Option<PathBuf>,
        /// CSV keyed by `program_id`; columns copied with an `activity_` prefix.
        #[arg(long)]
        activity: Option<PathBuf>,
        /// Output column to sort by: numbers descending, text ascending.
        #[arg(long)]
        sort_by: Option<String>,
    },
}

#[derive(Serialize)]
struct DepRow {
    program_id: String,
    loader: String,
    upgradeable: bool,
    kind: &'static str,
    name: String,
    class: &'static str,
    evidence: String,
    count: usize,
    selectors: String,
    unknown_selector_sites: usize,
    unreachable_sites: usize,
}

#[derive(Serialize)]
struct SummaryRow {
    program_id: String,
    loader: String,
    upgradeable: bool,
    e_machine: Option<u16>,
    e_flags: Option<u32>,
    parse_ok: bool,
    error: String,
    vulnerable_syscalls: usize,
    vulnerable_precompile_refs: usize,
    unresolved_static_hashes: usize,
    indirect_calls: usize,
    roots_found: bool,
    unknown_imports: String,
    parse_note: String,
}

fn main() -> Result<()> {
    match Cli::parse().cmd {
        Cmd::Fetch {
            rpc,
            out,
            batch,
            skip_elfs,
        } => fetch::run(&fetch::FetchOpts {
            rpc,
            out,
            batch,
            skip_elfs,
        }),
        Cmd::Scan { raw, out } => scan_all(&raw, &out),
        Cmd::ScanOne { path } => scan_one(&path),
        Cmd::Inspect {
            path,
            address,
            before,
            after,
        } => inspect(&path, address, before, after),

        Cmd::Profile {
            raw,
            scan,
            out,
            rpc,
            labels,
            reviews,
            activity,
            sort_by,
        } => profile::run(&profile::ProfileOpts {
            raw,
            scan,
            out,
            rpc,
            labels,
            reviews,
            activity,
            sort_by,
        }),
    }
}

fn parse_address(s: &str) -> Result<u64, String> {
    let t = s.trim();
    match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        Some(h) => u64::from_str_radix(h, 16),
        None => t.parse(),
    }
    .map_err(|e| format!("{s:?}: {e}"))
}

fn inspect(path: &Path, address: u64, before: u64, after: u64) -> Result<()> {
    let bytes = fs::read(path).with_context(|| path.display().to_string())?;
    let r = elf::inspect(&bytes, address, before, after)?;
    let labels = keys::all();
    println!("entries (32 bytes each; * = {address:#x}):");
    for (a, e) in &r.entries {
        let mark = if *a == address { '*' } else { ' ' };
        match e {
            Some(b) => {
                let label = labels.get(b).copied().unwrap_or("");
                println!(
                    "{mark} {a:#10x}  {:<44}  {label}",
                    bs58::encode(b).into_string()
                );
            }
            None => println!("{mark} {a:#10x}  (not in loaded data)"),
        }
    }
    println!("\nlddw instructions loading an address in this range:");
    if r.loads.is_empty() {
        println!("  none");
    }
    for (insn, v) in &r.loads {
        // V3 code may use the run-time address (base 2^32) of the same data.
        let t = (*v as u64)
            .checked_sub(1 << 32)
            .filter(|t| *t < (1 << 32))
            .unwrap_or(*v as u64);
        let rel = (t as i64 - address as i64).div_euclid(32);
        println!("  at {insn:#x}: {v:#x}  (entry {rel:+} from {address:#x})");
    }
    Ok(())
}

fn class_of(name: &str) -> &'static str {
    syscalls::by_name(name)
        .map(|s| s.class.as_str())
        .unwrap_or("unknown")
}

fn scan_one(path: &Path) -> Result<()> {
    let bytes = fs::read(path).with_context(|| path.display().to_string())?;
    let table = syscalls::hash_table();
    let rbs = precompile::decoded_refs();
    let r = elf::scan_elf(&bytes, &table, &rbs)?;
    println!(
        "e_machine={} e_flags={:#x} functions={} indirect_calls={} roots_found={}",
        r.e_machine, r.e_flags, r.functions, r.indirect_calls, r.roots_found
    );
    if !r.parse_note.is_empty() {
        println!("note: {}", r.parse_note);
    }
    for (name, hit) in &r.syscalls {
        let ev: Vec<_> = hit.evidence.iter().map(|e| e.as_str()).collect();
        println!(
            "syscall {name:<36} class={:<18} sites={:<4} evidence={} selectors={:?} unknown_selector_sites={} unreachable_sites={}",
            class_of(name),
            hit.count,
            ev.join("+"),
            hit.selectors,
            hit.unknown_selector_sites,
            hit.unreachable_sites
        );
    }
    for (h, n) in &r.unresolved_static_hashes {
        println!("unresolved static call hash {h:#010x} x{n}");
    }
    for t in &r.pq_tables {
        println!(
            "pq table {:<13} form={:<28} at {:#x} windows={}/{} code_refs={}",
            t.scheme, t.form, t.address, t.windows_matched, t.windows_tried, t.code_refs
        );
    }
    if r.keccak_constants_inline > 0 {
        println!(
            "pq keccak round constants as lddw: {}/24 distinct",
            r.keccak_constants_inline
        );
    }
    for (name, n) in &r.pq_weak {
        println!("pq weak signal {name}: {n} immediates");
    }
    for id in r.located_ids.iter().filter(|id| id.in_file) {
        let addrs: Vec<String> = id.addresses.iter().map(|a| format!("{a:#x}")).collect();
        println!(
            "precompile id {:<28} addresses={} [{}]",
            id.r.name,
            id.addresses.len(),
            addrs.join(", ")
        );
    }
    Ok(())
}

fn scan_all(raw: &Path, out: &Path) -> Result<()> {
    fs::create_dir_all(out)?;
    let table = syscalls::hash_table();
    let rbs = precompile::decoded_refs();

    // Programs with a downloaded ELF (closed, retracted or skipped ones have none).
    let mut programs = Vec::new();
    for row in csv::Reader::from_path(raw.join("programs.csv"))?.deserialize::<fetch::ProgramRow>()
    {
        let p = row?;
        if elf_path(raw, &p).exists() {
            programs.push(p);
        }
    }

    // Programs are independent: scan them in parallel. `collect` keeps input
    // order, so the CSVs are identical to a sequential run.
    let total = programs.len();
    let done = AtomicUsize::new(0);
    let step = (total / 20).max(1);
    let results: Vec<(SummaryRow, Vec<DepRow>)> = programs
        .par_iter()
        .map(|p| {
            let r = scan_program(p, raw, &table, &rbs);
            let n = done.fetch_add(1, Ordering::Relaxed) + 1;
            if n % step == 0 || n == total {
                eprintln!("scanned {n}/{total}");
            }
            r
        })
        .collect();

    let mut deps = csv::Writer::from_path(out.join("dependencies.csv"))?;
    let mut summary = csv::Writer::from_path(out.join("scan_summary.csv"))?;
    let mut flagged = 0usize;
    for (s, ds) in &results {
        if s.vulnerable_syscalls + s.vulnerable_precompile_refs > 0 {
            flagged += 1;
        }
        for d in ds {
            deps.serialize(d)?;
        }
        summary.serialize(s)?;
    }
    deps.flush()?;
    summary.flush()?;
    eprintln!("scanned {total} ELFs; {flagged} with quantum-vulnerable dependencies");
    Ok(())
}

fn elf_path(raw: &Path, p: &fetch::ProgramRow) -> PathBuf {
    raw.join("elf").join(format!("{}.so", p.program_id))
}

/// Rows for PQ implementations found by their constant tables (`pqtables`). Lattice tables (ML-DSA,
/// ML-KEM, Falcon) are `pq_implementation`. Keccak round constants only support such a hit, hence
/// `marker`. Moduli among immediates are `weak`. `count` is the number of reachable code references
/// (tables) or occurrences (immediates).
fn pq_rows<'a>(
    r: &elf::ElfReport,
    dep: &dyn Fn(&'static str, &str, &'static str, String) -> DepRow,
) -> Vec<DepRow> {
    let mut rows = Vec::new();
    for t in &r.pq_tables {
        let class = if t.scheme == "keccak-f1600" {
            "marker"
        } else {
            "pq_implementation"
        };
        let evidence = format!(
            "table {} at {:#x}, windows {}/{}",
            t.form, t.address, t.windows_matched, t.windows_tried
        );
        rows.push(DepRow {
            count: t.code_refs,
            ..dep("pq_table", t.scheme, class, evidence)
        });
    }
    if r.keccak_constants_inline > 0 {
        let evidence = format!(
            "round constants as lddw, {}/24 distinct",
            r.keccak_constants_inline
        );
        rows.push(DepRow {
            count: r.keccak_constants_inline,
            ..dep("pq_table", "keccak-f1600", "marker", evidence)
        });
    }
    for (name, n) in &r.pq_weak {
        rows.push(DepRow {
            count: *n,
            ..dep("pq_table", name, "weak", "immediates".into())
        });
    }
    rows
}

/// Scan one program's ELF. Never fails: read and parse errors are recorded in the summary row so
/// one bad file does not stop the run.
fn scan_program(
    p: &fetch::ProgramRow,
    raw: &Path,
    table: &HashMap<u32, &'static syscalls::Syscall>,
    rbs: &[precompile::RefBytes],
) -> (SummaryRow, Vec<DepRow>) {
    let mut s = SummaryRow {
        program_id: p.program_id.clone(),
        loader: p.loader.clone(),
        upgradeable: p.upgradeable,
        e_machine: None,
        e_flags: None,
        parse_ok: false,
        error: String::new(),
        vulnerable_syscalls: 0,
        vulnerable_precompile_refs: 0,
        unresolved_static_hashes: 0,
        indirect_calls: 0,
        roots_found: false,
        unknown_imports: String::new(),
        parse_note: String::new(),
    };
    let mut deps = Vec::new();
    let dep = |kind, name: &str, class, evidence: String| DepRow {
        program_id: p.program_id.clone(),
        loader: p.loader.clone(),
        upgradeable: p.upgradeable,
        kind,
        name: name.to_string(),
        class,
        evidence,
        count: 0,
        selectors: String::new(),
        unknown_selector_sites: 0,
        unreachable_sites: 0,
    };

    let bytes = match fs::read(elf_path(raw, p)) {
        Ok(b) => b,
        Err(e) => {
            s.error = format!("read: {e}");
            return (s, deps);
        }
    };

    match elf::scan_elf(&bytes, table, rbs) {
        Ok(r) => {
            s.parse_ok = true;
            s.e_machine = Some(r.e_machine);
            s.e_flags = Some(r.e_flags);
            s.unresolved_static_hashes = r.unresolved_static_hashes.len();
            s.indirect_calls = r.indirect_calls;
            s.roots_found = r.roots_found;
            s.parse_note = r.parse_note.clone();
            let mut unknown = Vec::new();
            for (name, hit) in &r.syscalls {
                let class = class_of(name);
                match class {
                    "quantum_vulnerable" => s.vulnerable_syscalls += 1,
                    "unknown" => unknown.push(name.clone()),
                    _ => {}
                }
                if class == "benign" {
                    continue;
                }
                let evidence = hit
                    .evidence
                    .iter()
                    .map(|e| e.as_str())
                    .collect::<Vec<_>>()
                    .join("+");
                deps.push(DepRow {
                    count: hit.count,
                    selectors: hit
                        .selectors
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(";"),
                    unknown_selector_sites: hit.unknown_selector_sites,
                    unreachable_sites: hit.unreachable_sites,
                    ..dep("syscall", name, class, evidence)
                });
            }
            s.unknown_imports = unknown.join(";");
            deps.extend(pq_rows(&r, &dep));

            // where each ID's bytes occur, presence only
            for id in r.located_ids.iter().filter(|id| id.in_file) {
                let (evidence, count) = if id.addresses.is_empty() {
                    ("bytes_outside_data", 1)
                } else {
                    ("bytes_in_data", id.addresses.len())
                };
                let class = if id.r.vulnerable { "review" } else { "marker" };
                deps.push(DepRow {
                    count,
                    ..dep("precompile_ref", id.r.name, class, evidence.into())
                });
            }
        }
        Err(e) => s.error = format!("{e:#}"),
    }
    (s, deps)
}
