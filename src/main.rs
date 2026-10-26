//! pqready: census of Solana programs depending on quantum-vulnerable crypto.
//!
//!   pqready fetch --rpc http://127.0.0.1:8899 --out data/raw
//!   pqready scan --raw data/raw --out data/scans/2026-11-03
//!   pqready scan-one path/to/program.so

mod constprop;
mod elf;
mod fetch;
mod precompile;
mod sbpf;
mod syscalls;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use serde::Serialize;
use std::{fs, path::PathBuf};

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
}

#[derive(Serialize)]
struct DepRow<'a> {
    program_id: &'a str,
    loader: &'a str,
    upgradeable: bool,
    kind: &'a str,
    name: &'a str,
    class: &'a str,
    evidence: String,
    count: usize,
    selectors: String,
    unknown_selector_sites: usize,
    unreachable_sites: usize,
}

#[derive(Serialize)]
struct SummaryRow<'a> {
    program_id: &'a str,
    loader: &'a str,
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
    }
}

fn class_of(name: &str) -> &'static str {
    syscalls::by_name(name)
        .map(|s| s.class.as_str())
        .unwrap_or("unknown")
}

fn scan_one(path: &PathBuf) -> Result<()> {
    let bytes = fs::read(path).with_context(|| path.display().to_string())?;
    let table = syscalls::hash_table();
    let decoded_refs = precompile::decoded_refs();
    let r = elf::scan_elf(&bytes, &table)?;
    println!(
        "e_machine={} e_flags={:#x} functions={} indirect_calls={} roots_found={}",
        r.e_machine, r.e_flags, r.functions, r.indirect_calls, r.roots_found
    );
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
    for (rf, n) in precompile::find_refs(&bytes, &decoded_refs) {
        println!("precompile ref {:<28} x{n}", rf.name);
    }
    Ok(())
}

fn scan_all(raw: &PathBuf, out: &PathBuf) -> Result<()> {
    fs::create_dir_all(out)?;
    let table = syscalls::hash_table();
    let needles = precompile::decoded_refs();
    let mut rdr = csv::Reader::from_path(raw.join("programs.csv"))?;
    let mut deps = csv::Writer::from_path(out.join("dependencies.csv"))?;
    let mut summary = csv::Writer::from_path(out.join("scan_summary.csv"))?;
    let (mut scanned, mut flagged) = (0usize, 0usize);

    for row in rdr.deserialize::<fetch::ProgramRow>() {
        let p = row?;
        let elf_path = raw.join("elf").join(format!("{}.so", p.program_id));
        if !elf_path.exists() {
            continue; // closed, retracted, or not downloaded
        }
        let bytes = fs::read(&elf_path)?;
        scanned += 1;

        let mut s = SummaryRow {
            program_id: &p.program_id,
            loader: &p.loader,
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
        };

        // Precompile references are byte matches, so they work even if ELF parsing fails.
        for (rf, n) in precompile::find_refs(&bytes, &needles) {
            if rf.vulnerable {
                s.vulnerable_precompile_refs += 1;
            }
            deps.serialize(DepRow {
                program_id: &p.program_id,
                loader: &p.loader,
                upgradeable: p.upgradeable,
                kind: "precompile_ref",
                name: rf.name,
                class: if rf.vulnerable {
                    "quantum_vulnerable"
                } else {
                    "marker"
                },
                evidence: "rodata_bytes".into(),
                count: n,
                selectors: String::new(),
                unknown_selector_sites: 0,
                unreachable_sites: 0,
            })?;
        }

        match elf::scan_elf(&bytes, &table) {
            Ok(r) => {
                s.parse_ok = true;
                s.e_machine = Some(r.e_machine);
                s.e_flags = Some(r.e_flags);
                s.unresolved_static_hashes = r.unresolved_static_hashes.len();
                s.indirect_calls = r.indirect_calls;
                s.roots_found = r.roots_found;
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
                    deps.serialize(DepRow {
                        program_id: &p.program_id,
                        loader: &p.loader,
                        upgradeable: p.upgradeable,
                        kind: "syscall",
                        name,
                        class,
                        evidence: hit
                            .evidence
                            .iter()
                            .map(|e| e.as_str())
                            .collect::<Vec<_>>()
                            .join("+"),
                        count: hit.count,
                        selectors: hit
                            .selectors
                            .iter()
                            .map(|v| v.to_string())
                            .collect::<Vec<_>>()
                            .join(";"),
                        unknown_selector_sites: hit.unknown_selector_sites,
                        unreachable_sites: hit.unreachable_sites,
                    })?;
                }
                s.unknown_imports = unknown.join(";");
            }
            Err(e) => s.error = format!("{e:#}"),
        }
        if s.vulnerable_syscalls + s.vulnerable_precompile_refs > 0 {
            flagged += 1;
        }
        summary.serialize(&s)?;
    }
    deps.flush()?;
    summary.flush()?;
    eprintln!("scanned {scanned} ELFs; {flagged} with quantum-vulnerable dependencies");
    Ok(())
}
