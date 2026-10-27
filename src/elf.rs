//! ELF front end. Finds syscall imports and call sites, collects analysis roots, and runs
//! control-flow and constant-propagation analysis (`cfg`, `constprop`) over each executable range.
//!
//! Syscall call sites come in two encodings, both handled whatever SBPF version the ELF declares:
//!
//! - legacy: the call's immediate is a placeholder and a relocation (R_BPF_64_32) names an
//! undefined symbol such as `sol_secp256k1_recover`;
//!
//! - static syscalls: `call` with src = 0 and imm = murmur3_32(name).
//!
//! For sol_curve_* and sol_alt_bn128_*, register r1 holds a selector (curve id or operation). The
//! analysis reports, per call site, the set of constant values r1 can hold on every path into the
//! call, following values through non-inlined wrapper functions to their direct callers. Where any
//! path yields a non-constant value, the site is counted as unknown instead.
//!
//! Dynamic symbols, strings and relocations normally come from the dynamic segment (DT_SYMTAB,
//! DT_STRTAB, DT_REL/DT_RELA). Some deployed programs place those tables outside every PT_LOAD
//! segment, so their addresses cannot be mapped to file offsets through program headers. goblin
//! then reads them from file offset 0 (the ELF header) and fails, or returns garbage. In that case
//! the tables are taken from the section headers instead (`.dynsym`, its linked string table, and
//! the relocation sections linked to it), and the report carries a `parse_note` saying so.
//!
//! Roots (entry point, exported functions, functions whose address is taken) define reachability.
//! syscall site not reachable from any root through direct calls is counted separately as possible
//! dead code.

use crate::constprop::analyze_range;
use crate::sbpf::{Code, OP_LDDW, RelocCall, classify_calls};
use crate::syscalls::{Syscall, by_name};
use anyhow::{Context, Result, bail};
use goblin::container::{Container, Ctx};
use goblin::elf::{Elf, dynamic, header, program_header, reloc::RelocSection, section_header, sym};
use goblin::strtab::Strtab;
use std::collections::{BTreeMap, BTreeSet, HashMap};

const R_BPF_64_64: u32 = 1;
const R_BPF_64_RELATIVE: u32 = 8;
const R_BPF_64_32: u32 = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Evidence {
    Relocation,
    DynamicSymbol,
    StaticCall,
}

impl Evidence {
    pub fn as_str(self) -> &'static str {
        match self {
            Evidence::Relocation => "relocation",
            Evidence::DynamicSymbol => "dynamic_symbol",
            Evidence::StaticCall => "static_call",
        }
    }
}

#[derive(Debug, Default)]
pub struct Hit {
    pub evidence: BTreeSet<Evidence>,
    /// Call sites found in executable code (0 = imported but never called).
    pub count: usize,
    /// Union of selector values proven at call sites (selector syscalls only).
    pub selectors: BTreeSet<i64>,
    /// Call sites whose selector is not constant on every path.
    pub unknown_selector_sites: usize,
    /// Call sites not reachable from any root through direct calls.
    pub unreachable_sites: usize,
}

#[derive(Debug, Default)]
pub struct ElfReport {
    pub e_machine: u16,
    pub e_flags: u32,
    pub syscalls: BTreeMap<String, Hit>,
    /// `call` immediates (src = 0) matching no known syscall name.
    pub unresolved_static_hashes: BTreeMap<u32, usize>,
    /// `callx` instructions; selector sets may be incomplete if these reach functions whose
    /// address-taking we did not detect.
    pub indirect_calls: usize,
    pub functions: usize,
    /// False if no entry point, exported function or address-taken function was found; reachability
    /// is then not meaningful and is not reported.
    pub roots_found: bool,
    /// Non-empty when the ELF needed a fallback to be parsed (see module docs).
    pub parse_note: String,
}

struct Range {
    file_start: usize,
    file_end: usize,
    vaddr_start: u64,
}

pub fn scan_elf(bytes: &[u8], table: &HashMap<u32, &'static Syscall>) -> Result<ElfReport> {
    // goblin fails on unmappable dynamic tables; retry with the dynamic
    // segment hidden, then read those tables from the section headers.
    let patched;
    let (mut elf, failed) = match Elf::parse(bytes) {
        Ok(e) => (e, None),
        Err(first) => {
            patched = without_dynamic_segment(bytes)
                .ok_or(first)
                .context("ELF parse")?;
            (
                Elf::parse(&patched).context("ELF parse (dynamic segment hidden)")?,
                Some(()),
            )
        }
    };
    let mut parse_note = String::new();
    if failed.is_some() || !dynamic_tables_mapped(&elf) {
        if dynamic_from_sections(bytes, &mut elf)? {
            parse_note = "dynamic tables outside loaded segments; read from section headers".into();
        } else if failed.is_some() {
            bail!("ELF parse: dynamic tables outside loaded segments and no .dynsym section");
        } else {
            parse_note = "dynamic tables outside loaded segments and no .dynsym section; imports may be missing".into();
        }
    }
    let mut report = ElfReport {
        e_machine: elf.header.e_machine,
        e_flags: elf.header.e_flags,
        parse_note,
        ..Default::default()
    };
    let ranges = executable_ranges(&elf, bytes.len());
    let is_rel = elf.header.e_type == header::ET_REL;
    let section_off = |shndx: usize| elf.section_headers.get(shndx).map(|s| s.sh_offset as usize);

    // Call sites patched by relocations, keyed by file offset of the call.
    let mut reloc_calls: HashMap<usize, RelocCall> = HashMap::new();
    // Function addresses taken by relocations or lddw (become roots).
    let mut taken_vaddrs: BTreeSet<u64> = BTreeSet::new();
    let mut taken_files: BTreeSet<usize> = BTreeSet::new();
    // Exported functions and the entry point (become roots).
    let mut root_vaddrs: BTreeSet<u64> = BTreeSet::new();
    let mut root_files: BTreeSet<usize> = BTreeSet::new();

    // Dynamic relocations (deployed programs).
    for reloc in elf
        .dynrels
        .iter()
        .chain(elf.dynrelas.iter())
        .chain(elf.pltrelocs.iter())
    {
        let sym = (reloc.r_sym != 0)
            .then(|| elf.dynsyms.get(reloc.r_sym))
            .flatten();
        match reloc.r_type {
            R_BPF_64_32 => {
                let Some(sym) = sym else { continue };
                let Some(site) = vaddr_to_file(&elf, reloc.r_offset) else {
                    continue;
                };
                if sym.st_shndx == 0 {
                    let Some(name) = elf.dynstrtab.get_at(sym.st_name).filter(|n| !n.is_empty())
                    else {
                        continue;
                    };
                    report
                        .syscalls
                        .entry(name.to_string())
                        .or_default()
                        .evidence
                        .insert(Evidence::Relocation);
                    reloc_calls.insert(site, RelocCall::Syscall(name.to_string()));
                } else if let Some(target) = vaddr_to_file(&elf, sym.st_value) {
                    reloc_calls.insert(site, RelocCall::Internal(target));
                }
            }
            R_BPF_64_64 => {
                if let Some(sym) = sym.filter(|s| s.st_shndx != 0 && s.st_type() == sym::STT_FUNC) {
                    taken_vaddrs.insert(sym.st_value);
                }
            }
            R_BPF_64_RELATIVE => {
                if let Some(v) = relative_target(bytes, &elf, &ranges, reloc.r_offset) {
                    taken_vaddrs.insert(v);
                }
            }
            _ => {}
        }
    }

    // 2. Section relocations (relocatable objects only: in linked programs these
    //    sections include .rel.dyn, already handled above with the right symbols).
    for (reloc_sec, relocs) in elf.shdr_relocs.iter().filter(|_| is_rel) {
        let Some(target_sec) = elf
            .section_headers
            .get(*reloc_sec)
            .and_then(|rs| section_off(rs.sh_info as usize))
        else {
            continue;
        };
        for reloc in relocs.iter() {
            let Some(sym) = (reloc.r_sym != 0)
                .then(|| elf.syms.get(reloc.r_sym))
                .flatten()
            else {
                continue;
            };
            let site = target_sec + reloc.r_offset as usize;
            match reloc.r_type {
                R_BPF_64_32 if sym.st_shndx == 0 => {
                    let Some(name) = elf.strtab.get_at(sym.st_name).filter(|n| !n.is_empty())
                    else {
                        continue;
                    };
                    report
                        .syscalls
                        .entry(name.to_string())
                        .or_default()
                        .evidence
                        .insert(Evidence::Relocation);
                    reloc_calls.insert(site, RelocCall::Syscall(name.to_string()));
                }
                R_BPF_64_32 if sym.st_type() == sym::STT_FUNC => {
                    if let Some(off) = section_off(sym.st_shndx) {
                        reloc_calls.insert(site, RelocCall::Internal(off + sym.st_value as usize));
                    }
                }
                R_BPF_64_64 if sym.st_shndx != 0 && sym.st_type() == sym::STT_FUNC => {
                    if let Some(off) = section_off(sym.st_shndx) {
                        taken_files.insert(off + sym.st_value as usize);
                    }
                }
                _ => {}
            }
        }
    }

    // Undefined dynamic symbols with no relocation still indicate an import.
    for s in elf
        .dynsyms
        .iter()
        .filter(|s| s.st_shndx == 0 && s.st_name != 0)
    {
        if let Some(name) = elf.dynstrtab.get_at(s.st_name).filter(|n| !n.is_empty()) {
            report
                .syscalls
                .entry(name.to_string())
                .or_default()
                .evidence
                .insert(Evidence::DynamicSymbol);
        }
    }

    // Roots: entry point and externally visible functions.
    if !is_rel && elf.header.e_entry != 0 {
        root_vaddrs.insert(elf.header.e_entry);
    }
    let exported = |s: &sym::Sym| {
        s.st_shndx != 0
            && s.st_type() == sym::STT_FUNC
            && matches!(s.st_bind(), sym::STB_GLOBAL | sym::STB_WEAK)
    };
    for s in elf.dynsyms.iter().chain(elf.syms.iter()).filter(exported) {
        if is_rel {
            if let Some(off) = section_off(s.st_shndx) {
                root_files.insert(off + s.st_value as usize);
            }
        } else {
            root_vaddrs.insert(s.st_value);
        }
    }

    // Analyse each executable range.
    for r in &ranges {
        let code = Code::decode(
            &bytes[r.file_start..r.file_end],
            r.file_start,
            r.vaddr_start,
        );
        let calls = classify_calls(&code, &reloc_calls, table);

        let mut roots: BTreeSet<usize> = BTreeSet::new();
        for v in root_vaddrs.iter().chain(&taken_vaddrs) {
            roots.extend(code.idx_at_vaddr(*v));
        }
        for f in root_files.iter().chain(&taken_files) {
            roots.extend(code.idx_at_file(*f));
        }
        // Addresses of functions loaded as constants (function pointers).
        if !is_rel {
            for i in code.insns.iter().filter(|i| i.opc == OP_LDDW) {
                roots.extend(code.idx_at_vaddr(i.imm64 as u64));
            }
        }
        let roots_found = !roots.is_empty();
        if !roots_found && !code.insns.is_empty() {
            roots.insert(0); // analyse from the start; reachability not reported
        }
        report.roots_found |= roots_found;

        let res = analyze_range(&code, &calls, &roots);
        report.indirect_calls += res.indirect_calls;
        report.functions += res.functions;
        for (h, n) in res.unresolved {
            *report.unresolved_static_hashes.entry(h).or_default() += n;
        }
        for site in res.sites {
            let wants_selector = by_name(&site.name).is_some_and(|s| !s.r1_meaning.is_empty());
            let hit = report.syscalls.entry(site.name).or_default();
            hit.evidence.insert(if site.via_reloc {
                Evidence::Relocation
            } else {
                Evidence::StaticCall
            });
            hit.count += 1;
            if roots_found && !site.reachable {
                hit.unreachable_sites += 1;
            }
            if wants_selector {
                match site.selectors {
                    Some(s) => hit.selectors.extend(s),
                    None => hit.unknown_selector_sites += 1,
                }
            }
        }
    }
    Ok(report)
}

const DYN_TABLE_TAGS: [u64; 4] = [
    dynamic::DT_SYMTAB,
    dynamic::DT_STRTAB,
    dynamic::DT_REL,
    dynamic::DT_RELA,
];

fn in_load_segment(elf: &Elf, vaddr: u64) -> bool {
    elf.program_headers.iter().any(|ph| {
        ph.p_type == program_header::PT_LOAD
            && vaddr >= ph.p_vaddr
            && vaddr - ph.p_vaddr < ph.p_memsz
    })
}

/// True if every dynamic table address maps into a PT_LOAD segment (or there
/// is no dynamic segment).
fn dynamic_tables_mapped(elf: &Elf) -> bool {
    elf.dynamic.as_ref().is_none_or(|d| {
        d.dyns
            .iter()
            .filter(|e| DYN_TABLE_TAGS.contains(&e.d_tag))
            .all(|e| in_load_segment(elf, e.d_val))
    })
}

/// Copy of the ELF with its PT_DYNAMIC program header turned into PT_NULL, so
/// goblin skips the dynamic segment. None if there is nothing to hide.
fn without_dynamic_segment(bytes: &[u8]) -> Option<Vec<u8>> {
    let header = Elf::parse_header(bytes).ok()?;
    let mut out = bytes.to_vec();
    let little = header.e_ident[header::EI_DATA] == header::ELFDATA2LSB;
    let mut hidden = false;
    for i in 0..header.e_phnum as usize {
        let at = (header.e_phoff as usize).checked_add(i * header.e_phentsize as usize)?;
        let field = out.get_mut(at..at + 4)?;
        let p_type = if little {
            u32::from_le_bytes(field.try_into().ok()?)
        } else {
            u32::from_be_bytes(field.try_into().ok()?)
        };
        if p_type == program_header::PT_DYNAMIC {
            field.copy_from_slice(&[0; 4]); // PT_NULL
            hidden = true;
        }
    }
    hidden.then_some(out)
}

/// Replace goblin's dynamic symbols, strings and relocations with those found
/// through section headers. Returns false if there is no `.dynsym` section.
fn dynamic_from_sections<'a>(bytes: &'a [u8], elf: &mut Elf<'a>) -> Result<bool> {
    let Some(dynsym_idx) = elf
        .section_headers
        .iter()
        .position(|s| s.sh_type == section_header::SHT_DYNSYM)
    else {
        return Ok(false);
    };
    let ctx = Ctx::new(
        if elf.is_64 {
            Container::Big
        } else {
            Container::Little
        },
        if elf.little_endian {
            goblin::container::Endian::Little
        } else {
            goblin::container::Endian::Big
        },
    );
    let in_file = |off: u64, size: u64| {
        off.checked_add(size)
            .is_some_and(|end| end <= bytes.len() as u64)
    };
    let ds = &elf.section_headers[dynsym_idx];
    let sym_size = if elf.is_64 { 24 } else { 16 };
    if !in_file(ds.sh_offset, ds.sh_size) {
        bail!(".dynsym section out of bounds");
    }
    let strs = elf
        .section_headers
        .get(ds.sh_link as usize)
        .context(".dynsym sh_link out of range")?;
    if !in_file(strs.sh_offset, strs.sh_size) {
        bail!(".dynstr section out of bounds");
    }
    let dynsyms = sym::Symtab::parse(
        bytes,
        ds.sh_offset as usize,
        (ds.sh_size / sym_size) as usize,
        ctx,
    )
    .context(".dynsym")?;
    let dynstrtab = Strtab::parse(bytes, strs.sh_offset as usize, strs.sh_size as usize, 0)
        .context(".dynstr")?;

    let mut dynrels = RelocSection::default();
    let mut dynrelas = RelocSection::default();
    for s in &elf.section_headers {
        let is_rela = match s.sh_type {
            section_header::SHT_REL => false,
            section_header::SHT_RELA => true,
            _ => continue,
        };
        if s.sh_link as usize != dynsym_idx || !in_file(s.sh_offset, s.sh_size) {
            continue;
        }
        let r = RelocSection::parse(
            bytes,
            s.sh_offset as usize,
            s.sh_size as usize,
            is_rela,
            ctx,
        )
        .context("dynamic relocation section")?;
        if is_rela {
            dynrelas = r;
        } else {
            dynrels = r;
        }
    }
    elf.dynsyms = dynsyms;
    elf.dynstrtab = dynstrtab;
    elf.dynrels = dynrels;
    elf.dynrelas = dynrelas;
    elf.pltrelocs = RelocSection::default();
    Ok(true)
}

/// Target of an R_BPF_64_RELATIVE relocation: an lddw immediate pair if the
/// location is in code, otherwise a 64-bit value in data.
fn relative_target(bytes: &[u8], elf: &Elf, ranges: &[Range], r_offset: u64) -> Option<u64> {
    let loc = vaddr_to_file(elf, r_offset)?;
    let read_u32 = |o: usize| {
        bytes
            .get(o..o + 4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
    };
    if ranges
        .iter()
        .any(|r| loc >= r.file_start && loc < r.file_end)
    {
        let lo = read_u32(loc + 4)?;
        let hi = read_u32(loc + 12)?;
        Some((u64::from(hi) << 32) | u64::from(lo))
    } else {
        bytes
            .get(loc..loc + 8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
    }
}

/// Map a virtual address to a file offset via loadable segments, then sections.
fn vaddr_to_file(elf: &Elf, vaddr: u64) -> Option<usize> {
    for ph in &elf.program_headers {
        if ph.p_type == program_header::PT_LOAD
            && vaddr >= ph.p_vaddr
            && vaddr < ph.p_vaddr + ph.p_filesz
        {
            return Some((ph.p_offset + (vaddr - ph.p_vaddr)) as usize);
        }
    }
    for sh in &elf.section_headers {
        if sh.sh_addr != 0 && vaddr >= sh.sh_addr && vaddr < sh.sh_addr + sh.sh_size {
            return Some((sh.sh_offset + (vaddr - sh.sh_addr)) as usize);
        }
    }
    None
}

/// Executable PT_LOAD segments, falling back to SHF_EXECINSTR sections.
fn executable_ranges(elf: &Elf, file_len: usize) -> Vec<Range> {
    let make = |off: u64, size: u64, vaddr: u64| {
        let file_start = (off as usize).min(file_len);
        let file_end = (off.saturating_add(size) as usize).min(file_len);
        (file_end > file_start).then_some(Range {
            file_start,
            file_end,
            vaddr_start: vaddr,
        })
    };
    let mut ranges: Vec<Range> = elf
        .program_headers
        .iter()
        .filter(|ph| ph.p_type == program_header::PT_LOAD && ph.p_flags & program_header::PF_X != 0)
        .filter_map(|ph| make(ph.p_offset, ph.p_filesz, ph.p_vaddr))
        .collect();
    if ranges.is_empty() {
        ranges = elf
            .section_headers
            .iter()
            .filter(|sh| {
                sh.sh_flags & u64::from(section_header::SHF_EXECINSTR) != 0
                    && sh.sh_type != section_header::SHT_NOBITS
            })
            .filter_map(|sh| make(sh.sh_offset, sh.sh_size, sh.sh_addr))
            .collect();
    }
    ranges
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syscalls::hash_table;

    // Generated by tests/gen_dyn_elf.py: `r1 = 1; call sol_curve_group_op; exit`
    // with the call patched by a dynamic relocation.
    const MAPPED: &[u8] = include_bytes!("../tests/fixtures/mapped.so");
    const UNMAPPED: &[u8] = include_bytes!("../tests/fixtures/unmapped.so");

    fn curve_hit(r: &ElfReport) -> &Hit {
        &r.syscalls["sol_curve_group_op"]
    }

    #[test]
    fn dynamic_tables_in_loaded_segment() {
        let r = scan_elf(MAPPED, &hash_table()).unwrap();
        assert!(r.parse_note.is_empty());
        assert_eq!(curve_hit(&r).count, 1);
        assert_eq!(curve_hit(&r).selectors, BTreeSet::from([1]));
    }

    #[test]
    fn dynamic_tables_outside_loaded_segments_fall_back_to_sections() {
        // goblin alone fails on this file (it reads the string table from offset 0).
        assert!(Elf::parse(UNMAPPED).is_err());
        let r = scan_elf(UNMAPPED, &hash_table()).unwrap();
        assert!(r.parse_note.contains("section headers"));
        let hit = curve_hit(&r);
        assert!(hit.evidence.contains(&Evidence::Relocation));
        assert_eq!(hit.count, 1);
        assert_eq!(hit.selectors, BTreeSet::from([1]));
    }
}
