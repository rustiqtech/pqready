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
use crate::precompile::{self, DataRegion, LocatedId, RefBytes};
use crate::sbpf::{Code, OP_LDDW, RelocCall, classify_calls, models_alu};
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
    pub located_ids: Vec<LocatedId>,
    /// Recorded register values per executable range, for tests only: the rules that use them run
    /// inside `scan_elf`.
    #[cfg(test)]
    pub snapshots: Vec<std::collections::BTreeMap<usize, crate::constprop::FnSnapshots>>,
}

struct Range {
    file_start: usize,
    file_end: usize,
    vaddr_start: u64,
}

pub fn scan_elf(
    bytes: &[u8],
    table: &HashMap<u32, &'static Syscall>,
    rbs: &[RefBytes],
) -> Result<ElfReport> {
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
    let regions = data_regions(&elf, bytes);
    report.located_ids = precompile::locate_ids(&regions, bytes, &rbs);
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

    // Section relocations (relocatable objects only: in linked programs these sections include
    // .rel.dyn, already handled above with the right symbols).
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

    let lddw_values = lddw_relocation_values(&elf, bytes, &ranges);

    // Decode each executable range and apply relocated `lddw` values.
    let codes: Vec<Code> = ranges
        .iter()
        .map(|r| {
            let mut code = Code::decode(
                &bytes[r.file_start..r.file_end],
                r.file_start,
                r.vaddr_start,
            );
            code.model_alu = models_alu(elf.header.e_flags);
            let base = code.file_base;
            for i in code
                .instrs
                .iter_mut()
                .filter(|i| i.opc == OP_LDDW && i.len == 2)
            {
                if let Some(&v) = lddw_values.get(&(base + i.slot * 8)) {
                    i.imm64 = v;
                }
            }
            code
        })
        .collect();

    // Addresses loaded by `lddw` that may point at functions (function pointers), gathered across
    // all ranges: a pointer loaded in one section may target another. In a relocatable object only
    // relocated values are addresses; other immediates are plain numbers and could collide with
    // synthetic section addresses.
    let lddw_targets: BTreeSet<u64> = if is_rel {
        lddw_values.values().map(|&v| v as u64).collect()
    } else {
        codes
            .iter()
            .flat_map(|c| {
                c.instrs
                    .iter()
                    .filter(|i| i.opc == OP_LDDW)
                    .map(|i| i.imm64 as u64)
            })
            .collect()
    };

    // Analyse each range.
    for code in &codes {
        let calls = classify_calls(code, &reloc_calls, table);

        let mut roots: BTreeSet<usize> = BTreeSet::new();
        for v in root_vaddrs.iter().chain(&taken_vaddrs) {
            roots.extend(code.idx_at_vaddr(*v));
        }
        for f in root_files.iter().chain(&taken_files) {
            roots.extend(code.idx_at_file(*f));
        }
        // Functions whose address is loaded by an `lddw` (function pointers).
        for v in &lddw_targets {
            roots.extend(code.idx_at_vaddr(*v));
        }
        let roots_found = !roots.is_empty();
        if !roots_found && !code.instrs.is_empty() {
            roots.insert(0); // analyse from the start; reachability not reported
        }
        report.roots_found |= roots_found;

        let res = analyze_range(code, &calls, &roots);
        #[cfg(test)]
        report.snapshots.push(res.snapshots.clone());

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

/// Target of an R_BPF_64_RELATIVE relocation, read as the loader reads it: the lddw immediate pair
/// if the location is in code, otherwise the 32-bit value at r_offset + 4 in data.
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
        // In data the loader reads only the 32-bit value at r_offset + 4 (kept for compatibility
        // with toolchains that stored the address there) and writes back a 64-bit address: sbpf
        // elf.rs, R_BPF_64_RELATIVE.
        read_u32(loc + 4).map(u64::from)
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

fn make_range(file_len: usize, off: u64, size: u64, vaddr: u64) -> Option<Range> {
    let file_start = (off as usize).min(file_len);
    let file_end = (off.saturating_add(size) as usize).min(file_len);
    (file_end > file_start).then_some(Range {
        file_start,
        file_end,
        vaddr_start: vaddr,
    })
}

/// Code to decode: executable sections when the file has section headers, otherwise executable
/// PT_LOAD segments. Sections come first because an executable segment may also hold read-only data
/// or headers, which would be decoded as spurious instructions.
fn executable_ranges(elf: &Elf, file_len: usize) -> Vec<Range> {
    let make = |off: u64, size: u64, vaddr: u64| make_range(file_len, off, size, vaddr);
    if !elf.section_headers.is_empty() {
        elf.section_headers
            .iter()
            .enumerate()
            .filter(|(_, sh)| {
                sh.sh_flags & u64::from(section_header::SHF_EXECINSTR) != 0
                    && sh.sh_type != section_header::SHT_NOBITS
            })
            .filter_map(|(i, sh)| make(sh.sh_offset, sh.sh_size, section_address(elf, i)?))
            .collect()
    } else {
        elf.program_headers
            .iter()
            .filter(|ph| {
                ph.p_type == program_header::PT_LOAD && ph.p_flags & program_header::PF_X != 0
            })
            .filter_map(|ph| make(ph.p_offset, ph.p_filesz, ph.p_vaddr))
            .collect()
    }
}

/// Address of section `index` as the analysis sees it: `sh_addr` in a linked program. In a
/// relocatable object, where every `sh_addr` is 0, a synthetic base of `index << 32` so that
/// sections do not overlap. `None` for the null section, reserved indexes SHN_ABS, SHN_COMMON, ...
/// and out-of-range indexes.
fn section_address(elf: &Elf, index: usize) -> Option<u64> {
    let sh = elf.section_headers.get(index).filter(|_| index != 0)?;
    if elf.header.e_type == header::ET_REL {
        Some((index as u64) << 32)
    } else {
        Some(sh.sh_addr)
    }
}

fn data_regions<'a>(elf: &Elf, bytes: &'a [u8]) -> Vec<DataRegion<'a>> {
    let make = |off: u64, size: u64, vaddr: u64| make_range(bytes.len(), off, size, vaddr);
    let reg = |r: Range| DataRegion {
        bytes: &bytes[r.file_start..r.file_end],
        address: r.vaddr_start,
    };

    let regs: Vec<DataRegion> = if !elf.section_headers.is_empty() {
        elf.section_headers
            .iter()
            .enumerate()
            .filter(|(_, sh)| {
                sh.sh_flags & u64::from(section_header::SHF_ALLOC) != 0
                    && sh.sh_flags & u64::from(section_header::SHF_EXECINSTR) == 0
                    && sh.sh_type != section_header::SHT_NOBITS
            })
            .filter_map(|(i, sh)| make(sh.sh_offset, sh.sh_size, section_address(elf, i)?))
            .map(reg)
            .collect()
    } else {
        elf.program_headers
            .iter()
            .filter(|ph| {
                ph.p_type == program_header::PT_LOAD && ph.p_flags & program_header::PF_X == 0
            })
            .filter_map(|ph| make(ph.p_offset, ph.p_filesz, ph.p_vaddr))
            .map(reg)
            .collect()
    };
    regs
}

/// `lddw` instructions patched by an R_BPF_64_64 relocation, mapped from the file offset of the
/// `lddw` to the value it holds once relocated. Without this, such an `lddw` would be read as its
/// placeholder immediate.
///
/// The value follows the loader (sbpf crate `elf.rs`, relocation pass): symbol value plus the
/// implicit addend in the low 32-bit immediate; the high immediate is ignored. The region base the
/// loader adds at run time is left out, so values are ELF addresses, comparable with
/// `section_address` and `DataRegion` addresses. Relocations against undefined or absolute symbols
/// are skipped, so their `lddw` stays unresolved rather than guessed.
fn lddw_relocation_values(elf: &Elf, bytes: &[u8], ranges: &[Range]) -> HashMap<usize, i64> {
    let in_code = |off: usize| {
        ranges
            .iter()
            .any(|r| off >= r.file_start && off < r.file_end)
    };
    let imm_low = |site: usize| {
        bytes
            .get(site + 4..site + 8)
            .map(|b| u64::from(u32::from_le_bytes(b.try_into().unwrap())))
    };
    let mut values = HashMap::new();

    // Linked programs: dynamic relocations against .dynsym.
    for reloc in elf.dynrels.iter().chain(elf.dynrelas.iter()) {
        if reloc.r_type != R_BPF_64_64 || reloc.r_sym == 0 {
            continue;
        }
        let Some(sym) = elf.dynsyms.get(reloc.r_sym).filter(|s| s.st_shndx != 0) else {
            continue;
        };
        let Some(site) = vaddr_to_file(elf, reloc.r_offset).filter(|&s| in_code(s)) else {
            continue;
        };
        let Some(addend) = reloc.r_addend.map(|a| a as u64).or_else(|| imm_low(site)) else {
            continue;
        };
        values.insert(site, sym.st_value.wrapping_add(addend) as i64);
    }

    // Relocatable objects: section relocations against .symtab.
    if elf.header.e_type == header::ET_REL {
        for (reloc_sec, relocs) in &elf.shdr_relocs {
            let Some(target) = elf
                .section_headers
                .get(*reloc_sec)
                .and_then(|rs| elf.section_headers.get(rs.sh_info as usize))
            else {
                continue;
            };
            for reloc in relocs.iter() {
                if reloc.r_type != R_BPF_64_64 || reloc.r_sym == 0 {
                    continue;
                }
                let Some(sym) = elf.syms.get(reloc.r_sym) else {
                    continue;
                };
                let Some(base) = section_address(elf, sym.st_shndx) else {
                    continue;
                };
                let site = target.sh_offset as usize + reloc.r_offset as usize;
                if !in_code(site) {
                    continue;
                }
                let Some(addend) = reloc.r_addend.map(|a| a as u64).or_else(|| imm_low(site))
                else {
                    continue;
                };
                values.insert(
                    site,
                    base.wrapping_add(sym.st_value).wrapping_add(addend) as i64,
                );
            }
        }
    }
    values
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
        let r = scan_elf(MAPPED, &hash_table(), &[]).unwrap();
        assert!(r.parse_note.is_empty());
        assert_eq!(curve_hit(&r).count, 1);
        assert_eq!(curve_hit(&r).selectors, BTreeSet::from([1]));
    }

    #[test]
    fn dynamic_tables_outside_loaded_segments_fall_back_to_sections() {
        // goblin alone fails on this file (it reads the string table from offset 0).
        assert!(Elf::parse(UNMAPPED).is_err());
        let r = scan_elf(UNMAPPED, &hash_table(), &[]).unwrap();
        assert!(r.parse_note.contains("section headers"));
        let hit = curve_hit(&r);
        assert!(hit.evidence.contains(&Evidence::Relocation));
        assert_eq!(hit.count, 1);
        assert_eq!(hit.selectors, BTreeSet::from([1]));
    }

    fn values(bytes: &[u8]) -> HashMap<usize, i64> {
        let elf = Elf::parse(bytes).unwrap();
        lddw_relocation_values(&elf, bytes, &executable_ranges(&elf, bytes.len()))
    }

    #[test]
    fn object_file_lddw_against_rodata_section_symbol() {
        // tests/fixtures/memcmp_call.c, built with
        // clang --target=bpf -O2 -fPIC -fno-builtin -c:
        // `r2 = 0 ll` + R_BPF_64_64 .rodata at .text offset 0.
        // .text is at file offset 0x40; .rodata is section 4 with ED25519_ID at 0.
        let bytes = include_bytes!("../tests/fixtures/memcmp_call.o");
        assert_eq!(values(bytes), HashMap::from([(0x40, 4i64 << 32)]));
    }

    #[test]
    fn linked_program_lddw_uses_symbol_plus_low_immediate() {
        // tests/gen_dyn_elf.py lddw64.so: ID.st_value = 0x2000, imm_lo = 0x10,
        // imm_hi = 0x77 (ignored by the loader), lddw at .text start.
        let bytes = include_bytes!("../tests/fixtures/lddw64.so");
        let elf = Elf::parse(bytes).unwrap();
        let text = elf.section_headers[1].sh_offset as usize;
        assert_eq!(values(bytes), HashMap::from([(text, 0x2010)]));
    }

    #[test]
    fn no_relocated_lddw_gives_empty_map() {
        assert!(values(include_bytes!("../tests/fixtures/mapped.so")).is_empty());
    }

    fn curve_site(bytes: &[u8]) -> (usize, usize, BTreeSet<i64>) {
        let r = scan_elf(bytes, &hash_table(), &[]).unwrap();
        let h = &r.syscalls["sol_curve_group_op"];
        (
            h.unreachable_sites,
            h.unknown_selector_sites,
            h.selectors.clone(),
        )
    }

    #[test]
    fn object_file_function_pointer_via_lddw_is_a_root() {
        // tests/fixtures/fnptr.c (clang --target=bpf -O2 -fPIC -c): `on_curve` is
        // static and called only through a pointer loaded by
        // `r3 = 0x30 ll` + R_BPF_64_64 .text.
        let bytes = include_bytes!("../tests/fixtures/fnptr.o");
        assert_eq!(curve_site(bytes), (0, 0, BTreeSet::from([1])));
    }

    #[test]
    fn function_pointer_in_data_is_read_as_the_loader_reads_it() {
        // tests/gen_dyn_elf.py reldata.so: R_BPF_64_RELATIVE in .data.rel.ro,
        // address in the 32 bits at r_offset + 4. Reading 64 bits at r_offset
        // instead gives address << 32 and the handler looks unreachable.
        let bytes = include_bytes!("../tests/fixtures/reldata.so");
        assert_eq!(curve_site(bytes), (0, 0, BTreeSet::from([1])));
    }

    #[cfg(test)]
    mod snapshot_tests {
        use super::*;
        use crate::syscalls::hash_table;

        fn ed25519() -> [u8; 32] {
            bs58::decode("Ed25519SigVerify111111111111111111111111111")
                .into_vec()
                .unwrap()
                .try_into()
                .unwrap()
        }

        #[test]
        fn memcmp_call_receives_the_id_address_and_length() {
            // tests/fixtures/memcmp_call.c with -fno-builtin: memcmp(key, ED25519_ID, 32).
            // ED25519_ID is at offset 0 of .rodata, section 4: address 4 << 32.
            let bytes = include_bytes!("../tests/fixtures/memcmp_call.o");
            let r = scan_elf(bytes, &hash_table(), &[]).unwrap();
            let found = r
                .snapshots
                .iter()
                .flat_map(|m| m.values())
                .flat_map(|f| f.calls.values())
                .any(|regs| {
                    regs[1] == Some(BTreeSet::from([4i64 << 32]))
                        && regs[2] == Some(BTreeSet::from([32]))
                });
            assert!(found, "{:#?}", r.snapshots);
        }

        #[test]
        fn inlined_memcmp_compares_all_four_chunks_in_one_function() {
            // Same source without -fno-builtin: clang inlines memcmp into four
            // 64-bit comparisons against lddw constants.
            let bytes = include_bytes!("../tests/fixtures/memcmp_inline.o");
            let r = scan_elf(bytes, &hash_table(), &[]).unwrap();
            let id = ed25519();
            let chunks: Vec<i64> = (0..4)
                .map(|k| i64::from_le_bytes(id[8 * k..8 * k + 8].try_into().unwrap()))
                .collect();
            let one_function_has_all = r.snapshots.iter().flat_map(|m| m.values()).any(|f| {
                let operands: BTreeSet<i64> = f
                    .jumps
                    .values()
                    .chain(f.xors.values())
                    .flatten()
                    .flatten()
                    .flatten()
                    .copied()
                    .collect();
                chunks.iter().all(|c| operands.contains(c))
            });
            assert!(
                one_function_has_all,
                "chunks {chunks:x?}\n{:#?}",
                r.snapshots
            );
        }
    }
}
