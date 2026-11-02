//! Constant propagation over the control-flow graph, within and across
//! functions, to resolve the selector argument (r1) of curve and BN254
//! syscalls.
//!
//! Each register holds one of: a small set of known constants, "the value this
//! register had on entry to the current function", or unknown. Within a
//! function, values are propagated forward to a fixpoint, merging at joins
//! (set union; anything else becomes unknown). Across functions, a parameter's
//! possible values are the union of the values passed at every direct call
//! site, iterated to a fixpoint.
//!
//! Soundness assumptions, stated rather than hidden:
//! - Functions that may be entered other than by a direct call (the entry
//!   point, exported symbols, functions whose address is taken) are roots:
//!   their parameters are unknown. If address-taken functions are missed,
//!   their selector sets may be incomplete; `indirect_calls` flags programs
//!   where that could matter.
//! - A selector is reported as known only if every path that reaches the
//!   syscall yields a constant; otherwise the site counts as unknown.

use crate::sbpf::{self, Call, Code, Instr};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Larger constant sets collapse to unknown.
pub const MAX_SET: usize = 16;

type Set = BTreeSet<i64>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Unknown,
    Consts(Set),
    /// Value of register r_i on entry to the current function.
    Entry(u8),
}

fn consts(c: i64) -> Val {
    Val::Consts(Set::from([c]))
}

fn join(a: &Val, b: &Val) -> Val {
    match (a, b) {
        (Val::Consts(x), Val::Consts(y)) => {
            let u: Set = x | y;
            if u.len() > MAX_SET {
                Val::Unknown
            } else {
                Val::Consts(u)
            }
        }
        _ if a == b => a.clone(),
        _ => Val::Unknown,
    }
}

type Regs = Vec<Val>; // r0..=r10

fn transfer(i: &Instr, s: &Regs, model_alu: bool) -> Regs {
    let mut o = s.clone();
    let d = i.dst as usize;
    let src = i.src as usize;
    let writable = d <= 9;
    match i.opc {
        sbpf::OP_LDDW if writable => o[d] = consts(i.imm64),
        sbpf::OP_MOV64_IMM if writable => o[d] = consts(i64::from(i.imm)),
        sbpf::OP_MOV32_IMM if writable => o[d] = consts(i64::from(i.imm as u32)),
        sbpf::OP_MOV64_REG if writable => o[d] = s.get(src).cloned().unwrap_or(Val::Unknown),
        sbpf::OP_MOV32_REG if writable => {
            o[d] = match s.get(src) {
                Some(Val::Consts(set)) => {
                    Val::Consts(set.iter().map(|c| i64::from(*c as u32)).collect())
                }
                _ => Val::Unknown,
            }
        }
        sbpf::OP_CALL | sbpf::OP_CALLX => o[0..=5].fill(Val::Unknown),
        sbpf::OP_EXIT | sbpf::OP_RETURN | sbpf::OP_JA => {}
        // 64-bit add/sub; the 32-bit immediate is sign-extended (sbpf interpreter: `i.imm as
        // u64` with a sign-extended imm).
        sbpf::OP_ADD64_IMM if writable && model_alu => {
            o[d] = map_consts(&s[d], |c| c.wrapping_add(i64::from(i.imm)))
        }
        sbpf::OP_SUB64_IMM if writable && model_alu => {
            o[d] = map_consts(&s[d], |c| c.wrapping_sub(i64::from(i.imm)))
        }
        sbpf::OP_ADD64_REG if writable && model_alu => {
            o[d] = add_sets(&s[d], s.get(src).unwrap_or(&Val::Unknown))
        }
        opc if sbpf::is_cond_jump(opc) || sbpf::is_store(opc) => {}
        _ if writable => o[d] = Val::Unknown,
        _ => {}
    }
    o
}

pub struct FnInfo {
    pub reached: BTreeSet<usize>,
    /// (call instruction, callee entry, r1..=r5 at the call)
    pub call_args: Vec<(usize, usize, Vec<Val>)>,
    /// (syscall instruction, r1 at the call)
    // FIXME: now duplicates calls[..][0] for syscalls and needs code cleanup
    pub syscall_r1: HashMap<usize, Val>,
    /// Register values just before selected instructions, still in terms of this function's
    /// parameters (resolved across callers in `analyze_range`).
    pub raw: RawSnapshots,
}

/// Values recorded within one function, before resolving parameters.
#[derive(Debug, Default)]
pub struct RawSnapshots {
    /// Every call: r1, r2, r3.
    pub calls: BTreeMap<usize, [Val; 3]>,
    /// Every conditional jump: its two operands (dst; src register or immediate).
    pub jumps: BTreeMap<usize, [Val; 2]>,
    /// 64-bit xor (register or immediate): its two operands.
    pub xors: BTreeMap<usize, [Val; 2]>,
    /// Every store: address (base + offset), stored value, size in bytes.
    pub stores: BTreeMap<usize, (Val, Val, u8)>,
    /// Value of every `lddw`: relocations already applied by the caller.
    pub lddws: BTreeMap<usize, i64>,
    /// Address of every load from memory: base + offset.
    pub mem_loads: BTreeMap<usize, Val>,
}

/// Values recorded within one reachable function, parameters resolved: a set
/// of constants, or None where some path gives a non-constant value.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FnSnapshots {
    pub calls: BTreeMap<usize, [Option<Set>; 3]>,
    pub jumps: BTreeMap<usize, [Option<Set>; 2]>,
    pub xors: BTreeMap<usize, [Option<Set>; 2]>,
    pub stores: BTreeMap<usize, Store>,
    /// Value of every `lddw` in the function.
    pub lddws: BTreeMap<usize, i64>,
    /// Address of every load from memory: base + offset.
    pub mem_loads: BTreeMap<usize, Option<Set>>,
    /// r1..r3 at every call before parameters are resolved, so that `Val::Entry(i)` ("this
    /// function's own i-th argument") stays visible.  Argument-forwarding wrappers are recognised
    /// from these.
    pub raw_calls: BTreeMap<usize, [Val; 3]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Store {
    pub addr: Option<Set>,
    pub value: Option<Set>,
    pub size: u8,
}

const OP_XOR64_IMM: u8 = 0xa7;
const OP_XOR64_REG: u8 = 0xaf;

/// Size in bytes of a plain load from memory (LDX, BPF_MEM mode), or None.  0x61 w, 0x69 h, 0x71 b,
/// 0x79 dw.
fn load_size(opc: u8) -> Option<u8> {
    match opc {
        0x61 => Some(4),
        0x69 => Some(2),
        0x71 => Some(1),
        0x79 => Some(8),
        _ => None,
    }
}

/// Size in bytes of a plain store (BPF_MEM mode), or None for any other opcode.  ST (immediate
/// value): 0x62 w, 0x6a h, 0x72 b, 0x7a dw; STX (register value): 0x63, 0x6b, 0x73, 0x7b. Atomic
/// and other modes are not stores here.
fn store_size(opc: u8) -> Option<u8> {
    match opc {
        0x62 | 0x63 => Some(4),
        0x6a | 0x6b => Some(2),
        0x72 | 0x73 => Some(1),
        0x7a | 0x7b => Some(8),
        _ => None,
    }
}

/// Record the values `raw` keeps for instruction `idx`, from the state `s` just before it executes.
fn record(code: &Code, calls: &HashMap<usize, Call>, idx: usize, s: &Regs, raw: &mut RawSnapshots) {
    let i = &code.instrs[idx];
    let reg = |r: u8| s.get(r as usize).cloned().unwrap_or(Val::Unknown);
    let src_operand = || {
        if i.opc & 0x08 != 0 {
            reg(i.src)
        } else {
            consts(i64::from(i.imm))
        }
    };
    if calls.contains_key(&idx) {
        raw.calls.insert(idx, [reg(1), reg(2), reg(3)]);
    } else if i.opc == sbpf::OP_LDDW && i.len == 2 {
        raw.lddws.insert(idx, i.imm64);
    } else if sbpf::is_cond_jump(i.opc) {
        raw.jumps.insert(idx, [reg(i.dst), src_operand()]);
    } else if !code.model_alu {
        // Store and xor encodings differ in V2; record nothing rather than guess.
    } else if matches!(i.opc, OP_XOR64_IMM | OP_XOR64_REG) {
        raw.xors.insert(idx, [reg(i.dst), src_operand()]);
    } else if let Some(size) = store_size(i.opc) {
        let addr = map_consts(&reg(i.dst), |b| b.wrapping_add(i64::from(i.off)));
        raw.stores.insert(idx, (addr, src_operand(), size));
    } else if load_size(i.opc).is_some() {
        raw.mem_loads.insert(
            idx,
            map_consts(&reg(i.src), |b| b.wrapping_add(i64::from(i.off))),
        );
    }
}

pub fn analyze_function(code: &Code, calls: &HashMap<usize, Call>, entry: usize) -> FnInfo {
    let mut init = vec![Val::Unknown; 11];
    for (r, v) in init.iter_mut().enumerate().take(6).skip(1) {
        *v = Val::Entry(r as u8);
    }
    let mut state: HashMap<usize, Regs> = HashMap::from([(entry, init)]);
    let mut work = vec![entry];
    let mut succ = Vec::new();
    while let Some(idx) = work.pop() {
        let out = transfer(&code.instrs[idx], &state[&idx], code.model_alu);
        sbpf::successors(code, idx, &mut succ);
        for &n in &succ {
            match state.get_mut(&n) {
                None => {
                    state.insert(n, out.clone());
                    work.push(n);
                }
                Some(cur) => {
                    let joined: Regs = cur.iter().zip(&out).map(|(a, b)| join(a, b)).collect();
                    if joined != *cur {
                        *cur = joined;
                        work.push(n);
                    }
                }
            }
        }
    }
    let mut info = FnInfo {
        reached: BTreeSet::new(),
        call_args: Vec::new(),
        syscall_r1: HashMap::new(),
        raw: Default::default(),
    };
    for (&idx, s) in &state {
        info.reached.insert(idx);
        record(code, calls, idx, s, &mut info.raw);
        match calls.get(&idx) {
            Some(Call::Syscall { .. }) => {
                info.syscall_r1.insert(idx, s[1].clone());
            }
            Some(Call::Internal(t)) => info.call_args.push((idx, *t, s[1..=5].to_vec())),
            _ => {}
        }
    }
    info
}

#[derive(Debug)]
pub struct SiteResult {
    pub idx: usize,
    pub name: String,
    pub via_reloc: bool,
    /// Reachable from a root through direct calls. False also covers code we
    /// could not attribute to any function.
    pub reachable: bool,
    /// Possible r1 values at this call site; None = unknown on some path.
    pub selectors: Option<Set>,
}

#[derive(Debug, Default)]
pub struct RangeResult {
    pub sites: Vec<SiteResult>,
    pub unresolved: BTreeMap<u32, usize>,
    pub indirect_calls: usize,
    pub functions: usize,
    /// Recorded values per reachable function (keyed by its entry instruction).
    pub snapshots: BTreeMap<usize, FnSnapshots>,
}

/// Unknown entry values are None; Some(set) is the union so far.
type EntryVals = Vec<Option<Set>>; // index = register 0..=5

fn resolve(v: &Val, ev: &EntryVals) -> Option<Set> {
    match v {
        Val::Consts(s) => Some(s.clone()),
        Val::Entry(i) => ev.get(*i as usize).cloned().flatten(),
        Val::Unknown => None,
    }
}

fn merge(a: &Option<Set>, b: &Option<Set>) -> Option<Set> {
    match (a, b) {
        (Some(x), Some(y)) => {
            let u: Set = x | y;
            (u.len() <= MAX_SET).then_some(u)
        }
        _ => None,
    }
}

pub fn analyze_range(
    code: &Code,
    calls: &HashMap<usize, Call>,
    roots: &BTreeSet<usize>,
) -> RangeResult {
    let mut entries = roots.clone();
    entries.extend(calls.values().filter_map(|c| match c {
        Call::Internal(t) => Some(*t),
        _ => None,
    }));
    let fns: BTreeMap<usize, FnInfo> = entries
        .iter()
        .map(|&e| (e, analyze_function(code, calls, e)))
        .collect();

    // Functions reachable from the roots through direct calls.
    let mut reachable_fns = BTreeSet::new();
    let mut stack: Vec<usize> = roots.iter().copied().collect();
    while let Some(f) = stack.pop() {
        if reachable_fns.insert(f) {
            stack.extend(fns[&f].call_args.iter().map(|(_, callee, _)| *callee));
        }
    }

    // Parameter values across functions, to a fixpoint. Roots stay unknown.
    let mut ev: BTreeMap<usize, EntryVals> = entries
        .iter()
        .map(|&e| {
            (
                e,
                if roots.contains(&e) {
                    vec![None; 6]
                } else {
                    vec![Some(Set::new()); 6]
                },
            )
        })
        .collect();
    loop {
        let mut updates: Vec<(usize, usize, Option<Set>)> = Vec::new();
        for (f, info) in &fns {
            for (_, callee, args) in &info.call_args {
                if roots.contains(callee) {
                    continue;
                }
                for r in 1..=5 {
                    updates.push((*callee, r, resolve(&args[r - 1], &ev[f])));
                }
            }
        }
        let mut changed = false;
        for (callee, r, contrib) in updates {
            let cur = &mut ev.get_mut(&callee).unwrap()[r];
            let new = merge(cur, &contrib);
            if new != *cur {
                *cur = new;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut out = RangeResult {
        functions: fns.len(),
        ..Default::default()
    };
    // Snapshots of reachable functions, with parameters resolved through the values their callers
    // pass. An empty set (no caller contributes) is unknown.
    let res = |v: &Val, e: &EntryVals| resolve(v, e).filter(|s| !s.is_empty());
    for f in &reachable_fns {
        let (raw, e) = (&fns[f].raw, &ev[f]);
        let snap = FnSnapshots {
            calls: raw
                .calls
                .iter()
                .map(|(&k, [a, b, c])| (k, [res(a, e), res(b, e), res(c, e)]))
                .collect(),
            jumps: raw
                .jumps
                .iter()
                .map(|(&k, [a, b])| (k, [res(a, e), res(b, e)]))
                .collect(),
            xors: raw
                .xors
                .iter()
                .map(|(&k, [a, b])| (k, [res(a, e), res(b, e)]))
                .collect(),
            stores: raw
                .stores
                .iter()
                .map(|(&k, (a, v, size))| {
                    (
                        k,
                        Store {
                            addr: res(a, e),
                            value: res(v, e),
                            size: *size,
                        },
                    )
                })
                .collect(),
            lddws: raw.lddws.clone(),
            mem_loads: raw.mem_loads.iter().map(|(&k, a)| (k, res(a, e))).collect(),
            raw_calls: raw.calls.clone(),
        };
        out.snapshots.insert(*f, snap);
    }
    for (&idx, call) in calls {
        match call {
            Call::Syscall { name, via_reloc } => {
                let mut selectors: Option<Set> = Some(Set::new());
                let (mut attributed, mut reachable) = (false, false);
                for (f, info) in &fns {
                    if let Some(v) = info.syscall_r1.get(&idx) {
                        attributed = true;
                        reachable |= reachable_fns.contains(f);
                        selectors = merge(&selectors, &resolve(v, &ev[f]));
                    }
                }
                // Unattributed code, or a parameter with no constant from any
                // caller (e.g. a cycle of functions passing it around): unknown.
                if !attributed || selectors.as_ref().is_some_and(|s| s.is_empty()) {
                    selectors = None;
                }
                out.sites.push(SiteResult {
                    idx,
                    name: name.clone(),
                    via_reloc: *via_reloc,
                    reachable,
                    selectors,
                });
            }
            Call::Unresolved(h) => *out.unresolved.entry(*h).or_default() += 1,
            Call::Indirect => out.indirect_calls += 1,
            _ => {}
        }
    }
    out.sites.sort_by_key(|s| s.idx);
    out
}

/// Apply `f` to every constant; anything but a constant set becomes unknown.
fn map_consts(v: &Val, f: impl Fn(i64) -> i64) -> Val {
    match v {
        Val::Consts(set) => Val::Consts(set.iter().map(|&c| f(c)).collect()),
        _ => Val::Unknown,
    }
}

/// All pairwise sums of two constant sets, or unknown if either is not a constant set or the result
/// would exceed `MAX_SET`.
fn add_sets(a: &Val, b: &Val) -> Val {
    match (a, b) {
        (Val::Consts(x), Val::Consts(y)) if x.len() * y.len() <= MAX_SET => Val::Consts(
            x.iter()
                .flat_map(|&p| y.iter().map(move |&q| p.wrapping_add(q)))
                .collect(),
        ),
        _ => Val::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sbpf::{Code, classify_calls};
    use crate::syscalls::{hash_table, syscall_hash};

    const CURVE: &str = "sol_curve_group_op";

    fn instr(opc: u8, dst: u8, src: u8, off: i16, imm: i32) -> [u8; 8] {
        let mut b = [0u8; 8];
        b[0] = opc;
        b[1] = (src << 4) | (dst & 0x0f);
        b[2..4].copy_from_slice(&off.to_le_bytes());
        b[4..8].copy_from_slice(&imm.to_le_bytes());
        b
    }
    fn mov(dst: u8, imm: i32) -> [u8; 8] {
        instr(sbpf::OP_MOV64_IMM, dst, 0, 0, imm)
    }
    fn syscall(name: &str) -> [u8; 8] {
        instr(sbpf::OP_CALL, 0, 0, 0, syscall_hash(name) as i32)
    }
    /// Internal call (src = 1) from `slot` to `target`.
    fn call_to(slot: usize, target: usize) -> [u8; 8] {
        instr(sbpf::OP_CALL, 0, 1, 0, target as i32 - slot as i32 - 1)
    }
    fn exit() -> [u8; 8] {
        instr(sbpf::OP_EXIT, 0, 0, 0, 0)
    }

    fn run(prog: &[[u8; 8]], root_slots: &[usize]) -> RangeResult {
        let text: Vec<u8> = prog.concat();
        let mut code = Code::decode(&text, 0, 0);
        code.model_alu = true;
        let calls = classify_calls(&code, &HashMap::new(), &hash_table());
        let roots = root_slots
            .iter()
            .map(|s| code.idx_at_slot(*s as i64).unwrap())
            .collect();
        analyze_range(&code, &calls, &roots)
    }

    fn selectors_of(r: &RangeResult) -> Vec<Option<Vec<i64>>> {
        r.sites
            .iter()
            .filter(|s| s.name == CURVE)
            .map(|s| s.selectors.as_ref().map(|x| x.iter().copied().collect()))
            .collect()
    }

    #[test]
    fn straight_line_constant() {
        let r = run(&[mov(1, 1), mov(2, 7), syscall(CURVE), exit()], &[0]);
        assert_eq!(selectors_of(&r), vec![Some(vec![1])]);
        assert!(r.sites.iter().all(|s| s.reachable));
    }

    #[test]
    fn branch_merges_both_constants() {
        // 0: if r2 == 0 goto 3; 1: r1 = 1; 2: goto 4; 3: r1 = 0; 4: call curve
        // The last mov in file order is r1 = 0; the old linear sweep reported
        // only {0}. Both paths must be reported.
        let prog = [
            instr(0x15, 2, 0, 2, 0), // jeq r2, 0: target 0 + 1 + 2 = 3
            mov(1, 1),
            instr(sbpf::OP_JA, 0, 0, 1, 0), // target 2 + 1 + 1 = 4
            mov(1, 0),
            syscall(CURVE),
            exit(),
        ];
        let r = run(&prog, &[0]);
        assert_eq!(selectors_of(&r), vec![Some(vec![0, 1])]);
    }

    #[test]
    fn value_from_unknown_source_is_unknown() {
        // r1 loaded from memory (ldxdw r1, [r2+0]) -> unknown, not the earlier mov
        let prog = [mov(1, 1), instr(0x79, 1, 2, 0, 0), syscall(CURVE), exit()];
        let r = run(&prog, &[0]);
        assert_eq!(selectors_of(&r), vec![None]);
    }

    #[test]
    fn selector_through_non_inlined_wrapper() {
        // root: r1 = 1; call W; r1 = 0; call W; exit
        // W (slot 5): call curve(r1); exit
        let prog = [
            mov(1, 1),
            call_to(1, 5),
            mov(1, 0),
            call_to(3, 5),
            exit(),
            syscall(CURVE),
            exit(),
        ];
        let r = run(&prog, &[0]);
        assert_eq!(selectors_of(&r), vec![Some(vec![0, 1])]);
        assert!(r.sites[0].reachable);
    }

    #[test]
    fn wrapper_that_is_also_a_root_is_unknown() {
        // Same as above, but W is exported (a root): external callers may pass anything.
        let prog = [
            mov(1, 1),
            call_to(1, 5),
            mov(1, 0),
            call_to(3, 5),
            exit(),
            syscall(CURVE),
            exit(),
        ];
        let r = run(&prog, &[0, 5]);
        assert_eq!(selectors_of(&r), vec![None]);
    }

    #[test]
    fn calls_clobber_argument_registers() {
        // r1 = 1; call sol_log_ (clobbers r1); call curve -> unknown
        let prog = [mov(1, 1), syscall("sol_log_"), syscall(CURVE), exit()];
        let r = run(&prog, &[0]);
        assert_eq!(selectors_of(&r), vec![None]);
    }

    #[test]
    fn unreachable_site_is_flagged() {
        // root exits immediately; the curve call after it is never reached
        let prog = [mov(0, 0), exit(), mov(1, 1), syscall(CURVE), exit()];
        let r = run(&prog, &[0]);
        let site = r.sites.iter().find(|s| s.name == CURVE).unwrap();
        assert!(!site.reachable);
        assert_eq!(site.selectors, None);
    }

    #[test]
    fn lddw_is_two_slots_and_jump_targets_count_them() {
        // slots 0-1: lddw r3, X; 2: if r2 == 0 goto 4; 3: r1 = 1; 4: r1 = 2; 5: call curve
        let mut lddw = Vec::new();
        lddw.extend_from_slice(&instr(sbpf::OP_LDDW, 3, 0, 0, 5));
        lddw.extend_from_slice(&[0u8; 8]);
        let mut text = lddw;
        for i in [
            instr(0x15, 2, 0, 1, 0),
            mov(1, 1),
            mov(1, 2),
            syscall(CURVE),
            exit(),
        ] {
            text.extend_from_slice(&i);
        }
        let code = Code::decode(&text, 0, 0);
        assert_eq!(code.instrs.len(), 6);
        let calls = classify_calls(&code, &HashMap::new(), &hash_table());
        let r = analyze_range(&code, &calls, &BTreeSet::from([0]));
        // jump from slot 2 skips slot 3 and lands on slot 4 (r1 = 2): both paths give 2
        assert_eq!(selectors_of(&r), vec![Some(vec![2])]);
    }

    #[test]
    fn unknown_hash_and_indirect_calls_are_counted() {
        let prog = [
            instr(
                sbpf::OP_CALL,
                0,
                0,
                0,
                syscall_hash("sol_future_syscall") as i32,
            ),
            instr(sbpf::OP_CALLX, 0, 2, 0, 0),
            exit(),
        ];
        let r = run(&prog, &[0]);
        assert_eq!(r.unresolved.len(), 1);
        assert_eq!(r.indirect_calls, 1);
    }

    /// `lddw dst, v` as its two slots.
    fn lddw(dst: u8, v: i64) -> [[u8; 8]; 2] {
        let mut hi = [0u8; 8];
        hi[4..8].copy_from_slice(&((v >> 32) as i32).to_le_bytes());
        [instr(sbpf::OP_LDDW, dst, 0, 0, v as i32), hi]
    }

    /// r1 at a curve call appended after `prog`, with add/sub modelled or not.
    fn r1_with(prog: &[[u8; 8]], model_alu: bool) -> Option<Vec<i64>> {
        let mut text: Vec<u8> = prog.concat();
        text.extend_from_slice(&syscall(CURVE));
        text.extend_from_slice(&exit());
        let mut code = Code::decode(&text, 0, 0);
        code.model_alu = model_alu;
        let calls = classify_calls(&code, &HashMap::new(), &hash_table());
        let r = analyze_range(&code, &calls, &BTreeSet::from([0]));
        r.sites[0]
            .selectors
            .as_ref()
            .map(|s| s.iter().copied().collect())
    }

    /// A typical synthetic address (section 4, offset 0x100): above 32 bits.
    const X: i64 = 0x4_0000_0100;

    #[test]
    fn add_immediate_to_constant() {
        let [a, b] = lddw(1, X);
        let prog = [a, b, instr(sbpf::OP_ADD64_IMM, 1, 0, 0, 0x20)];
        assert_eq!(r1_with(&prog, true), Some(vec![X + 0x20]));
    }

    #[test]
    fn add_immediate_is_sign_extended() {
        let [a, b] = lddw(1, X);
        let prog = [a, b, instr(sbpf::OP_ADD64_IMM, 1, 0, 0, -8)];
        assert_eq!(r1_with(&prog, true), Some(vec![X - 8]));
    }

    #[test]
    fn sub_immediate_only_where_modelled() {
        let [a, b] = lddw(1, X);
        let prog = [a, b, instr(sbpf::OP_SUB64_IMM, 1, 0, 0, 8)];
        assert_eq!(r1_with(&prog, true), Some(vec![X - 8]));
        assert_eq!(r1_with(&prog, false), None);
    }

    #[test]
    fn add_register_gives_pairwise_sums() {
        // r3 is 0 or 32 depending on a branch; then r1 = X + r3.
        let [a, b] = lddw(1, X);
        let prog = [
            a, // slots 0-1: lddw r1, X
            b,
            instr(0x15, 2, 0, 2, 0),        // slot 2: if r2 == 0 goto 5
            mov(3, 32),                     // slot 3
            instr(sbpf::OP_JA, 0, 0, 1, 0), // slot 4: goto 6
            mov(3, 0),                      // slot 5
            instr(sbpf::OP_ADD64_REG, 1, 3, 0, 0), // slot 6: r1 += r3
        ];
        assert_eq!(r1_with(&prog, true), Some(vec![X, X + 32]));
    }

    #[test]
    fn add_to_parameter_is_unknown() {
        // r1 on entry is a parameter of the root function (Entry(1)), not a constant.
        let prog = [instr(sbpf::OP_ADD64_IMM, 1, 0, 0, 0x20)];
        assert_eq!(r1_with(&prog, true), None);
    }

    #[test]
    fn sbpf_versions_with_v0_alu_semantics() {
        for v in [0, 1, 3, 4] {
            assert!(sbpf::models_alu(v), "e_flags {v}");
        }
        for v in [2, 5, 0x20] {
            assert!(!sbpf::models_alu(v), "e_flags {v}");
        }
    }

    const MEMCMP: &str = "sol_memcmp_";

    /// Analyse `prog` with roots at `root_slots`.
    fn snaps(prog: &[[u8; 8]], root_slots: &[usize], model_alu: bool) -> (Code, RangeResult) {
        let text: Vec<u8> = prog.concat();
        let mut code = Code::decode(&text, 0, 0);
        code.model_alu = model_alu;
        let calls = classify_calls(&code, &HashMap::new(), &hash_table());
        let roots = root_slots
            .iter()
            .map(|s| code.idx_at_slot(*s as i64).unwrap())
            .collect();
        let r = analyze_range(&code, &calls, &roots);
        (code, r)
    }

    fn set(v: &[i64]) -> Option<Set> {
        Some(v.iter().copied().collect())
    }

    fn at_slot(code: &Code, slot: usize) -> usize {
        code.idx_at_slot(slot as i64).unwrap()
    }

    #[test]
    fn call_records_r1_to_r3() {
        let [a, b] = lddw(2, X);
        // slots 0-1: lddw r2, X; 2: r3 = 32; 3: call sol_memcmp_; 4: exit
        let prog = [a, b, mov(3, 32), syscall(MEMCMP), exit()];
        let (code, r) = snaps(&prog, &[0], true);
        let calls = &r.snapshots[&0].calls;
        // r1 is a parameter of the exported root, so unknown.
        assert_eq!(calls[&at_slot(&code, 3)], [None, set(&[X]), set(&[32])]);
    }

    #[test]
    fn parameter_resolved_through_caller() {
        // root: lddw r1, X; call W; exit.  W (slot 4): r3 = 32; call sol_memcmp_; exit
        let [a, b] = lddw(1, X);
        let prog = [
            a,
            b,
            call_to(2, 4),
            exit(),
            mov(3, 32),
            syscall(MEMCMP),
            exit(),
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let w = &r.snapshots[&at_slot(&code, 4)];
        assert_eq!(w.calls[&at_slot(&code, 5)][0], set(&[X]));
    }

    #[test]
    fn conditional_jump_operands_immediate_and_register() {
        let [a, b] = lddw(2, X);
        // 0: if r1 == 7 goto 1; 1-2: lddw r2, X; 3: if r1 != r2 goto 4; 4: exit
        let prog = [
            instr(0x15, 1, 0, 0, 7),
            a,
            b,
            instr(0x5d, 1, 2, 0, 0),
            exit(),
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let jumps = &r.snapshots[&0].jumps;
        assert_eq!(jumps[&at_slot(&code, 0)], [None, set(&[7])]);
        assert_eq!(jumps[&at_slot(&code, 3)], [None, set(&[X])]);
    }

    #[test]
    fn xor_operands() {
        let [a, b] = lddw(2, X);
        // 0-1: lddw r2, X; 2: r1 ^= r2; 3: exit
        let prog = [a, b, instr(OP_XOR64_REG, 1, 2, 0, 0), exit()];
        let (code, r) = snaps(&prog, &[0], true);
        assert_eq!(r.snapshots[&0].xors[&at_slot(&code, 2)], [None, set(&[X])]);
    }

    #[test]
    fn stores_record_address_value_and_size() {
        let [a, b] = lddw(1, X);
        // 0-1: lddw r1, X; 2: r2 = 5; 3: *(u64 *)(r1 + 8) = r2; 4: *(u32 *)(r1 + 0) = 9; 5: exit
        let prog = [
            a,
            b,
            mov(2, 5),
            instr(0x7b, 1, 2, 8, 0),
            instr(0x62, 1, 0, 0, 9),
            exit(),
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let stores = &r.snapshots[&0].stores;
        assert_eq!(
            stores[&at_slot(&code, 3)],
            Store {
                addr: set(&[X + 8]),
                value: set(&[5]),
                size: 8
            }
        );
        assert_eq!(
            stores[&at_slot(&code, 4)],
            Store {
                addr: set(&[X]),
                value: set(&[9]),
                size: 4
            }
        );
    }

    #[test]
    fn stores_and_xors_not_recorded_where_encodings_differ() {
        let [a, b] = lddw(1, X);
        let prog = [
            a,
            b,
            instr(0x7b, 1, 2, 8, 0),
            instr(OP_XOR64_REG, 1, 2, 0, 0),
            instr(0x15, 1, 0, 0, 7),
            exit(),
        ];
        let (_, r) = snaps(&prog, &[0], false);
        let s = &r.snapshots[&0];
        assert!(s.stores.is_empty() && s.xors.is_empty());
        assert_eq!(s.jumps.len(), 1, "jumps are still recorded");
    }

    #[test]
    fn unreachable_function_has_no_snapshots() {
        // root exits at once; slots 2-4 are never reached
        let prog = [mov(0, 0), exit(), mov(3, 32), syscall(MEMCMP), exit()];
        let (_, r) = snaps(&prog, &[0], true);
        assert_eq!(r.snapshots.keys().copied().collect::<Vec<_>>(), vec![0]);
        assert!(r.snapshots[&0].calls.is_empty());
    }

    // --- lddw values, load addresses, unresolved call arguments ---

    #[test]
    fn lddw_values_and_load_addresses() {
        let [a, b] = lddw(1, X);
        // 0-1: lddw r1, X; 2: r1 += 0x20; 3: r2 = *(u64 *)(r1 + 8); 4: exit
        let prog = [
            a,
            b,
            instr(sbpf::OP_ADD64_IMM, 1, 0, 0, 0x20),
            instr(0x79, 2, 1, 8, 0),
            exit(),
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let s = &r.snapshots[&0];
        assert_eq!(s.lddws, BTreeMap::from([(at_slot(&code, 0), X)]));
        assert_eq!(s.mem_loads[&at_slot(&code, 3)], set(&[X + 0x28]));
    }

    #[test]
    fn raw_call_arguments_keep_entry_values() {
        // W (slot 4) forwards its own r1..r3 to sol_memcmp_ after saving r2 in r8
        // and putting it back, as the toolchain's memcmp does.
        // root: lddw r2, X; r3 = 32; call W; exit
        let [a, b] = lddw(2, X);
        let prog = [
            a,
            b,                                     // slots 0-1
            mov(3, 32),                            // 2
            call_to(3, 5),                         // 3
            exit(),                                // 4
            instr(sbpf::OP_MOV64_REG, 8, 2, 0, 0), // 5: r8 = r2
            mov(2, 0),                             // 6: r2 clobbered
            instr(sbpf::OP_MOV64_REG, 2, 8, 0, 0), // 7: r2 = r8
            syscall(MEMCMP),                       // 8
            exit(),                                // 9
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let w = &r.snapshots[&at_slot(&code, 5)];
        assert_eq!(
            w.raw_calls[&at_slot(&code, 8)],
            [Val::Entry(1), Val::Entry(2), Val::Entry(3)]
        );
        // Resolved through the caller, r2 and r3 are the constants it passed.
        assert_eq!(w.calls[&at_slot(&code, 8)][1..], [set(&[X]), set(&[32])]);
        // The caller's own call to W carries the values the rules read.
        let root = &r.snapshots[&0];
        assert_eq!(root.calls[&at_slot(&code, 3)][1..], [set(&[X]), set(&[32])]);
    }

    #[test]
    fn rearranged_argument_is_not_an_entry_value() {
        // W changes r2 before the syscall: r2 = r2 + 8. No longer Entry(2).
        let prog = [
            call_to(0, 2),                         // 0: call W
            exit(),                                // 1
            instr(sbpf::OP_ADD64_IMM, 2, 0, 0, 8), // 2: r2 += 8
            syscall(MEMCMP),                       // 3
            exit(),                                // 4
        ];
        let (code, r) = snaps(&prog, &[0], true);
        let w = &r.snapshots[&at_slot(&code, 2)];
        assert_eq!(
            w.raw_calls[&at_slot(&code, 3)],
            [Val::Entry(1), Val::Unknown, Val::Entry(3)]
        );
    }
}
