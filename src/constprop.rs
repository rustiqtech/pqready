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

fn transfer(i: &Instr, s: &Regs) -> Regs {
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
    pub syscall_r1: HashMap<usize, Val>,
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
        let out = transfer(&code.insns[idx], &state[&idx]);
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
    };
    for (&idx, s) in &state {
        info.reached.insert(idx);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sbpf::{Code, classify_calls};
    use crate::syscalls::{hash_table, syscall_hash};

    const CURVE: &str = "sol_curve_group_op";

    fn insn(opc: u8, dst: u8, src: u8, off: i16, imm: i32) -> [u8; 8] {
        let mut b = [0u8; 8];
        b[0] = opc;
        b[1] = (src << 4) | (dst & 0x0f);
        b[2..4].copy_from_slice(&off.to_le_bytes());
        b[4..8].copy_from_slice(&imm.to_le_bytes());
        b
    }
    fn mov(dst: u8, imm: i32) -> [u8; 8] {
        insn(sbpf::OP_MOV64_IMM, dst, 0, 0, imm)
    }
    fn syscall(name: &str) -> [u8; 8] {
        insn(sbpf::OP_CALL, 0, 0, 0, syscall_hash(name) as i32)
    }
    /// Internal call (src = 1) from `slot` to `target`.
    fn call_to(slot: usize, target: usize) -> [u8; 8] {
        insn(sbpf::OP_CALL, 0, 1, 0, target as i32 - slot as i32 - 1)
    }
    fn exit() -> [u8; 8] {
        insn(sbpf::OP_EXIT, 0, 0, 0, 0)
    }

    fn run(prog: &[[u8; 8]], root_slots: &[usize]) -> RangeResult {
        let text: Vec<u8> = prog.concat();
        let code = Code::decode(&text, 0, 0);
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
            insn(0x15, 2, 0, 2, 0), // jeq r2, 0: target 0 + 1 + 2 = 3
            mov(1, 1),
            insn(sbpf::OP_JA, 0, 0, 1, 0), // target 2 + 1 + 1 = 4
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
        let prog = [mov(1, 1), insn(0x79, 1, 2, 0, 0), syscall(CURVE), exit()];
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
        lddw.extend_from_slice(&insn(sbpf::OP_LDDW, 3, 0, 0, 5));
        lddw.extend_from_slice(&[0u8; 8]);
        let mut text = lddw;
        for i in [
            insn(0x15, 2, 0, 1, 0),
            mov(1, 1),
            mov(1, 2),
            syscall(CURVE),
            exit(),
        ] {
            text.extend_from_slice(&i);
        }
        let code = Code::decode(&text, 0, 0);
        assert_eq!(code.insns.len(), 6);
        let calls = classify_calls(&code, &HashMap::new(), &hash_table());
        let r = analyze_range(&code, &calls, &BTreeSet::from([0]));
        // jump from slot 2 skips slot 3 and lands on slot 4 (r1 = 2): both paths give 2
        assert_eq!(selectors_of(&r), vec![Some(vec![2])]);
    }

    #[test]
    fn unknown_hash_and_indirect_calls_are_counted() {
        let prog = [
            insn(
                sbpf::OP_CALL,
                0,
                0,
                0,
                syscall_hash("sol_future_syscall") as i32,
            ),
            insn(sbpf::OP_CALLX, 0, 2, 0, 0),
            exit(),
        ];
        let r = run(&prog, &[0]);
        assert_eq!(r.unresolved.len(), 1);
        assert_eq!(r.indirect_calls, 1);
    }
}
