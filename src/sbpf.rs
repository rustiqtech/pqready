//! SBPF instruction decoding, call classification and intra-procedural control flow for one
//! executable range of an ELF.
//!
//! Instructions are addressed by slot (8 bytes); `lddw` occupies two slots.  Jump targets are `slot
//! + 1 + off`, relative call targets `slot + 1 + imm`.
//!
//! Decoding is deliberately conservative across SBPF versions: any instruction not recognised as a
//! constant move, a jump, a call, a store or an exit is treated as overwriting its destination
//! register with an unknown value. That can lose precision but never invents a constant.

use crate::syscalls::Syscall;
use std::collections::HashMap;

pub const OP_LDDW: u8 = 0x18;
pub const OP_JA: u8 = 0x05;
pub const OP_CALL: u8 = 0x85;
pub const OP_CALLX: u8 = 0x8d;
pub const OP_EXIT: u8 = 0x95;
/// `return` in newer SBPF versions; unused in legacy, so safe to treat as exit.
pub const OP_RETURN: u8 = 0x9d;
pub const OP_MOV64_IMM: u8 = 0xb7;
pub const OP_MOV32_IMM: u8 = 0xb4;
pub const OP_MOV64_REG: u8 = 0xbf;
pub const OP_MOV32_REG: u8 = 0xbc;
pub const OP_ADD64_IMM: u8 = 0x07;
pub const OP_SUB64_IMM: u8 = 0x17;
pub const OP_ADD64_REG: u8 = 0x0f;

const CLASS_MASK: u8 = 0x07;
const CLASS_ST: u8 = 0x02;
const CLASS_STX: u8 = 0x03;
const CLASS_JMP: u8 = 0x05;

#[derive(Clone, Copy, Debug)]
pub struct Instr {
    pub slot: usize,
    pub opc: u8,
    pub dst: u8,
    pub src: u8,
    pub off: i16,
    pub imm: i32,
    /// Full 64-bit immediate for `lddw`; equals `imm` otherwise.
    pub imm64: i64,
    /// Length in slots (2 for `lddw`).
    pub len: usize,
}

pub struct Code {
    /// File offset of slot 0.
    pub file_base: usize,
    /// Virtual address of slot 0.
    pub vaddr_base: u64,
    pub instrs: Vec<Instr>,
    by_slot: HashMap<usize, usize>,
    /// Model 64-bit add/sub (see `models_alu`). False until the caller, which knows the SBPF
    /// version, sets it: unknown versions stay conservative.
    pub model_alu: bool,
}

impl Code {
    pub fn decode(text: &[u8], file_base: usize, vaddr_base: u64) -> Self {
        let n = text.len() / 8;
        let mut instrs = Vec::with_capacity(n);
        let mut by_slot = HashMap::with_capacity(n);
        let mut slot = 0;
        while slot < n {
            let b = &text[slot * 8..slot * 8 + 8];
            let opc = b[0];
            let imm = i32::from_le_bytes(b[4..8].try_into().unwrap());
            let (len, imm64) = if opc == OP_LDDW && slot + 1 < n {
                let hi = u32::from_le_bytes(text[slot * 8 + 12..slot * 8 + 16].try_into().unwrap());
                (2, ((u64::from(hi) << 32) | u64::from(imm as u32)) as i64)
            } else {
                (1, i64::from(imm))
            };
            by_slot.insert(slot, instrs.len());
            instrs.push(Instr {
                slot,
                opc,
                dst: b[1] & 0x0f,
                src: b[1] >> 4,
                off: i16::from_le_bytes([b[2], b[3]]),
                imm,
                imm64,
                len,
            });
            slot += len;
        }
        Self {
            file_base,
            vaddr_base,
            instrs,
            by_slot,
            model_alu: false,
        }
    }

    pub fn idx_at_slot(&self, slot: i64) -> Option<usize> {
        usize::try_from(slot)
            .ok()
            .and_then(|s| self.by_slot.get(&s).copied())
    }

    pub fn idx_at_file(&self, off: usize) -> Option<usize> {
        let rel = off.checked_sub(self.file_base)?;
        (rel % 8 == 0)
            .then(|| self.idx_at_slot((rel / 8) as i64))
            .flatten()
    }

    pub fn idx_at_vaddr(&self, vaddr: u64) -> Option<usize> {
        let rel = vaddr.checked_sub(self.vaddr_base)?;
        (rel % 8 == 0)
            .then(|| self.idx_at_slot((rel / 8) as i64))
            .flatten()
    }

    pub fn file_off(&self, idx: usize) -> usize {
        self.file_base + self.instrs[idx].slot * 8
    }
}

/// What a relocation says about the call instruction it patches.
#[derive(Clone, Debug)]
pub enum RelocCall {
    Syscall(String),
    /// Internal function, by file offset of its first instruction.
    Internal(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Call {
    Syscall {
        name: String,
        via_reloc: bool,
    },
    /// Internal function call, by instruction index of the callee.
    Internal(usize),
    /// `callx`: target not known statically.
    Indirect,
    /// `call` with src = 0 whose immediate is neither a known syscall hash nor
    /// a valid relative target: probably a syscall missing from our table.
    Unresolved(u32),
    /// Relocated or malformed call we could not resolve.
    Unknown,
}

pub fn classify_calls(
    code: &Code,
    reloc_calls: &HashMap<usize, RelocCall>,
    table: &HashMap<u32, &'static Syscall>,
) -> HashMap<usize, Call> {
    let mut calls = HashMap::new();
    for (idx, i) in code.instrs.iter().enumerate() {
        let call = match i.opc {
            OP_CALLX => Call::Indirect,
            OP_CALL => {
                if let Some(rc) = reloc_calls.get(&code.file_off(idx)) {
                    match rc {
                        RelocCall::Syscall(name) => Call::Syscall {
                            name: name.clone(),
                            via_reloc: true,
                        },
                        RelocCall::Internal(t) => {
                            code.idx_at_file(*t).map_or(Call::Unknown, Call::Internal)
                        }
                    }
                } else if let Some(sc) = (i.src == 0).then(|| table.get(&(i.imm as u32))).flatten()
                {
                    Call::Syscall {
                        name: sc.name.to_string(),
                        via_reloc: false,
                    }
                } else if i.imm == -1 {
                    Call::Unknown
                } else if let Some(t) = code.idx_at_slot(i.slot as i64 + 1 + i64::from(i.imm)) {
                    Call::Internal(t)
                } else if i.src == 0 {
                    Call::Unresolved(i.imm as u32)
                } else {
                    Call::Unknown
                }
            }
            _ => continue,
        };
        calls.insert(idx, call);
    }
    calls
}

pub fn is_cond_jump(opc: u8) -> bool {
    opc & CLASS_MASK == CLASS_JMP
        && !matches!(opc, OP_JA | OP_CALL | OP_CALLX | OP_EXIT | OP_RETURN)
}

pub fn is_store(opc: u8) -> bool {
    matches!(opc & CLASS_MASK, CLASS_ST | CLASS_STX)
}

/// Intra-procedural successors: calls fall through, exits have none.
pub fn successors(code: &Code, idx: usize, out: &mut Vec<usize>) {
    out.clear();
    let i = &code.instrs[idx];
    let target = || code.idx_at_slot(i.slot as i64 + 1 + i64::from(i.off));
    let fall = || code.idx_at_slot((i.slot + i.len) as i64);
    match i.opc {
        OP_EXIT | OP_RETURN => {}
        OP_JA => out.extend(target()),
        o if is_cond_jump(o) => {
            out.extend(target());
            out.extend(fall());
        }
        _ => out.extend(fall()),
    }
}

/// Whether the 64-bit add/sub encodings of this SBPF version (from `e_flags`) mean what they mean
/// in V0. False for V2, which swaps the operands of `sub` with an immediate and reassigns
/// instruction classes, and for values sbpf treats as reserved. Source: sbpf `program.rs`
/// (SBPFVersion features) and `elf.rs` (`e_flags` mapping).
pub fn models_alu(e_flags: u32) -> bool {
    matches!(e_flags, 0 | 1 | 3 | 4)
}
