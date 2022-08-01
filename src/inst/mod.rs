#![allow(dead_code)]

mod table;

use std::hash::{Hash, Hasher};
use std::mem::discriminant;
use table::INST_TO_OPCODE;

#[derive(Debug, Eq, Clone, Copy)]
pub struct Instruction {
    pub kind: Mnemonic,
    pub mode: AddrMode,
}

impl Instruction {
    /// Create a new instruction
    pub fn new(kind: Mnemonic, mode: AddrMode) -> Instruction {
        Instruction { kind, mode }
    }

    /// If the instruction is valid, return the byte of opcode
    pub fn byte(&self) -> Option<u8> {
        Some(INST_TO_OPCODE.get(self)?.byte)
    }

    /// If the instruction is valid, return the length of opcode
    pub fn len(&self) -> Option<u16> {
        Some(INST_TO_OPCODE.get(self)?.len)
    }
}

impl PartialEq for Instruction {
    fn eq(&self, other: &Self) -> bool {
        let b1 = self.kind == other.kind;
        // Hash requires h1 == h2 iff hash(h1) == hash(h2), so ignore internal value
        let b2 = discriminant(&self.mode) == discriminant(&other.mode);
        b1 && b2
    }
}

impl Hash for Instruction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        // Don't care the internal value of AddrMode
        discriminant(&self.mode).hash(state);
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Mnemonic {
    Adc, And, Asl, Bcc, Bcs, Beq, Bit, Bmi, Bne, Bpl, Brk, Bvc, Bvs, Clc,
    Cld, Cli, Clv, Cmp, Cpx, Cpy, Dec, Dex, Dey, Eor, Inc, Inx, Iny, Jmp,
    Jsr, Lda, Ldx, Ldy, Lsr, Nop, Ora, Pha, Php, Pla, Plp, Rol, Ror, Rti,
    Rts, Sbc, Sec, Sed, Sei, Sta, Stx, Sty, Tax, Tay, Tsx, Txa, Txs, Tya,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum AddrMode {
    Accumulator,
    Absolute(u16),
    AbsoluteX(u16),
    AbsoluteY(u16),
    Immediate(u8),
    Implied,
    Indirect(u16),
    IndirectX(u8),
    IndirectY(u8),
    Relative(u16),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
}
