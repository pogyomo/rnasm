#![allow(dead_code)]

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mnemonic {
    Adc, And, Asl, Bcc, Bcs, Beq, Bit, Bmi, Bne, Bpl, Brk, Bvc, Bvs, Clc,
    Cld, Cli, Clv, Cmp, Cpx, Cpy, Dec, Dex, Dey, Eor, Inc, Inx, Iny, Jmp,
    Jsr, Lda, Ldx, Ldy, Lsr, Nop, Ora, Pha, Php, Pla, Plp, Rol, Ror, Rti,
    Rts, Sbc, Sec, Sed, Sei, Sta, Stx, Sty, Tax, Tay, Tsx, Txa, Txs, Tya,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AddrMode {
    Accumulator,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Immediate,
    Implied,
    Indirect,
    IndirectX,
    IndirectY,
    Relative,
    Zeropage(ZPKind),
    ZeropageX(ZPKind),
    ZeropageY(ZPKind),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ZPKind {
    /// Use lsb of expression as operand
    Lsb,
    /// Use msb of expression as operand
    Msb,
}
