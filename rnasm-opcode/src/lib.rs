//! Provide a way to convert mnemonic into machine code.

use derive_new::new;
use thiserror::Error;

/// An error which will be returned when the `Opcode` is invalid on 6502.
#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[error("{addrmode:?} of {mnemonic:?} is invalid")]
pub struct OpcodeConvertError {
    mnemonic: Mnemonic,
    addrmode: AddrMode,
}

/// A struct which hold menmonic and addressing mode.
#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Opcode {
    mnemonic: Mnemonic,
    addrmode: AddrMode,
}

impl TryFrom<Opcode> for u8 {
    type Error = OpcodeConvertError;

    fn try_from(value: Opcode) -> Result<Self, Self::Error> {
        use AddrMode::*;
        use Mnemonic::*;
        match (value.mnemonic, value.addrmode) {
            (Adc, Immediate)   => Ok(0x69),
            (Adc, ZeroPage)    => Ok(0x65),
            (Adc, ZeroPageX)   => Ok(0x75),
            (Adc, Absolute)    => Ok(0x6D),
            (Adc, AbsoluteX)   => Ok(0x7D),
            (Adc, AbsoluteY)   => Ok(0x79),
            (Adc, IndirectX)   => Ok(0x61),
            (Adc, IndirectY)   => Ok(0x71),
            (And, Immediate)   => Ok(0x29),
            (And, ZeroPage)    => Ok(0x25),
            (And, ZeroPageX)   => Ok(0x35),
            (And, Absolute)    => Ok(0x2D),
            (And, AbsoluteX)   => Ok(0x3D),
            (And, AbsoluteY)   => Ok(0x39),
            (And, IndirectX)   => Ok(0x21),
            (And, IndirectY)   => Ok(0x31),
            (Asl, Accumulator) => Ok(0x0A),
            (Asl, ZeroPage)    => Ok(0x06),
            (Asl, ZeroPageX)   => Ok(0x16),
            (Asl, Absolute)    => Ok(0x0E),
            (Asl, AbsoluteX)   => Ok(0x1E),
            (Bcc, Relative)    => Ok(0x90),
            (Bcs, Relative)    => Ok(0xB0),
            (Beq, Relative)    => Ok(0xF0),
            (Bit, ZeroPage)    => Ok(0x24),
            (Bit, Absolute)    => Ok(0x2C),
            (Bmi, Relative)    => Ok(0x30),
            (Bne, Relative)    => Ok(0xD0),
            (Bpl, Relative)    => Ok(0x10),
            (Brk, Implied)     => Ok(0x00),
            (Bvc, Relative)    => Ok(0x50),
            (Bvs, Relative)    => Ok(0x70),
            (Clc, Implied)     => Ok(0x18),
            (Cld, Implied)     => Ok(0xD8),
            (Cli, Implied)     => Ok(0x58),
            (Clv, Implied)     => Ok(0xB8),
            (Cmp, Immediate)   => Ok(0xC9),
            (Cmp, ZeroPage)    => Ok(0xC5),
            (Cmp, ZeroPageX)   => Ok(0xD5),
            (Cmp, Absolute)    => Ok(0xCD),
            (Cmp, AbsoluteX)   => Ok(0xDD),
            (Cmp, AbsoluteY)   => Ok(0xD9),
            (Cmp, IndirectX)   => Ok(0xC1),
            (Cmp, IndirectY)   => Ok(0xD1),
            (Cpx, Immediate)   => Ok(0xE0),
            (Cpx, ZeroPage)    => Ok(0xE4),
            (Cpx, Absolute)    => Ok(0xEC),
            (Cpy, Immediate)   => Ok(0xC0),
            (Cpy, ZeroPage)    => Ok(0xC4),
            (Cpy, Absolute)    => Ok(0xCC),
            (Dec, ZeroPage)    => Ok(0xC6),
            (Dec, ZeroPageX)   => Ok(0xD6),
            (Dec, Absolute)    => Ok(0xCE),
            (Dec, AbsoluteX)   => Ok(0xDE),
            (Dex, Implied)     => Ok(0xCA),
            (Dey, Implied)     => Ok(0x88),
            (Eor, Immediate)   => Ok(0x49),
            (Eor, ZeroPage)    => Ok(0x45),
            (Eor, ZeroPageX)   => Ok(0x55),
            (Eor, Absolute)    => Ok(0x4D),
            (Eor, AbsoluteX)   => Ok(0x5D),
            (Eor, AbsoluteY)   => Ok(0x59),
            (Eor, IndirectX)   => Ok(0x41),
            (Eor, IndirectY)   => Ok(0x51),
            (Inc, ZeroPage)    => Ok(0xE6),
            (Inc, ZeroPageX)   => Ok(0xF6),
            (Inc, Absolute)    => Ok(0xEE),
            (Inc, AbsoluteX)   => Ok(0xFE),
            (Inx, Implied)     => Ok(0xE8),
            (Iny, Implied)     => Ok(0xC8),
            (Jmp, Absolute)    => Ok(0x4C),
            (Jmp, Indirect)    => Ok(0x6C),
            (Jsr, Absolute)    => Ok(0x20),
            (Lda, Immediate)   => Ok(0xA9),
            (Lda, ZeroPage)    => Ok(0xA5),
            (Lda, ZeroPageX)   => Ok(0xB5),
            (Lda, Absolute)    => Ok(0xAD),
            (Lda, AbsoluteX)   => Ok(0xBD),
            (Lda, AbsoluteY)   => Ok(0xB9),
            (Lda, IndirectX)   => Ok(0xA1),
            (Lda, IndirectY)   => Ok(0xB1),
            (Ldx, Immediate)   => Ok(0xA2),
            (Ldx, ZeroPage)    => Ok(0xA6),
            (Ldx, ZeroPageY)   => Ok(0xB6),
            (Ldx, Absolute)    => Ok(0xAE),
            (Ldx, AbsoluteY)   => Ok(0xBE),
            (Ldy, Immediate)   => Ok(0xA0),
            (Ldy, ZeroPage)    => Ok(0xA4),
            (Ldy, ZeroPageX)   => Ok(0xB4),
            (Ldy, Absolute)    => Ok(0xAC),
            (Ldy, AbsoluteX)   => Ok(0xBC),
            (Lsr, Accumulator) => Ok(0x4A),
            (Lsr, ZeroPage)    => Ok(0x46),
            (Lsr, ZeroPageX)   => Ok(0x56),
            (Lsr, Absolute)    => Ok(0x4E),
            (Lsr, AbsoluteX)   => Ok(0x5E),
            (Nop, Implied)     => Ok(0xEA),
            (Ora, Immediate)   => Ok(0x09),
            (Ora, ZeroPage)    => Ok(0x05),
            (Ora, ZeroPageX)   => Ok(0x15),
            (Ora, Absolute)    => Ok(0x0D),
            (Ora, AbsoluteX)   => Ok(0x1D),
            (Ora, AbsoluteY)   => Ok(0x19),
            (Ora, IndirectX)   => Ok(0x01),
            (Ora, IndirectY)   => Ok(0x11),
            (Pha, Implied)     => Ok(0x48),
            (Php, Implied)     => Ok(0x08),
            (Pla, Implied)     => Ok(0x68),
            (Plp, Implied)     => Ok(0x28),
            (Rol, Accumulator) => Ok(0x2A),
            (Rol, ZeroPage)    => Ok(0x26),
            (Rol, ZeroPageX)   => Ok(0x36),
            (Rol, Absolute)    => Ok(0x2E),
            (Rol, AbsoluteX)   => Ok(0x3E),
            (Ror, Accumulator) => Ok(0x6A),
            (Ror, ZeroPage)    => Ok(0x66),
            (Ror, ZeroPageX)   => Ok(0x76),
            (Ror, Absolute)    => Ok(0x6E),
            (Ror, AbsoluteX)   => Ok(0x7E),
            (Rti, Implied)     => Ok(0x40),
            (Rts, Implied)     => Ok(0x60),
            (Sbc, Immediate)   => Ok(0xE9),
            (Sbc, ZeroPage)    => Ok(0xE5),
            (Sbc, ZeroPageX)   => Ok(0xF5),
            (Sbc, Absolute)    => Ok(0xED),
            (Sbc, AbsoluteX)   => Ok(0xFD),
            (Sbc, AbsoluteY)   => Ok(0xF9),
            (Sbc, IndirectX)   => Ok(0xE1),
            (Sbc, IndirectY)   => Ok(0xF1),
            (Sec, Implied)     => Ok(0x38),
            (Sed, Implied)     => Ok(0xF8),
            (Sei, Implied)     => Ok(0x78),
            (Sta, ZeroPage)    => Ok(0x85),
            (Sta, ZeroPageX)   => Ok(0x95),
            (Sta, Absolute)    => Ok(0x8D),
            (Sta, AbsoluteX)   => Ok(0x9D),
            (Sta, AbsoluteY)   => Ok(0x99),
            (Sta, IndirectX)   => Ok(0x81),
            (Sta, IndirectY)   => Ok(0x91),
            (Stx, ZeroPage)    => Ok(0x86),
            (Stx, ZeroPageY)   => Ok(0x96),
            (Stx, Absolute)    => Ok(0x8E),
            (Sty, ZeroPage)    => Ok(0x84),
            (Sty, ZeroPageX)   => Ok(0x94),
            (Sty, Absolute)    => Ok(0x8C),
            (Tax, Implied)     => Ok(0xAA),
            (Tay, Implied)     => Ok(0xA8),
            (Tsx, Implied)     => Ok(0xBA),
            (Txa, Implied)     => Ok(0x8A),
            (Txs, Implied)     => Ok(0x9A),
            (Tya, Implied)     => Ok(0x98),
            _ => Err(OpcodeConvertError {
                mnemonic: value.mnemonic,
                addrmode: value.addrmode,
            }),
        }
    }
}

/// An error which will be returned when the given string is
/// invalid name of mnemonic.
#[derive(Debug, Error, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[error("{0} is invalid name of mnemonic")]
pub struct MnemonicConvertError(String);

/// An enum which represent set of valid 6502 mnemonic name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[rustfmt::skip]
pub enum Mnemonic {
    Adc, And, Asl, Bcc, Bcs, Beq, Bit, Bmi, Bne, Bpl, Brk, Bvc, Bvs, Clc,
    Cld, Cli, Clv, Cmp, Cpx, Cpy, Dec, Dex, Dey, Eor, Inc, Inx, Iny, Jmp,
    Jsr, Lda, Ldx, Ldy, Lsr, Nop, Ora, Pha, Php, Pla, Plp, Rol, Ror, Rti,
    Rts, Sbc, Sec, Sed, Sei, Sta, Stx, Sty, Tax, Tay, Tsx, Txa, Txs, Tya,
}

impl TryFrom<&str> for Mnemonic {
    type Error = MnemonicConvertError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        use Mnemonic::*;
        match value.to_lowercase().as_str() {
            "adc" => Ok(Adc),
            "and" => Ok(And),
            "asl" => Ok(Asl),
            "bcc" => Ok(Bcc),
            "bcs" => Ok(Bcs),
            "beq" => Ok(Beq),
            "bit" => Ok(Bit),
            "bmi" => Ok(Bmi),
            "bne" => Ok(Bne),
            "bpl" => Ok(Bpl),
            "brk" => Ok(Brk),
            "bvc" => Ok(Bvc),
            "bvs" => Ok(Bvs),
            "clc" => Ok(Clc),
            "cld" => Ok(Cld),
            "cli" => Ok(Cli),
            "clv" => Ok(Clv),
            "cmp" => Ok(Cmp),
            "cpx" => Ok(Cpx),
            "cpy" => Ok(Cpy),
            "dec" => Ok(Dec),
            "dex" => Ok(Dex),
            "dey" => Ok(Dey),
            "eor" => Ok(Eor),
            "inc" => Ok(Inc),
            "inx" => Ok(Inx),
            "iny" => Ok(Iny),
            "jmp" => Ok(Jmp),
            "jsr" => Ok(Jsr),
            "lda" => Ok(Lda),
            "ldx" => Ok(Ldx),
            "ldy" => Ok(Ldy),
            "lsr" => Ok(Lsr),
            "nop" => Ok(Nop),
            "ora" => Ok(Ora),
            "pha" => Ok(Pha),
            "php" => Ok(Php),
            "pla" => Ok(Pla),
            "plp" => Ok(Plp),
            "rol" => Ok(Rol),
            "ror" => Ok(Ror),
            "rti" => Ok(Rti),
            "rts" => Ok(Rts),
            "sbc" => Ok(Sbc),
            "sec" => Ok(Sec),
            "sed" => Ok(Sed),
            "sei" => Ok(Sei),
            "sta" => Ok(Sta),
            "stx" => Ok(Stx),
            "sty" => Ok(Sty),
            "tax" => Ok(Tax),
            "tay" => Ok(Tay),
            "tsx" => Ok(Tsx),
            "txa" => Ok(Txa),
            "txs" => Ok(Txs),
            "tya" => Ok(Tya),
            _ => Err(MnemonicConvertError(value.to_string())),
        }
    }
}

/// An enum which represent set of 6502 addressing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
}