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

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpcodeByteLen {
    One,
    Two,
    Three,
}

impl From<OpcodeByteLen> for u16 {
    fn from(value: OpcodeByteLen) -> Self {
        match value {
            OpcodeByteLen::One => 1,
            OpcodeByteLen::Two => 2,
            OpcodeByteLen::Three => 3,
        }
    }
}

/// A struct which hold menmonic and addressing mode.
#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Opcode {
    mnemonic: Mnemonic,
    addrmode: AddrMode,
}

impl Opcode {
    pub fn to_byte_len(&self) -> OpcodeByteLen {
        use AddrMode::*;
        use OpcodeByteLen::*;
        match self.addrmode {
            Accumulator | Implied => One,
            Immediate
            | Relative
            | Zeropage
            | ZeropageX
            | ZeropageY
            | IndirectX
            | IndirectY => Two,
            Indirect | Absolute | AbsoluteX | AbsoluteY => Three,
        }
    }
}

impl TryFrom<Opcode> for u8 {
    type Error = OpcodeConvertError;

    fn try_from(value: Opcode) -> Result<Self, Self::Error> {
        use AddrMode::*;
        use Mnemonic::*;
        match (value.mnemonic, value.addrmode) {
            (Adc, Immediate)   => Ok(0x69),
            (Adc, Zeropage)    => Ok(0x65),
            (Adc, ZeropageX)   => Ok(0x75),
            (Adc, Absolute)    => Ok(0x6D),
            (Adc, AbsoluteX)   => Ok(0x7D),
            (Adc, AbsoluteY)   => Ok(0x79),
            (Adc, IndirectX)   => Ok(0x61),
            (Adc, IndirectY)   => Ok(0x71),
            (And, Immediate)   => Ok(0x29),
            (And, Zeropage)    => Ok(0x25),
            (And, ZeropageX)   => Ok(0x35),
            (And, Absolute)    => Ok(0x2D),
            (And, AbsoluteX)   => Ok(0x3D),
            (And, AbsoluteY)   => Ok(0x39),
            (And, IndirectX)   => Ok(0x21),
            (And, IndirectY)   => Ok(0x31),
            (Asl, Accumulator) => Ok(0x0A),
            (Asl, Zeropage)    => Ok(0x06),
            (Asl, ZeropageX)   => Ok(0x16),
            (Asl, Absolute)    => Ok(0x0E),
            (Asl, AbsoluteX)   => Ok(0x1E),
            (Bcc, Relative)    => Ok(0x90),
            (Bcs, Relative)    => Ok(0xB0),
            (Beq, Relative)    => Ok(0xF0),
            (Bit, Zeropage)    => Ok(0x24),
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
            (Cmp, Zeropage)    => Ok(0xC5),
            (Cmp, ZeropageX)   => Ok(0xD5),
            (Cmp, Absolute)    => Ok(0xCD),
            (Cmp, AbsoluteX)   => Ok(0xDD),
            (Cmp, AbsoluteY)   => Ok(0xD9),
            (Cmp, IndirectX)   => Ok(0xC1),
            (Cmp, IndirectY)   => Ok(0xD1),
            (Cpx, Immediate)   => Ok(0xE0),
            (Cpx, Zeropage)    => Ok(0xE4),
            (Cpx, Absolute)    => Ok(0xEC),
            (Cpy, Immediate)   => Ok(0xC0),
            (Cpy, Zeropage)    => Ok(0xC4),
            (Cpy, Absolute)    => Ok(0xCC),
            (Dec, Zeropage)    => Ok(0xC6),
            (Dec, ZeropageX)   => Ok(0xD6),
            (Dec, Absolute)    => Ok(0xCE),
            (Dec, AbsoluteX)   => Ok(0xDE),
            (Dex, Implied)     => Ok(0xCA),
            (Dey, Implied)     => Ok(0x88),
            (Eor, Immediate)   => Ok(0x49),
            (Eor, Zeropage)    => Ok(0x45),
            (Eor, ZeropageX)   => Ok(0x55),
            (Eor, Absolute)    => Ok(0x4D),
            (Eor, AbsoluteX)   => Ok(0x5D),
            (Eor, AbsoluteY)   => Ok(0x59),
            (Eor, IndirectX)   => Ok(0x41),
            (Eor, IndirectY)   => Ok(0x51),
            (Inc, Zeropage)    => Ok(0xE6),
            (Inc, ZeropageX)   => Ok(0xF6),
            (Inc, Absolute)    => Ok(0xEE),
            (Inc, AbsoluteX)   => Ok(0xFE),
            (Inx, Implied)     => Ok(0xE8),
            (Iny, Implied)     => Ok(0xC8),
            (Jmp, Absolute)    => Ok(0x4C),
            (Jmp, Indirect)    => Ok(0x6C),
            (Jsr, Absolute)    => Ok(0x20),
            (Lda, Immediate)   => Ok(0xA9),
            (Lda, Zeropage)    => Ok(0xA5),
            (Lda, ZeropageX)   => Ok(0xB5),
            (Lda, Absolute)    => Ok(0xAD),
            (Lda, AbsoluteX)   => Ok(0xBD),
            (Lda, AbsoluteY)   => Ok(0xB9),
            (Lda, IndirectX)   => Ok(0xA1),
            (Lda, IndirectY)   => Ok(0xB1),
            (Ldx, Immediate)   => Ok(0xA2),
            (Ldx, Zeropage)    => Ok(0xA6),
            (Ldx, ZeropageY)   => Ok(0xB6),
            (Ldx, Absolute)    => Ok(0xAE),
            (Ldx, AbsoluteY)   => Ok(0xBE),
            (Ldy, Immediate)   => Ok(0xA0),
            (Ldy, Zeropage)    => Ok(0xA4),
            (Ldy, ZeropageX)   => Ok(0xB4),
            (Ldy, Absolute)    => Ok(0xAC),
            (Ldy, AbsoluteX)   => Ok(0xBC),
            (Lsr, Accumulator) => Ok(0x4A),
            (Lsr, Zeropage)    => Ok(0x46),
            (Lsr, ZeropageX)   => Ok(0x56),
            (Lsr, Absolute)    => Ok(0x4E),
            (Lsr, AbsoluteX)   => Ok(0x5E),
            (Nop, Implied)     => Ok(0xEA),
            (Ora, Immediate)   => Ok(0x09),
            (Ora, Zeropage)    => Ok(0x05),
            (Ora, ZeropageX)   => Ok(0x15),
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
            (Rol, Zeropage)    => Ok(0x26),
            (Rol, ZeropageX)   => Ok(0x36),
            (Rol, Absolute)    => Ok(0x2E),
            (Rol, AbsoluteX)   => Ok(0x3E),
            (Ror, Accumulator) => Ok(0x6A),
            (Ror, Zeropage)    => Ok(0x66),
            (Ror, ZeropageX)   => Ok(0x76),
            (Ror, Absolute)    => Ok(0x6E),
            (Ror, AbsoluteX)   => Ok(0x7E),
            (Rti, Implied)     => Ok(0x40),
            (Rts, Implied)     => Ok(0x60),
            (Sbc, Immediate)   => Ok(0xE9),
            (Sbc, Zeropage)    => Ok(0xE5),
            (Sbc, ZeropageX)   => Ok(0xF5),
            (Sbc, Absolute)    => Ok(0xED),
            (Sbc, AbsoluteX)   => Ok(0xFD),
            (Sbc, AbsoluteY)   => Ok(0xF9),
            (Sbc, IndirectX)   => Ok(0xE1),
            (Sbc, IndirectY)   => Ok(0xF1),
            (Sec, Implied)     => Ok(0x38),
            (Sed, Implied)     => Ok(0xF8),
            (Sei, Implied)     => Ok(0x78),
            (Sta, Zeropage)    => Ok(0x85),
            (Sta, ZeropageX)   => Ok(0x95),
            (Sta, Absolute)    => Ok(0x8D),
            (Sta, AbsoluteX)   => Ok(0x9D),
            (Sta, AbsoluteY)   => Ok(0x99),
            (Sta, IndirectX)   => Ok(0x81),
            (Sta, IndirectY)   => Ok(0x91),
            (Stx, Zeropage)    => Ok(0x86),
            (Stx, ZeropageY)   => Ok(0x96),
            (Stx, Absolute)    => Ok(0x8E),
            (Sty, Zeropage)    => Ok(0x84),
            (Sty, ZeropageX)   => Ok(0x94),
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

impl Mnemonic {
    /// Return true if the mnemonic is relative.
    pub fn is_relative(&self) -> bool {
        use Mnemonic::*;
        matches!(self, Bcc | Bcs | Beq | Bmi | Bne | Bpl | Bvc | Bvs)
    }
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
    Zeropage,
    ZeropageX,
    ZeropageY,
}
