//! Module to provide function to convert ast into opcode

use rnasm_ast::{ActualOperand, CastStrategy, Expression, IndexableRegister};
use rnasm_opcode::{AddrMode, Mnemonic};

/// Get actual addressing mode of given mnemonic.
/// This return None if mnemonic is relative, but indexing.
pub fn operand_to_addrmode(
    mnemonic: Mnemonic,
    operand: Option<&ActualOperand>,
) -> Option<AddrMode> {
    if let Some(ref operand) = operand {
        use ActualOperand::*;
        match operand {
            Accumulator(_) => Some(AddrMode::Accumulator),
            AbsoluteOrRelative(aor) => {
                if mnemonic.is_relative() {
                    if matches!(aor.register, None) {
                        Some(AddrMode::Relative)
                    } else {
                        None
                    }
                } else {
                    match aor.register {
                        Some(IndexableRegister::X) => Some(AddrMode::AbsoluteX),
                        Some(IndexableRegister::Y) => Some(AddrMode::AbsoluteY),
                        None => Some(AddrMode::Absolute),
                    }
                }
            }
            Immediate(_) => Some(AddrMode::Immediate),
            Indirect(ind) => match ind.register {
                Some(IndexableRegister::X) => Some(AddrMode::IndirectX),
                Some(IndexableRegister::Y) => Some(AddrMode::IndirectY),
                None => Some(AddrMode::Indirect),
            },
            Zeropage(zpg) => match zpg.register {
                Some(IndexableRegister::X) => Some(AddrMode::ZeropageX),
                Some(IndexableRegister::Y) => Some(AddrMode::ZeropageY),
                None => Some(AddrMode::Zeropage),
            },
        }
    } else {
        Some(AddrMode::Implied)
    }
}

/// Try to get the operand's cast strategy.
pub fn operand_to_cast(operand: Option<&ActualOperand>) -> Option<CastStrategy> {
    if let Some(ref operand) = operand {
        use ActualOperand::*;
        match operand {
            Immediate(imm) => Some(imm.cast),
            Indirect(ind) => Some(ind.cast?),
            Zeropage(zpg) => Some(zpg.cast),
            _ => None,
        }
    } else {
        None
    }
}

/// Try to get operand's expression.
pub fn operand_to_expr(operand: Option<&ActualOperand>) -> Option<&Expression> {
    if let Some(ref operand) = operand {
        use ActualOperand::*;
        match operand {
            AbsoluteOrRelative(aor) => Some(&aor.expr),
            Immediate(imm) => Some(&imm.expr),
            Indirect(ind) => Some(&ind.expr),
            Zeropage(zpg) => Some(&zpg.expr),
            _ => None,
        }
    } else {
        None
    }
}
