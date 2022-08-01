#![allow(dead_code)]

pub mod object;
pub mod env;

use std::cell::Cell;
use std::rc::Rc;
use crate::asm::InstList;
use crate::parser::ast::{
    Program, Statement, Expression, Identifier, Prefix, PrefixOp,
    Infix, InfixOp, UncertainAddrMode
};
use crate::inst::{self, AddrMode};
use env::Environment;
use object::{Object, Integer, IntKind};

pub struct Eval<'a> {
    program: &'a Program,
    curr_pos: Cell<usize>,
    addr: u16,
    curr_addr: Cell<u16>,
    env: Rc<Environment>,
}

impl<'a> Eval<'a> {
    pub fn new(program: &'a Program, addr: u16, env: Rc<Environment>) -> Eval<'a> {
        Eval {
            program,
            curr_pos: Cell::new(0),
            addr,
            curr_addr: Cell::new(addr),
            env
        }
    }

    pub fn eval(&self) -> InstList {
        let mut body  = Vec::new();
        while self.curr_pos.get() < self.program.body.len() {
            match self.stmt() {
                Some(inst) => body.push(inst),
                None => (),
            }
        }
        InstList::new(self.addr, body)
    }

    fn stmt(&self) -> Option<inst::Instruction> {
        match self.curr_stmt()? {
            Statement::Assign(val) => {
                self.next_stmt();
                let obj = self.expr(&val.expr)?.wrapping();
                self.env.reg(val.ident.name.to_owned(), obj);
                None
            }
            Statement::Instruction(val) => {
                self.next_stmt();
                let inst = match val.mode {
                    UncertainAddrMode::AbsoluteOrZeroPage => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPage(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPage(value))
                            }
                            IntKind::Word => {
                                let value = int.value;
                                inst::Instruction::new(val.kind, AddrMode::Absolute(value))
                            }
                        }
                    }
                    UncertainAddrMode::AbsoluteXOrZeroPageX => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPageX(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPageX(value))
                            }
                            IntKind::Word => {
                                let value = int.value;
                                inst::Instruction::new(val.kind, AddrMode::AbsoluteX(value))
                            }
                        }
                    }
                    UncertainAddrMode::AbsoluteYOrZeroPageY => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPageY(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::ZeroPageY(value))
                            }
                            IntKind::Word => {
                                let value = int.value;
                                inst::Instruction::new(val.kind, AddrMode::AbsoluteY(value))
                            }
                        }
                    }
                    UncertainAddrMode::Accumulator => {
                        inst::Instruction::new(val.kind, AddrMode::Accumulator)
                    }
                    UncertainAddrMode::Implied => {
                        inst::Instruction::new(val.kind, AddrMode::Implied)
                    }
                    UncertainAddrMode::Immediate => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::Immediate(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::Immediate(value))
                            }
                            _ => return None,
                        }
                    }
                    UncertainAddrMode::IndirectX => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::IndirectX(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::IndirectX(value))
                            }
                            _ => return None,
                        }
                    }
                    UncertainAddrMode::IndirectY => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Lsb => {
                                let value = int.value as u8;
                                inst::Instruction::new(val.kind, AddrMode::IndirectY(value))
                            }
                            IntKind::Msb => {
                                let value = (int.value >> 8) as u8;
                                inst::Instruction::new(val.kind, AddrMode::IndirectY(value))
                            }
                            _ => return None,
                        }
                    }
                    UncertainAddrMode::Indirect => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Word => {
                                let value = int.value;
                                inst::Instruction::new(val.kind, AddrMode::Indirect(value))
                            }
                            _ => return None,
                        }
                    }
                    UncertainAddrMode::Relative => {
                        let int = self.expr(&val.expr)?;
                        match int.kind {
                            IntKind::Word => {
                                let value = int.value;
                                inst::Instruction::new(val.kind, AddrMode::Relative(value))
                            }
                            _ => return None,
                        }
                    }
                };
                self.move_addr(inst.len()?);
                Some(inst)
            }
        }
    }

    fn expr(&self, expr: &Expression) -> Option<Integer> {
        match expr {
            Expression::Identifier(val) => self.identifier(val),
            Expression::Integer(val)    => Some(Integer::new(val.value, IntKind::Word)),
            Expression::Prefix(prefix)  => self.prefix(prefix),
            Expression::Infix(infix)    => self.infix(infix),
            Expression::CurrAddr(_)     => Some(Integer::new(self.curr_addr.get(), IntKind::Word)),
            Expression::EmptyExpr(_)    => None,
        }
    }

    fn identifier(&self, ident: &Identifier) -> Option<Integer> {
        let obj = self.env.get(&ident.name)?;
        match obj {
            Object::Integer(int) => Some(int),
        }
    }

    fn prefix(&self, prefix: &Prefix) -> Option<Integer> {
        let mut ret = self.expr(prefix.rhs_expr.as_ref())?;
        ret.kind = match prefix.op {
            PrefixOp::TakeLSB => IntKind::Lsb,
            PrefixOp::TakeMSB => IntKind::Msb,
        };
        Some(ret)
    }

    fn infix(&self, infix: &Infix) -> Option<Integer> {
        let lhs = self.expr(infix.lhs_expr.as_ref())?;
        let rhs = self.expr(infix.rhs_expr.as_ref())?;
        let val = match infix.op {
            InfixOp::Add    => lhs.value.wrapping_add(rhs.value),
            InfixOp::Sub    => lhs.value.wrapping_sub(rhs.value),
            InfixOp::Mul    => lhs.value.wrapping_mul(rhs.value),
            InfixOp::Div    => lhs.value.wrapping_div(rhs.value),
            InfixOp::LShift => lhs.value.wrapping_shl(rhs.value as u32),
            InfixOp::RShift => lhs.value.wrapping_shl(rhs.value as u32),
        };
        let kind = if lhs.kind == IntKind::Word && rhs.kind == IntKind::Word {
            IntKind::Word
        } else if lhs.kind == rhs.kind {
            lhs.kind
        } else {
            // (<num) + (>num) is undefined
            return None
        };
        Some(Integer::new(val, kind))
    }
}

impl<'a> Eval<'a> {
    fn curr_stmt(&self) -> Option<&Statement> {
        self.program.body.get(self.curr_pos.get())
    }

    fn next_stmt(&self) {
        self.curr_pos.set(self.curr_pos.get() + 1);
    }

    fn move_addr(&self, diff: u16) {
        self.curr_addr.set(self.curr_addr.get().wrapping_add(diff));
    }
}
