use derive_new::new;
use thiserror::Error;
use std::rc::Rc;
use rnasm_ast::{
    Statement, Instruction, Label, PseudoInstruction, ActualInstruction,
    GlobalLabel, LocalLabel, Expression, InfixOp, CastStrategy
};
use rnasm_opcode::{Mnemonic, Opcode, OpcodeByteLen};
use rnasm_span::{Span, Spannable};
use object::{StringObj, IntegerObj, Object};
use opcode::{operand_to_addrmode, operand_to_cast, operand_to_expr};
use symtable::SymbolTable;

mod object;
mod opcode;
mod symtable;

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CodeGenError {
    #[error("invalid pseudo instruction name")]
    InvalidPseudoName { span: Span },
    #[error("invalid instruction name")]
    InvalidActualName { span: Span },
    #[error("invalid instruction")]
    InvalidInstruction { span: Span },
    #[error("symbol already exist")]
    SymbolAlreadyExist{ span: Span },
    #[error("no such symbol exist")]
    NoSuchSymbolExist { span: Span },
    #[error("cannot define local label: must be placed under global label")]
    CannotDefineLocalLabel { span: Span },
    #[error("invalid number of arguemnts: expect {expect}, got {got}")]
    InvalidNumberOfArguments { span: Span, expect: usize, got: usize },
    #[error("invalid type of arguemnt: expect {expect}")]
    InvalidTypeOfArgument { span: Span, expect: &'static str },
    #[error("invalid infix operation: {reason}")]
    InvalidInfixOperation { span: Span, reason: &'static str },
    #[error("relative can't indexing with register")]
    RelativeCantIndexing { span: Span },
    #[error("relative exceed range: must be from -128 to 127")]
    RelativeExceedRange { span: Span },
}

impl Spannable for CodeGenError {
    fn span(&self) -> Span {
        use CodeGenError::*;
        match *self {
            InvalidPseudoName { span } => span,
            InvalidActualName { span } => span,
            InvalidInstruction { span } => span,
            SymbolAlreadyExist { span } => span,
            NoSuchSymbolExist { span } => span,
            CannotDefineLocalLabel { span } => span,
            InvalidNumberOfArguments { span, .. } => span,
            InvalidTypeOfArgument { span, .. } => span,
            InvalidInfixOperation { span, .. } => span,
            RelativeCantIndexing { span } => span,
            RelativeExceedRange { span } => span,
        }
    }
}

/// A set of infomation which is required while generating code.
/// These infomation is **temporary** used in each pass unlike
/// symbol table is used though all pass.
#[derive(new)]
#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CodeGenInfo {
    is_pass1: bool,

    #[new(value = "0")]
    address: u16,
    #[new(value = "None")]
    curr_label: Option<String>,
}

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeGen {
    #[new(default)]
    info: CodeGenInfo,

    #[new(default)]
    symtable: SymbolTable,
    #[new(default)]
    codes: Vec<(u16, Vec<u8>)>, // Generated codes
}

impl CodeGen {
    pub fn gen(
        mut self,
        stmts: Vec<Statement>
    ) -> Result<Vec<(u16, Vec<u8>)>, CodeGenError> {
        self.info = CodeGenInfo::new(true);
        for stmt in stmts.iter() {
            self.statement(stmt)?;
        }
        self.info = CodeGenInfo::new(false);
        for stmt in stmts.iter() {
            self.statement(stmt)?;
        }
        Ok(self.codes)
    }
}

impl CodeGen {
    fn statement(&mut self, stmt: &Statement) -> Result<(), CodeGenError> {
        match stmt {
            Statement::InstStatement(stmt) => {
                self.instruction(&stmt.inst)
            }
            Statement::LabelStatement(stmt) => {
                self.label(&stmt.label)
            }
            Statement::LabelInstStatement(stmt) => {
                self.label(&stmt.label)?;
                self.instruction(&stmt.inst)
            }
        }
    }

    fn instruction(&mut self, inst: &Instruction) -> Result<(), CodeGenError> {
        match inst {
            Instruction::PseudoInstruction(pseudo) => self.pseudo(pseudo),
            Instruction::ActualInstruction(actual) => self.actual(actual),
        }
    }

    fn label(&mut self, label: &Label) -> Result<(), CodeGenError> {
        match label {
            Label::GlobalLabel(label) => self.global_label(label),
            Label::LocalLabel(label) => self.local_label(label),
        }
    }

    fn pseudo(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        match pseudo.name.name.as_str() {
            "org" => self.org(pseudo),
            _ => Err(CodeGenError::InvalidPseudoName {
                span: pseudo.name.span()
            })
        }
    }

    fn actual(&mut self, actual: &ActualInstruction) -> Result<(), CodeGenError> {
        let Ok(mnemonic) = Mnemonic::try_from(actual.name.name.as_str()) else {
            return Err(CodeGenError::InvalidActualName {
                span: actual.name.span()
            });
        };
        let addrmode = operand_to_addrmode(mnemonic, actual.operand.as_ref())
            .ok_or(CodeGenError::RelativeCantIndexing {
                span: actual.span()
            })?;
        let opcode = Opcode::new(mnemonic, addrmode);

        if !self.info.is_pass1 {
            let cast = operand_to_cast(actual.operand.as_ref())
                .unwrap_or(CastStrategy::Lsb);
            let value = match operand_to_expr(actual.operand.as_ref()) {
                Some(expr) =>  match *self.eval(expr)? {
                    Object::IntegerObj(int) => int.value,
                    _ => return Err(CodeGenError::InvalidTypeOfArgument {
                        span: expr.span(),
                        expect: "integer"
                    })
                }
                None => 0,
            };
            let Ok(byte) = opcode.try_into() else {
                return Err(CodeGenError::InvalidInstruction {
                    span: actual.span()
                });
            };

            if mnemonic.is_relative() {
                if self.info.address + 2 < value {
                    if value - self.info.address - 2 <= 127 {
                        let diff = (value - self.info.address - 2) as u8;
                        self.write(vec![byte, diff])?;
                    } else {
                        return Err(CodeGenError::RelativeExceedRange {
                            span: actual.span()
                        });
                    }
                } else {
                    if self.info.address + 2 - value <= 128 {
                        let diff = (self.info.address + 2 - value) as u8;
                        self.write(vec![byte, (!diff).wrapping_add(1)])?;
                    } else {
                        return Err(CodeGenError::RelativeExceedRange {
                            span: actual.span()
                        });
                    }
                }
            } else {
                match opcode.to_byte_len() {
                    OpcodeByteLen::One => self.write(vec![byte])?,
                    OpcodeByteLen::Two => match cast {
                        CastStrategy::Lsb => {
                            self.write(vec![byte, value.to_le_bytes()[0]])?;
                        }
                        CastStrategy::Msb => {
                            self.write(vec![byte, value.to_le_bytes()[1]])?;
                        }
                    }
                    OpcodeByteLen::Three => {
                        let value = value.to_le_bytes();
                        self.write(vec![byte, value[0], value[1]])?;
                    }
                }
            }
        } else {
            let len = <OpcodeByteLen as Into<u16>>::into(opcode.to_byte_len());
            self.info.address += len;
        }
        Ok(())
    }

    fn global_label(&mut self, label: &GlobalLabel) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            if self.symtable.add(
                label.name.clone(),
                IntegerObj::new(self.info.address).into()
            ) {
                return Err(CodeGenError::SymbolAlreadyExist {
                    span: label.span()
                })
            }
        }
        self.info.curr_label = Some(label.name.clone());
        Ok(())
    }

    fn local_label(&mut self, label: &LocalLabel) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            let Some(ref global) = self.info.curr_label else {
                return Err(CodeGenError::CannotDefineLocalLabel {
                    span: label.span()
                });
            };
            let Some(symbol) = self.symtable.get(global) else {
                return Err(CodeGenError::CannotDefineLocalLabel {
                    span: label.span()
                });
            };
            if symbol.borrow_mut().add(
                label.name.clone(),
                IntegerObj::new(self.info.address).into()
            ) {
                return Err(CodeGenError::SymbolAlreadyExist {
                    span: label.span()
                });
            }
        }
        Ok(())
    }
}

impl CodeGen {
    fn org(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: 1,
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: 1,
                got: operand.args.len()
            })
        }

        self.info.address = match *self.eval(&operand.args.first())? {
            Object::IntegerObj(int) => int.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        Ok(())
    }
}

impl CodeGen {
    /// Write bytes to current address then advance the address.
    /// If it is pass1, only advance address.
    fn write(&mut self, bytes: Vec<u8>) -> Result<(), CodeGenError> {
        let len = bytes.len();
        if !self.info.is_pass1 && bytes.len() != 0 {
            self.codes.push((self.info.address, bytes));
        }
        self.info.address += len as u16;
        Ok(())
    }
}

impl CodeGen {
    fn eval(&mut self, expr: &Expression) -> Result<Rc<Object>, CodeGenError> {
        use rnasm_ast::Symbol;
        match expr {
            Expression::Surrounded(expr) => self.eval(&expr.expr),
            Expression::Integer(value) => {
                Ok(Rc::new(IntegerObj::new(value.value).into()))
            }
            Expression::StringExpr(str) => {
                Ok(Rc::new(StringObj::new(str.value.clone()).into()))
            }
            Expression::Symbol(symbol) => match symbol {
                Symbol::GlobalSymbol(global) => {
                    let Some(symbol) = self.symtable.get(&global.name) else {
                        return Err(CodeGenError::NoSuchSymbolExist {
                            span: global.span()
                        })
                    };
                    let value = Rc::clone(&symbol.borrow().value);
                    Ok(value)
                }
                Symbol::LocalSymbol(local) => {
                    let Some(ref parent) = self.info.curr_label else {
                        return Err(CodeGenError::NoSuchSymbolExist {
                            span: local.span()
                        })
                    };
                    let Some(symbol) = self.symtable.get(parent) else {
                        return Err(CodeGenError::NoSuchSymbolExist {
                            span: local.span()
                        })
                    };
                    let Some(value) = symbol.borrow().get(&local.name) else {
                        return Err(CodeGenError::NoSuchSymbolExist {
                            span: local.span()
                        })
                    };
                    Ok(value)
                }
            }
            Expression::InfixExpr(infix) => {
                let lhs = self.eval(&infix.lhs)?;
                let rhs = self.eval(&infix.rhs)?;
                match (&*lhs, &*rhs) {
                    (Object::StringObj(lhs), Object::StringObj(rhs)) => {
                        match infix.op {
                            InfixOp::Add => {
                                let str = format!("{}{}", lhs.value, rhs.value);
                                Ok(Rc::new(StringObj::new(str).into()))
                            }
                            _ => Err(CodeGenError::InvalidInfixOperation {
                                span: infix.span(),
                                reason: "only + can be used"
                            })
                        }
                    }
                    (Object::IntegerObj(lhs), Object::IntegerObj(rhs)) => {
                        match infix.op {
                            InfixOp::Add => {
                                let value = lhs.value + rhs.value;
                                Ok(Rc::new(IntegerObj::new(value).into()))
                            }
                            InfixOp::Sub => {
                                let value = lhs.value - rhs.value;
                                Ok(Rc::new(IntegerObj::new(value).into()))
                            }
                            InfixOp::Mul => {
                                let value = lhs.value * rhs.value;
                                Ok(Rc::new(IntegerObj::new(value).into()))
                            }
                            InfixOp::Div => {
                                let value = lhs.value / rhs.value;
                                Ok(Rc::new(IntegerObj::new(value).into()))
                            }
                        }
                    }
                    _ => Err(CodeGenError::InvalidInfixOperation {
                        span: infix.span(),
                        reason: "type of lhs and rhs is different"
                    })
                }
            }
        }
    }
}
