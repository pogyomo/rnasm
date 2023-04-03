use derive_new::new;
use thiserror::Error;
use std::{rc::Rc, collections::HashMap, fs::File, io::Read};
use rnasm_ast::{
    Statement, Instruction, Label, PseudoInstruction, ActualInstruction,
    GlobalLabel, LocalLabel, Expression, InfixOp, CastStrategy
};
use rnasm_opcode::{Mnemonic, Opcode, OpcodeByteLen, AddrMode};
use rnasm_span::{Span, Spannable};
use object::{StringObj, IntegerObj, Object};
use opcode::{operand_to_addrmode, operand_to_cast, operand_to_expr};
use symtable::SymbolTable;

mod object;
mod opcode;
mod symtable;

#[derive(Debug, Error)]
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
    InvalidNumberOfArguments { span: Span, expect: &'static str, got: usize },
    #[error("invalid type of arguemnt: expect {expect}")]
    InvalidTypeOfArgument { span: Span, expect: &'static str },
    #[error("invalid value of arguemnt: expect {expect}")]
    InvalidValueOfArgument { span: Span, expect: &'static str },
    #[error("invalid infix operation: {reason}")]
    InvalidInfixOperation { span: Span, reason: &'static str },
    #[error("relative can't indexing with register")]
    RelativeCantIndexing { span: Span },
    #[error("relative exceed range: must be from -128 to 127")]
    RelativeExceedRange { span: Span },
    #[error("failed to open file: {reason}")]
    FailedToOpneFile { span: Span, reason: std::io::Error },
    #[error("failed to read file: {reason}")]
    FailedToReadFile { span: Span, reason: std::io::Error },
    #[error("file too big to use")]
    FileTooBig { span: Span },
    #[error("current address ${address:04X} is small on current bank")]
    AddressIsSmall { span: Span, address: u16 },
    #[error("need .pbank or .cbank before this")]
    NeedBankSwitch { span: Span },
    #[error("indirect can't use < or > to its expression")]
    IndirectCantUseCast { span: Span },
    #[error("multiple call of .pbankdef to the bank number")]
    MultipleCallOfPBankDef { span: Span },
    #[error("multiple call of .cbankdef to the bank number")]
    MultipleCallOfCBankDef { span: Span },
    #[error("target bytes is too long to write on current bank")]
    TargetBytesIsTooLong { span: Span },
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
            InvalidValueOfArgument { span, .. } => span,
            InvalidInfixOperation { span, .. } => span,
            RelativeCantIndexing { span } => span,
            RelativeExceedRange { span } => span,
            FailedToOpneFile { span, .. } => span,
            FailedToReadFile { span, .. } => span,
            FileTooBig { span } => span,
            AddressIsSmall { span, .. } => span,
            NeedBankSwitch { span } => span,
            IndirectCantUseCast { span } => span,
            MultipleCallOfPBankDef { span } => span,
            MultipleCallOfCBankDef { span } => span,
            TargetBytesIsTooLong { span } => span,
        }
    }
}

/// A generated code.
#[derive(new)]
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Code {
    #[new(default)]
    pub prgs: HashMap<u16, BankData>, // Bank to program
    #[new(default)]
    pub chrs: HashMap<u16, BankData>, // Bank to character
    #[new(value = "0")]
    pub mapper: u16,
    #[new(value = "0")]
    pub submapper: u8,
    #[new(default)]
    pub mirror: Mirror,
}

// Mirroring
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mirror {
    #[default]
    HorizontalOrMapperControlled,
    Vertical,
    ForuScreen,
}

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BankData {
    pub base: u16, // Lowest address of this bank.
    #[new(default)]
    pub data: Vec<(u16, Vec<u8>)>, // data.0 + base is actual address of the data.
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
    curr_label: Option<String>, // Current label if exist.
    #[new(value = "0")]
    curr_prg_bank: u16, // Current bank number
    #[new(value = "0")]
    curr_chr_bank: u16, // Current bank number
    #[new(value = "true")]
    curr_is_prg: bool, // True if .pbank is more recently used than .cbank
}

/// A struct which generate prg and chr codes from given statements.
#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeGen {
    #[new(default)]
    info: CodeGenInfo,

    #[new(default)]
    symtable: SymbolTable,

    #[new(default)]
    code: Code,
}

impl CodeGen {
    pub fn gen(mut self, stmts: Vec<Statement>) -> Result<Code, CodeGenError> {
        self.info = CodeGenInfo::new(true);
        for stmt in stmts.iter() {
            self.statement(stmt)?;
        }
        self.info = CodeGenInfo::new(false);
        for stmt in stmts.iter() {
            self.statement(stmt)?;
        }
        Ok(self.code)
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
            "db" => self.db(pseudo),
            "dw" => self.dw(pseudo),
            "pbank" => self.pbank(pseudo),
            "pbankdef" => self.pbankdef(pseudo),
            "cbank" => self.cbank(pseudo),
            "cbankdef" => self.cbankdef(pseudo),
            "inesmap" => self.inesmap(pseudo),
            "inessmap" => self.inessmap(pseudo),
            "inesmir" => self.inesmir(pseudo),
            "incbin" => self.incbin(pseudo),
            "equ" => self.equ(pseudo),
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
            let cast = match operand_to_cast(actual.operand.as_ref()) {
                Some(_) if matches!(addrmode, AddrMode::Indirect) => {
                    // If the statement is like jmp [<expr] or jmp [>expr],
                    // this is invalid.
                    return Err(CodeGenError::IndirectCantUseCast {
                        span: actual.span()
                    })
                }
                Some(cast) => cast,
                None => CastStrategy::Lsb,
            };
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

            let span = actual.span();
            if mnemonic.is_relative() {
                if self.info.address + 2 < value {
                    if value - self.info.address - 2 <= 127 {
                        let diff = (value - self.info.address - 2) as u8;
                        self.write(vec![byte, diff], span)?;
                    } else {
                        return Err(CodeGenError::RelativeExceedRange {
                            span
                        });
                    }
                } else {
                    if self.info.address + 2 - value <= 128 {
                        let diff = (self.info.address + 2 - value) as u8;
                        self.write(vec![byte, (!diff).wrapping_add(1)], span)?;
                    } else {
                        return Err(CodeGenError::RelativeExceedRange {
                            span
                        });
                    }
                }
            } else {
                match opcode.to_byte_len() {
                    OpcodeByteLen::One => self.write(vec![byte], span)?,
                    OpcodeByteLen::Two => match cast {
                        CastStrategy::Lsb => {
                            self.write(vec![byte, value.to_le_bytes()[0]], span)?;
                        }
                        CastStrategy::Msb => {
                            self.write(vec![byte, value.to_le_bytes()[1]], span)?;
                        }
                    }
                    OpcodeByteLen::Three => {
                        let value = value.to_le_bytes();
                        self.write(vec![byte, value[0], value[1]], span)?;
                    }
                }
            }
        } else {
            let len = <OpcodeByteLen as Into<u16>>::into(opcode.to_byte_len());
            self.info.address = self.info.address.wrapping_add(len);
        }
        Ok(())
    }

    fn global_label(&mut self, label: &GlobalLabel) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            if self.symtable.add(
                label.name.clone(),
                Rc::new(IntegerObj::new(self.info.address).into())
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
                Rc::new(IntegerObj::new(self.info.address).into())
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
    /// Change current address.
    fn org(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
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

    /// Write bytes.
    fn db(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if let Some(ref operand) = pseudo.operand {
            for arg in operand.args.iter() {
                if !self.info.is_pass1 {
                    let value = match *self.eval(arg)? {
                        Object::IntegerObj(int) => int.value,
                        _ => return Err(CodeGenError::InvalidTypeOfArgument {
                            span: arg.span(),
                            expect: "integer"
                        })
                    };
                    self.write(vec![value.to_le_bytes()[0]], pseudo.span())?;
                } else {
                    self.info.address = self.info.address.wrapping_add(1);
                }
            }
        }
        Ok(())
    }

    // Write words.
    fn dw(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if let Some(ref operand) = pseudo.operand {
            for arg in operand.args.iter() {
                if !self.info.is_pass1 {
                    let value = match *self.eval(arg)? {
                        Object::IntegerObj(int) => int.value,
                        _ => return Err(CodeGenError::InvalidTypeOfArgument {
                            span: arg.span(),
                            expect: "integer"
                        })
                    };
                    self.write(value.to_le_bytes().to_vec(), pseudo.span())?;
                } else {
                    self.info.address = self.info.address.wrapping_add(2);
                }
            }
        }
        Ok(())
    }

    /// Change current program bank.
    fn pbank(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            return Ok(())
        }

        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() > 2 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let bank = match *self.eval(&operand.args[0])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };

        self.info.curr_prg_bank = bank;
        self.info.curr_is_prg = true;
        Ok(())
    }

    /// Define the program bank's base address.
    fn pbankdef(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            return Ok(())
        }

        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: 0
            })
        };
        if operand.args.len() != 2 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: operand.args.len()
            })
        }

        let bank = match *self.eval(&operand.args[0])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        let base = match *self.eval(&operand.args[1])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };

        if self.code.prgs.insert(bank, BankData::new(base)).is_some() {
            Err(CodeGenError::MultipleCallOfPBankDef {
                span: pseudo.span()
            })
        } else {
            Ok(())
        }
    }

    /// Change current character bank.
    fn cbank(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            return Ok(())
        }

        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() > 2 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let bank = match *self.eval(&operand.args[0])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };

        self.info.curr_chr_bank = bank;
        self.info.curr_is_prg = false;
        Ok(())
    }

    /// Define the character bank's base address.
    fn cbankdef(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        if self.info.is_pass1 {
            return Ok(())
        }

        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: 0
            })
        };
        if operand.args.len() != 2 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: operand.args.len()
            })
        }

        let bank = match *self.eval(&operand.args[0])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        let base = match *self.eval(&operand.args[1])? {
            Object::IntegerObj(value) => value.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };

        if self.code.chrs.insert(bank, BankData::new(base)).is_some() {
            Err(CodeGenError::MultipleCallOfCBankDef {
                span: pseudo.span()
            })
        } else {
            Ok(())
        }
    }

    fn inesmap(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let value = match *self.eval(operand.args.first())? {
            Object::IntegerObj(int) => int.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        self.code.mapper = value;
        Ok(())
    }

    fn inessmap(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let value = match *self.eval(operand.args.first())? {
            Object::IntegerObj(int) => int.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        self.code.submapper = value as u8;
        Ok(())
    }

    fn inesmir(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let value = match *self.eval(operand.args.first())? {
            Object::IntegerObj(int) => int.value,
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "integer"
            })
        };
        self.code.mirror = match value {
            0 => Mirror::HorizontalOrMapperControlled,
            1 => Mirror::Vertical,
            2 => Mirror::ForuScreen,
            _ => return Err(CodeGenError::InvalidValueOfArgument {
                span: operand.args.first().span(),
                expect: "0, 1 or 2"
            })
        };
        Ok(())
    }

    fn incbin(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: 0
            })
        };
        if operand.args.len() != 1 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "1",
                got: operand.args.len()
            })
        }

        let name = match *self.eval(operand.args.first())? {
            Object::StringObj(ref str) => str.value.clone(),
            _ => return Err(CodeGenError::InvalidTypeOfArgument {
                span: operand.args.first().span(),
                expect: "string"
            })
        };
        let mut file = match File::open(name) {
            Ok(file) => file,
            Err(e) => return Err(CodeGenError::FailedToOpneFile {
                span: operand.args.first().span(),
                reason: e
            })
        };
        let mut bytes = Vec::new();
        match file.read_to_end(&mut bytes) {
            Ok(_) => (),
            Err(e) => return Err(CodeGenError::FailedToReadFile {
                span: operand.args.first().span(),
                reason: e
            })
        }
        let len = if bytes.len() > 0xFFFF {
            return Err(CodeGenError::FileTooBig {
                span: operand.args.first().span()
            })
        } else {
            bytes.len() as u16
        };
        if !self.info.is_pass1 {
            self.write(bytes, pseudo.span())?;
        } else {
            self.info.address = self.info.address.wrapping_add(len);
        }
        Ok(())
    }

    fn equ(&mut self, pseudo: &PseudoInstruction) -> Result<(), CodeGenError> {
        let Some(ref operand) = pseudo.operand else {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: 0
            })
        };
        if operand.args.len() != 2 {
            return Err(CodeGenError::InvalidNumberOfArguments {
                span: pseudo.span(),
                expect: "2",
                got: operand.args.len()
            })
        }

        if self.info.is_pass1 {
            let name = match operand.args.first() {
                Expression::Symbol(symbol) => match symbol {
                    rnasm_ast::Symbol::GlobalSymbol(symbol) => {
                        symbol.name.clone()
                    }
                    _ => return Err(CodeGenError::InvalidTypeOfArgument {
                        span: operand.args.first().span(),
                        expect: "global symbol"
                    })
                }
                _ => return Err(CodeGenError::InvalidTypeOfArgument {
                    span: operand.args.first().span(),
                    expect: "global symbol"
                })
            };
            let value = self.eval(&operand.args[1])?;
            if self.symtable.add(name, value) {
                return Err(CodeGenError::SymbolAlreadyExist {
                    span: operand.args.first().span()
                })
            };
        }
        Ok(())
    }
}

impl CodeGen {
    /// Write bytes to current address then advance the address.
    fn write(&mut self, bytes: Vec<u8>, span: Span) -> Result<(), CodeGenError> {
        let data = if self.info.curr_is_prg {
            match self.code.prgs.get_mut(&self.info.curr_prg_bank) {
                Some(prg) => prg,
                None => return Err(CodeGenError::NeedBankSwitch {
                    span
                }),
            }
        } else {
            match self.code.chrs.get_mut(&self.info.curr_chr_bank) {
                Some(chr) => chr,
                None => return Err(CodeGenError::NeedBankSwitch {
                    span
                }),
            }
        };
        let len = if bytes.len() > u16::MAX as usize {
            return Err(CodeGenError::TargetBytesIsTooLong { span })
        } else if self.info.address as usize + bytes.len() > data.base as usize + 0x4000 {
            return Err(CodeGenError::TargetBytesIsTooLong { span })
        } else {
            bytes.len()
        };
        let relative_addr = if self.info.address < data.base {
            return Err(CodeGenError::AddressIsSmall {
                span, address: self.info.address
            })
        } else {
            self.info.address - data.base
        };
        data.data.push((relative_addr, bytes));

        self.info.address = self.info.address.wrapping_add(len as u16);
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
