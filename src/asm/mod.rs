#![allow(dead_code)]

use std::cell::Cell;
use crate::inst::{Instruction, AddrMode};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct InstList {
    addr: u16,
    body: Vec<Instruction>,
}

impl InstList {
    pub fn new(addr: u16, body: Vec<Instruction>) -> InstList {
        InstList { addr, body }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Object {
    pub addr: u16,
    pub prog: Vec<u8>,
}

impl Object {
    pub fn new(addr: u16, prog: Vec<u8>) -> Object {
        Object { addr, prog }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Assembler<'a> {
    list: &'a InstList,
    curr_addr: Cell<u16>,
    curr_pos:  Cell<usize>,
}

impl<'a> Assembler<'a> {
    /// Create assembler
    pub fn new(list: &'a InstList) -> Assembler<'a> {
        Assembler {
            list,
            curr_addr: Cell::new(list.addr),
            curr_pos:  Cell::new(0),
        }
    }

    /// Assemble the list of instruction
    pub fn assemble(&self) -> Option<Object> {
        let mut body = Vec::new();
        while self.curr_pos.get() < self.list.body.len() {
            let inst  = self.curr_inst()?;
            println!("{:?}", inst);
            println!("{:?}", inst.byte());
            println!("{:?}", inst.len());

            body.push(inst.byte()?);
            match inst.mode {
                AddrMode::Accumulator
                | AddrMode::Implied => (),
                AddrMode::Absolute(field)
                | AddrMode::AbsoluteX(field)
                | AddrMode::AbsoluteY(field)
                | AddrMode::Indirect(field) => {
                    let bytes = field.to_le_bytes();
                    body.push(bytes[0]);
                    body.push(bytes[1]);
                }
                AddrMode::Immediate(field)
                | AddrMode::IndirectX(field)
                | AddrMode::IndirectY(field)
                | AddrMode::ZeroPage(field)
                | AddrMode::ZeroPageX(field)
                | AddrMode::ZeroPageY(field) => {
                    body.push(field);
                }
                AddrMode::Relative(field) => {
                    let next = self.curr_addr.get() + inst.len()?;
                    let byte = self.take_diff(field, next)?;
                    body.push(byte);
                }
            }

            self.next_inst();
            self.move_addr(inst.len()?);
        }
        Some(Object::new(self.list.addr, body))
    }
}

impl<'a> Assembler<'a> {
    /// Get current instruction
    fn curr_inst(&self) -> Option<&Instruction> {
        self.list.body.get(self.curr_pos.get())
    }

    /// Move on to the next instruction
    fn next_inst(&self) {
        self.curr_pos.set(self.curr_pos.get() + 1);
    }

    /// Increase current address by given integer
    fn move_addr(&self, diff: u16) {
        self.curr_addr.set(self.curr_addr.get().wrapping_add(diff));
    }

    /// Calculete n1 - n2 and return it as 2's complement if possible
    fn take_diff(&self, n1: u16, n2: u16) -> Option<u8> {
        if n1 > n2 {
            let diff = n1 - n2;
            if diff <= 127 {
                Some(diff as u8)
            } else {
                None
            }
        } else {
            let diff = n2 - n1;
            if diff <= 128 {
                Some(!(diff as u8) + 1)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::inst::*;
    use crate::asm::*;

    #[test]
    fn test_all_addrmode() {
        let insts = vec![
            Instruction::new(Mnemonic::Asl, AddrMode::Accumulator),
            Instruction::new(Mnemonic::Lda, AddrMode::Absolute(0x0123)),
            Instruction::new(Mnemonic::Lda, AddrMode::AbsoluteX(0x0123)),
            Instruction::new(Mnemonic::Lda, AddrMode::AbsoluteY(0x0123)),
            Instruction::new(Mnemonic::Lda, AddrMode::Immediate(0x23)),
            Instruction::new(Mnemonic::Clc, AddrMode::Implied),
            Instruction::new(Mnemonic::Jmp, AddrMode::Indirect(0x0123)),
            Instruction::new(Mnemonic::Lda, AddrMode::IndirectX(0x23)),
            Instruction::new(Mnemonic::Lda, AddrMode::IndirectY(0x23)),
            Instruction::new(Mnemonic::Bne, AddrMode::Relative(0x0000)),
            Instruction::new(Mnemonic::Lda, AddrMode::ZeroPage(0x23)),
            Instruction::new(Mnemonic::Lda, AddrMode::ZeroPageX(0x23)),
            Instruction::new(Mnemonic::Ldx, AddrMode::ZeroPageY(0x23)),
        ];
        let tests = vec![
            0x0A, 0xAD, 0x23, 0x01, 0xBD, 0x23, 0x01, 0xB9,
            0x23, 0x01, 0xA9, 0x23, 0x18, 0x6C, 0x23, 0x01,
            0xA1, 0x23, 0xB1, 0x23, 0xD0, 0xEA, 0xA5, 0x23,
            0xB5, 0x23, 0xB6, 0x23,
        ];
        let bytes = Assembler::new(&InstList::new(0, insts)).assemble();
        assert_eq!(0,     bytes.as_ref().unwrap().addr);
        assert_eq!(tests, bytes.as_ref().unwrap().prog);
    }

    #[test]
    fn test_invalid_addrmode() {
        let insts = vec![
            Instruction::new(Mnemonic::Lda, AddrMode::ZeroPageY(0x23)),
        ];
        let bytes = Assembler::new(&InstList::new(0, insts)).assemble();
        assert_eq!(None, bytes);
    }
}
