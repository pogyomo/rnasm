use derive_new::new;
use thiserror::Error;
use std::collections::HashSet;
use header::HeaderBuilder;
use rnasm_codegen::{BankData, Mirror};

mod header;

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuilderError {
    #[error("too many prgrom unit: got {got}")]
    TooManyPrgRomUnit { got: usize },
    #[error("too many chrrom unit: got {got}")]
    TooManyChrRomUnit { got: usize },
    #[error("{byte:02X} already exist at ${address:04X} of prgrom")]
    ByteAlreadyExistOnPrgRom { address: u16, byte: u8 },
    #[error("{byte:02X} already exist at ${address:04X} of chrrom")]
    ByteAlreadyExistOnChrRom { address: u16, byte: u8 },
}

/// A struct which create rom from given prgrom, chrrom and some infomation.
#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Builder {
    prgrom: Vec<BankData>,
    chrrom: Vec<BankData>,
    mapper: u16,
    submapper: u8,
    mirror: Mirror,
}

impl Builder {
    pub fn build(self) -> Result<Vec<u8>, BuilderError> {
        let prgrom = if self.prgrom.len() > 0xEFF {
            return Err(BuilderError::TooManyPrgRomUnit {
                got: self.prgrom.len()
            })
        } else {
            self.prgrom.len() as u16
        };
        let chrrom = if self.chrrom.len() > 0xEFF {
            return Err(BuilderError::TooManyChrRomUnit {
                got: self.chrrom.len()
            })
        } else {
            self.chrrom.len() as u16
        };

        let header = HeaderBuilder::new()
            .prgrom(prgrom)
            .chrrom(chrrom)
            .mapper(self.mapper)
            .submapper(self.submapper)
            .mirror(self.mirror)
            .build();

        let mut rom = Vec::from(header);
        for prg in self.prgrom.iter() {
            let mut check = HashSet::new();
            let mut target = vec![0; 0x4000];
            for (address, bytes) in prg.data.iter() {
                for (byte, offset) in bytes.iter().zip(0..) {
                    let (address, byte) = (*address, *byte);
                    if !check.insert(address + offset) {
                        return Err(BuilderError::ByteAlreadyExistOnPrgRom {
                            address: address + offset + prg.base, byte
                        })
                    }
                    target[offset as usize + address as usize] = byte;
                }
            }
            rom.append(&mut target);
        }
        for chr in self.chrrom.iter() {
            let mut check = HashSet::new();
            let mut target = vec![0; 0x2000];
            for (address, bytes) in chr.data.iter() {
                for (byte, offset) in bytes.iter().zip(0..) {
                    let (address, byte) = (*address, *byte);
                    if !check.insert(address + offset) {
                        return Err(BuilderError::ByteAlreadyExistOnPrgRom {
                            address: address + offset + chr.base, byte
                        })
                    }
                    target[offset as usize + address as usize] = byte;
                }
            }
            rom.append(&mut target);
        }
        Ok(rom)
    }
}
