use derive_new::new;
use thiserror::Error;
use std::collections::HashSet;
use header::HeaderBuilder;

pub use header::HeaderMirror;

mod header;

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuilderError {
    #[error("too many prgrom unit: got {got}")]
    TooManyPrgRomUnit { got: usize },
    #[error("too many chrrom unit: got {got}")]
    TooManyChrRomUnit { got: usize },
    #[error("you can't write program to {address:04X}")]
    IncorrectPrgRomAddress { address: u16 },
    #[error("you can't write character to {address:04X}")]
    IncorrectChrRomAddress { address: u16 },
    #[error("{byte:02X} already exist at ${address:04X} of prgrom")]
    ByteAlreadyExistOnPrgRom { address: u16, byte: u8 },
    #[error("{byte:02X} already exist at ${address:04X} of chrrom")]
    ByteAlreadyExistOnChrRom { address: u16, byte: u8 },
}

/// A struct which create rom from given prgrom, chrrom and some infomation.
///
/// We expect prgrom's address is 0x8000 (0xC000) <= address <= 0xBFFF (0xFFFF)
/// and chrrom's address is 0x0000 <= address <= 0x1FFF.
#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Builder {
    prgrom: Vec<Vec<(u16, u8)>>,
    chrrom: Vec<Vec<(u16, u8)>>,
    mapper: u16,
    submapper: u8,
    mirror: HeaderMirror,
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
            let mut bytes = vec![0; 0x4000];
            for (address, byte) in prg.iter() {
                let (address, byte) = (*address, *byte);
                if !check.insert(address) {
                    return Err(BuilderError::ByteAlreadyExistOnPrgRom {
                        address, byte
                    })
                }
                if address < 0x8000 {
                    return Err(BuilderError::IncorrectPrgRomAddress {
                        address
                    })
                } else {
                    // We need convert given address into 0-based address.
                    let address = if address >= 0xC000 {
                        address - 0xC000
                    } else {
                        address - 0x8000
                    };
                    bytes[address as usize] = byte;
                }
            }
            rom.append(&mut bytes);
        }
        for chr in self.chrrom.iter() {
            let mut check = HashSet::new();
            let mut bytes = vec![0; 0x8000];
            for (address, byte) in chr.iter() {
                let (address, byte) = (*address, *byte);
                if !check.insert(address) {
                    return Err(BuilderError::ByteAlreadyExistOnChrRom {
                        address, byte
                    })
                }
                if address >= 0x2000 {
                    return Err(BuilderError::IncorrectChrRomAddress {
                        address
                    })
                } else { // 0 <= address <= 0x1FFF
                    bytes[address as usize] = byte;
                }
            }
            rom.append(&mut bytes);
        }
        Ok(rom)
    }
}
