use std::collections::HashSet;

use derive_new::new;
use thiserror::Error;

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuilderError {
    #[error("{byte:02X} already exist at ${address:04X}")]
    ByteAlreadyExist { address: u16, byte: u8 }
}

/// Create a ines rom
#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Builder {
    codes: Vec<(u16, Vec<u8>)>
}

impl Builder {
    pub fn build(self) -> Result<Vec<u8>, BuilderError> {
        let mut rom = Vec::new();
        rom.append(&mut vec![
            0x4E, 0x45, 0x53, 0x1A,
            0x01,
            0x00,
            0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00
        ]);
        let mut map = HashSet::new();
        let mut prg = [0; 0x8000];
        for code in self.codes.iter() {
            for (byte, offset) in code.1.iter().zip(0..) {
                if !map.insert(code.0 + offset) {
                    return Err(BuilderError::ByteAlreadyExist {
                        address: code.0 + offset, byte: *byte
                    })
                };
                let address = (code.0 + offset) as usize;
                prg[address - 0x8000] = *byte;
            }
        }
        rom.append(&mut prg.to_vec());
        Ok(rom)
    }
}
