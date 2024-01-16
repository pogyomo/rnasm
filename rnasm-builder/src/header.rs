use derive_new::new;
use rnasm_codegen::Mirror;

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct HeaderBuilder {
    #[new(value = "0")]
    prgrom_size: u16,
    #[new(value = "0")]
    chrrom_size: u16,
    #[new(value = "0")]
    mapper: u16,
    #[new(value = "0")]
    submapper: u8,
    #[new(default)]
    mirror: Mirror,
}

impl HeaderBuilder {
    pub fn build(self) -> [u8; 16] {
        use Mirror::*;

        let mut header = [0; 16];

        // Write magic number
        header[0] = 0x4E;
        header[1] = 0x45;
        header[2] = 0x53;
        header[3] = 0x1A;
        header[7] = 0x08;

        // Write prg-rom size
        let [lsb, msb] = self.prgrom_size.to_le_bytes();
        header[4] = lsb;
        header[9] |= msb & 0x0F;

        // Write chr-rom size
        let [lsb, msb] = self.chrrom_size.to_le_bytes();
        header[5] = lsb;
        header[9] |= msb.wrapping_shl(4);

        // Write mapper number
        let [lhs, msb] = self.mapper.to_le_bytes();
        header[6] |= lhs.wrapping_shl(4);
        header[7] |= lsb & 0xF0;
        header[8] |= msb & 0x0F;

        // Write submapper number
        header[8] |= self.submapper.wrapping_shl(4);

        // Write mirroring
        header[6] &= 0xF6; // Clear mirroring bits.
        header[6] |= match self.mirror {
            HorizontalOrMapperControlled => 0x00,
            Vertical => 0x01,
            ForuScreen => 0x08,
        };

        header
    }
}

impl HeaderBuilder {
    /// Set program rom size. This must be from 0 to 0xEFF.
    /// If size exceed the range, size will be 0xEFF; the upper bound.
    pub fn prgrom(mut self, size: u16) -> Self {
        if size > 0xEFF {
            self.prgrom_size = 0xEFF;
        } else {
            self.prgrom_size = size;
        }
        self
    }

    /// Set character rom size. This must be from 0 to 0xEFF.
    /// If size exceed the range, size will be 0xEFF; the upper bound.
    pub fn chrrom(mut self, size: u16) -> Self {
        if size > 0xEFF {
            self.chrrom_size = 0xEFF;
        } else {
            self.chrrom_size = size;
        }
        self
    }

    /// Set mapper number. This must be from 0 to 0xFFF.
    /// If number exceed the range, number will be 0xFFF; the upper bound.
    pub fn mapper(mut self, number: u16) -> Self {
        if number > 0xFFF {
            self.mapper = 0xFFF;
        } else {
            self.mapper = number;
        }
        self
    }

    /// Set submapper number. This must be from 0 to 0xF.
    /// If number exceed the range, number will be 0xF; the upper bound.
    pub fn submapper(mut self, number: u8) -> Self {
        if number > 0xF {
            self.submapper = 0xF;
        } else {
            self.submapper = number;
        }
        self
    }

    /// Set mirroring method.
    pub fn mirror(mut self, mirror: Mirror) -> Self {
        self.mirror = mirror;
        self
    }
}
