#![allow(dead_code)]

use std::ops::{Add, Sub, Mul, Div, Shl, Shr};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Object {
    Integer(Integer),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum IntKind {
    /// value as u8
    Lsb,
    /// (value >> 8) as u8
    Msb,
    /// value
    Word,
}

impl IntKind {
    fn mixing(self, rhs: Self) -> Self {
        if self == IntKind::Word && rhs == IntKind::Word {
            IntKind::Word
        } else {
            IntKind::Lsb
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Integer {
    pub value: u16,
    pub kind:  IntKind,
}

impl Integer {
    pub fn new(value: u16, kind: IntKind) -> Integer {
        Integer { value, kind }
    }

    pub fn wrapping(self) -> Object {
        Object::Integer(self)
    }

    fn conv(&self) -> u16 {
        match self.kind {
            IntKind::Lsb  => self.value & 0x00FF,
            IntKind::Msb  => self.value.wrapping_shr(8),
            IntKind::Word => self.value,
        }
    }
}

impl Add for Integer {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_add(rhs.conv());
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}

impl Sub for Integer {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_sub(rhs.conv());
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}

impl Mul for Integer {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_mul(rhs.conv());
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}

impl Div for Integer {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_div(rhs.conv());
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}

impl Shl for Integer {
    type Output = Self;
    fn shl(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_shl(rhs.conv() as u32);
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}

impl Shr for Integer {
    type Output = Self;
    fn shr(self, rhs: Self) -> Self::Output {
        let value = self.conv().wrapping_shr(rhs.conv() as u32);
        let kind  = self.kind.mixing(rhs.kind);
        Integer::new(value, kind)
    }
}
