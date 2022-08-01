#![allow(dead_code)]

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
}
