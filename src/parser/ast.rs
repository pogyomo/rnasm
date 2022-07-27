#![allow(dead_code)]

use crate::lexer::token::Token;

use std::rc::Rc;

/// Set of statements
pub struct Program<'a> {
    body: Vec<Statement<'a>>,
}

impl<'a> Program<'a> {
    pub fn new(body: Vec<Statement>) -> Program {
        Program { body }
    }
}

/// I immetate the inheritance of OOP by wrapping structs.
/// Using this method, I can downcast Statement into these structs
/// by using match (It is easier than the downcast of trait).
pub enum Statement<'a> {
    Assign(Assign<'a>),
}

/// e.g. "label:" or "label = 10"
pub struct Assign<'a> {
    ident: Identifier,
    expr:  Expression<'a>,
}

impl<'a> Assign<'a> {
    pub fn new(ident: Identifier, expr: Expression) -> Assign {
        Assign { ident, expr }
    }

    pub fn wrapping(self) -> Statement<'a> {
        Statement::Assign(self)
    }
}

/// I use same method to represent Expression and whose children
pub enum Expression<'a> {
    /// Literals
    Identifier(Identifier),
    Integer(Integer),
    CurrAddr(CurrAddr),

    /// Operators
    Prefix(Prefix<'a>),
    Infix(Infix<'a>),
}

/// e.g. "label_with_underline", "camelCaseLabel"
pub struct Identifier {
    name: String,
}

impl<'a> Identifier {
    pub fn new(name: String) -> Identifier {
        Identifier { name }
    }

    pub fn wrapping(self) -> Expression<'a> {
        Expression::Identifier(self)
    }
}

// Kind of integer (Operand of 6502 is either 8-bit, 16-bit or none)
pub enum IntegerKind {
    /// 8-bit integer
    Byte,
    /// 16-bit integer
    Word
}

/// Integer literal
pub struct Integer {
    value: u16,
    kind:  IntegerKind
}

impl<'a> Integer {
    pub fn new(value: u16, kind: IntegerKind) -> Integer {
        Integer { value, kind }
    }

    pub fn wrapping(self) -> Expression<'a> {
        Expression::Integer(self)
    }
}

/// When I process "label:", I need to store the current address
/// to the identifier. But While constructiong ast, the parser can't
/// get the address, so there is no field.
/// (Get the address in next process: assemble)
pub struct CurrAddr;

impl<'a> CurrAddr {
    pub fn new() -> CurrAddr {
        CurrAddr {}
    }

    pub fn wrapping(self) -> Expression<'a> {
        Expression::CurrAddr(self)
    }
}

/// e.g. "#$00", "@(labe + 3)"
pub struct Prefix<'a> {
    op: Token<'a>,
    expr: Rc<Expression<'a>>,
}

impl<'a> Prefix<'a> {
    pub fn new(op: Token<'a>, expr: Rc<Expression<'a>>) -> Prefix<'a> {
        Prefix { op, expr }
    }

    pub fn wrapping(self) -> Expression<'a> {
        Expression::Prefix(self)
    }
}

/// e.g. "1 + 2", "1 / (2 + 3)" ..
pub struct Infix<'a> {
    op: Token<'a>,
    lhs_expr: Rc<Expression<'a>>,
    rhs_expr: Rc<Expression<'a>>,
}

impl<'a> Infix<'a> {
    pub fn new(
        op: Token<'a>,
        lhs_expr: Rc<Expression<'a>>,
        rhs_expr: Rc<Expression<'a>>
    ) -> Infix<'a> {
        Infix { op, lhs_expr, rhs_expr }
    }

    pub fn wrapping(self) -> Expression<'a> {
        Expression::Infix(self)
    }
}
