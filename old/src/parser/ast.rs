use std::rc::Rc;
use std::fmt::Debug;
use crate::inst::{Mnemonic, AddrMode};

#[derive(PartialEq, Eq, Clone)]
pub struct Program {
    pub body: Vec<Statement>
}

impl Debug for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.body)
        } else {
            write!(f, "{:?}", self.body)
        }
    }
}

impl Program {
    pub fn new(body: Vec<Statement>) -> Program {
        Program { body }
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum Statement {
    Assign(Assign),
    Instruction(Instruction),
}

impl Debug for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Statement::Assign(val)      => write!(f, "{:#?}", val),
                Statement::Instruction(val) => write!(f, "{:#?}", val),
            }
        } else {
            match self {
                Statement::Assign(val)      => write!(f, "{:?}", val),
                Statement::Instruction(val) => write!(f, "{:?}", val),
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Assign {
    pub ident: Identifier,
    pub expr:  Expression,
}

impl Assign {
    pub fn new(ident: Identifier, expr: Expression) -> Assign {
        Assign { ident, expr }
    }

    pub fn wrapping(self) -> Statement {
        Statement::Assign(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Instruction {
    pub kind: Mnemonic,
    pub mode: AddrMode,
    pub expr: Expression,
}

impl Instruction {
    pub fn new(kind: Mnemonic, mode: AddrMode, expr: Expression) -> Instruction {
        Instruction { kind, mode, expr }
    }

    pub fn wrapping(self) -> Statement {
        Statement::Instruction(self)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum Expression {
    // Literal
    /// e.g. 'Label_with_underline'
    Identifier(Identifier),
    /// e.g. '10', '312'
    Integer(Integer),

    // Operators
    /// TODO: I might not implement prefix operator
    Prefix(Prefix),
    /// e.g. '5 + label', '10 / label'
    Infix(Infix),

    // Special expression
    /// Current address. This will be used at assemble part.
    CurrAddr(CurrAddr),
    /// If parser can't get expression, this will be returned.
    /// There is instructions that don't have operand, so this expression
    /// will be used to parse these instruction.
    EmptyExpr(EmptyExpr),
}

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Expression::Identifier(val) => write!(f, "{:#?}", val),
                Expression::Integer(val)    => write!(f, "{:#?}", val),
                Expression::Prefix(val)     => write!(f, "{:#?}", val),
                Expression::Infix(val)      => write!(f, "{:#?}", val),
                Expression::CurrAddr(val)   => write!(f, "{:#?}", val),
                Expression::EmptyExpr(val)  => write!(f, "{:#?}", val),
            }
        } else {
            match self {
                Expression::Identifier(val) => write!(f, "{:?}", val),
                Expression::Integer(val)    => write!(f, "{:?}", val),
                Expression::Prefix(val)     => write!(f, "{:?}", val),
                Expression::Infix(val)      => write!(f, "{:?}", val),
                Expression::CurrAddr(val)   => write!(f, "{:?}", val),
                Expression::EmptyExpr(val)  => write!(f, "{:?}", val),
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Identifier {
    pub name: String,
}

impl Identifier {
    pub fn new(name: String) -> Identifier {
        Identifier { name }
    }

    pub fn wrapping(self) -> Expression {
        Expression::Identifier(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Integer {
    pub value: u16,
}

impl Integer {
    pub fn new(value: u16) -> Integer {
        Integer { value }
    }

    pub fn wrapping(self) -> Expression {
        Expression::Integer(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PrefixOp {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Prefix {
    pub op: PrefixOp,
    pub rhs_expr: Rc<Expression>,
}

impl Prefix {
    pub fn new(op: PrefixOp, rhs_expr: Rc<Expression>) -> Prefix {
        Prefix { op, rhs_expr }
    }

    pub fn wrapping(self) -> Expression {
        Expression::Prefix(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum InfixOp {
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Infix {
    pub op: InfixOp,
    pub lhs_expr: Rc<Expression>,
    pub rhs_expr: Rc<Expression>,
}

impl Infix {
    pub fn new(op: InfixOp, lhs_expr: Rc<Expression>, rhs_expr: Rc<Expression>) -> Infix {
        Infix { op, lhs_expr, rhs_expr }
    }

    pub fn wrapping(self) -> Expression {
        Expression::Infix(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CurrAddr;

impl CurrAddr {
    pub fn new() -> CurrAddr {
        CurrAddr {}
    }

    pub fn wrapping(self) -> Expression {
        Expression::CurrAddr(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EmptyExpr;

impl EmptyExpr {
    pub fn new() -> EmptyExpr {
        EmptyExpr {}
    }

    pub fn wrapping(self) -> Expression {
        Expression::EmptyExpr(self)
    }
}
