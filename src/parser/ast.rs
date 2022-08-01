use std::rc::Rc;
use std::fmt::Debug;
use crate::inst::Mnemonic;

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
        match self {
            Statement::Assign(val)      => write!(f, "{:?}", val),
            Statement::Instruction(val) => write!(f, "{:?}", val),
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
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

impl Debug for Assign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} = {:?}", self.ident, self.expr)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UncertainAddrMode {
    Accumulator,
    Immediate,
    Implied,
    Indirect,
    IndirectX,
    IndirectY,
    Relative,
    AbsoluteOrZeroPage,
    AbsoluteXOrZeroPageX,
    AbsoluteYOrZeroPageY,
}

#[derive(PartialEq, Eq, Clone)]
pub struct Instruction {
    pub kind: Mnemonic,
    pub mode: UncertainAddrMode,
    pub expr: Expression,
}

impl Instruction {
    pub fn new(kind: Mnemonic, mode: UncertainAddrMode, expr: Expression) -> Instruction {
        Instruction { kind, mode, expr }
    }

    pub fn wrapping(self) -> Statement {
        Statement::Instruction(self)
    }
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UncertainAddrMode::*;
        use UncertainAddrMode::AbsoluteOrZeroPage   as AbsOrZP;
        use UncertainAddrMode::AbsoluteXOrZeroPageX as AbsXOrZPX;
        use UncertainAddrMode::AbsoluteYOrZeroPageY as AbsYOrZPY;
        match self.mode {
            Accumulator => write!(f, "{:?} a",         self.kind),
            Immediate   => write!(f, "{:?} #{:?}",     self.kind, self.expr),
            Implied     => write!(f, "{:?} Implied",   self.kind),
            Indirect    => write!(f, "{:?} [{:?}]",    self.kind, self.expr),
            IndirectX   => write!(f, "{:?} [{:?}, x]", self.kind, self.expr),
            IndirectY   => write!(f, "{:?} [{:?}], y", self.kind, self.expr),
            Relative    => write!(f, "{:?} @{:?}",     self.kind, self.expr),
            AbsOrZP     => write!(f, "{:?} {:?}",      self.kind, self.expr),
            AbsXOrZPX   => write!(f, "{:?} {:?}",      self.kind, self.expr),
            AbsYOrZPY   => write!(f, "{:?} {:?}",      self.kind, self.expr),
        }
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
    /// e.g. '<$FF00', '>label'
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

#[derive(PartialEq, Eq, Clone)]
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

impl Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(PartialEq, Eq, Clone)]
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

impl Debug for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PrefixOp {
    /// '<'
    TakeLSB,
    /// '>'
    TakeMSB,
}

#[derive(PartialEq, Eq, Clone)]
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

impl Debug for Prefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let op = match self.op {
            PrefixOp::TakeLSB => "<",
            PrefixOp::TakeMSB => ">",
        };
        write!(f, "({}{:?})", op, self.rhs_expr)
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
    /// '<<'
    LShift,
    /// '>>'
    RShift,
}

#[derive(PartialEq, Eq, Clone)]
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

impl Debug for Infix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let op = match self.op {
            InfixOp::Add    => "+",
            InfixOp::Sub    => "-",
            InfixOp::Mul    => "*",
            InfixOp::Div    => "/",
            InfixOp::LShift => "<<",
            InfixOp::RShift => ">>",
        };
        write!(f, "({:?} {} {:?})", self.lhs_expr, op, self.rhs_expr)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct CurrAddr;

impl CurrAddr {
    pub fn new() -> CurrAddr {
        CurrAddr {}
    }

    pub fn wrapping(self) -> Expression {
        Expression::CurrAddr(self)
    }
}

impl Debug for CurrAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CurrAddr")
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct EmptyExpr;

impl EmptyExpr {
    pub fn new() -> EmptyExpr {
        EmptyExpr {}
    }

    pub fn wrapping(self) -> Expression {
        Expression::EmptyExpr(self)
    }
}

impl Debug for EmptyExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "EmptyExpr")
    }
}
