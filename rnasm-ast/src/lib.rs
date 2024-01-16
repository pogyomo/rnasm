//! Abstract syntax tree of the source code.

use derive_new::new;
use nonempty::NonEmpty;
use rnasm_span::{Span, Spannable};

macro_rules! impl_convert {
    ($target:ident, $($source:ident),*) => {$(
        impl From<$source> for $target {
            fn from(source: $source) -> $target {
                $target::$source(source)
            }
        }
    )*};
}

impl_convert!(Statement, LabelStatement, InstStatement, LabelInstStatement);

// We use enum instead of holding optional label and instructioin because
// if both label and instruction become None, this doesn't become Spannable.
// We want **all** element of ast to be `Spannable`, so I use enum.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Statement {
    LabelStatement(LabelStatement),
    InstStatement(InstStatement),
    LabelInstStatement(LabelInstStatement),
}

impl Spannable for Statement {
    fn span(&self) -> Span {
        use Statement::*;
        match self {
            LabelStatement(stmt) => stmt.span(),
            InstStatement(stmt) => stmt.span(),
            LabelInstStatement(stmt) => stmt.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LabelStatement {
    pub label: Label,
}

impl Spannable for LabelStatement {
    fn span(&self) -> Span {
        self.label.span()
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstStatement {
    pub inst: Instruction,
}

impl Spannable for InstStatement {
    fn span(&self) -> Span {
        self.inst.span()
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LabelInstStatement {
    pub label: Label,
    pub inst: Instruction,
}

impl Spannable for LabelInstStatement {
    fn span(&self) -> Span {
        self.label.span() + self.inst.span()
    }
}

impl_convert!(Label, GlobalLabel, LocalLabel);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Label {
    GlobalLabel(GlobalLabel),
    LocalLabel(LocalLabel),
}

impl Spannable for Label {
    fn span(&self) -> Span {
        use Label::*;
        match self {
            GlobalLabel(label) => label.span(),
            LocalLabel(label) => label.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GlobalLabel {
    span: Span,
    pub name: String,
}

impl Spannable for GlobalLabel {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalLabel {
    span: Span,
    pub name: String,
}

impl Spannable for LocalLabel {
    fn span(&self) -> Span {
        self.span
    }
}

impl_convert!(Instruction, PseudoInstruction, ActualInstruction);

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instruction {
    PseudoInstruction(PseudoInstruction),
    ActualInstruction(ActualInstruction),
}

impl Spannable for Instruction {
    fn span(&self) -> Span {
        use Instruction::*;
        match self {
            PseudoInstruction(inst) => inst.span(),
            ActualInstruction(inst) => inst.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PseudoInstruction {
    pub name: InstName,
    pub operand: Option<PseudoOperand>,
}

impl Spannable for PseudoInstruction {
    fn span(&self) -> Span {
        match &self.operand {
            Some(operand) => self.name.span() + operand.span(),
            None => self.name.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ActualInstruction {
    pub name: InstName,
    pub operand: Option<ActualOperand>,
}

impl Spannable for ActualInstruction {
    fn span(&self) -> Span {
        match &self.operand {
            Some(operand) => self.name.span() + operand.span(),
            None => self.name.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstName {
    span: Span,
    pub name: String,
}

impl Spannable for InstName {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PseudoOperand {
    pub args: NonEmpty<Expression>,
}

impl PseudoOperand {
    pub fn new(head: Expression, tail: Vec<Expression>) -> Self {
        Self {
            args: NonEmpty { head, tail },
        }
    }
}

impl Spannable for PseudoOperand {
    fn span(&self) -> Span {
        let mut span = self.args.first().span();
        for expr in self.args.tail().iter() {
            span = span + expr.span();
        }
        span
    }
}

impl_convert!(
    ActualOperand,
    Accumulator,
    AbsoluteOrRelative,
    Immediate,
    Indirect,
    Zeropage
);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualOperand {
    Accumulator(Accumulator),
    AbsoluteOrRelative(AbsoluteOrRelative),
    Immediate(Immediate),
    Indirect(Indirect),
    Zeropage(Zeropage),
}

impl Spannable for ActualOperand {
    fn span(&self) -> Span {
        use ActualOperand::*;
        match self {
            Accumulator(acc) => acc.span(),
            AbsoluteOrRelative(aor) => aor.span(),
            Immediate(imm) => imm.span(),
            Indirect(ind) => ind.span(),
            Zeropage(zpg) => zpg.span(),
        }
    }
}

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Accumulator {
    span: Span,
}

impl Spannable for Accumulator {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbsoluteOrRelative {
    span: Span,
    pub expr: Expression,
    pub register: Option<IndexableRegister>,
}

impl Spannable for AbsoluteOrRelative {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Immediate {
    span: Span,
    pub cast: CastStrategy,
    pub expr: Expression,
}

impl Spannable for Immediate {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Indirect {
    span: Span,
    pub cast: Option<CastStrategy>,
    pub expr: Expression,
    pub register: Option<IndexableRegister>,
}

impl Spannable for Indirect {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Zeropage {
    span: Span,
    pub cast: CastStrategy,
    pub expr: Expression,
    pub register: Option<IndexableRegister>,
}

impl Spannable for Zeropage {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IndexableRegister {
    X,
    Y,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CastStrategy {
    Lsb,
    Msb,
}

impl_convert!(Expression, Surrounded, Integer, Symbol, StringExpr, InfixExpr);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expression {
    Surrounded(Surrounded),
    Integer(Integer),
    Symbol(Symbol),
    StringExpr(StringExpr),
    InfixExpr(InfixExpr),
}

impl Spannable for Expression {
    fn span(&self) -> Span {
        use Expression::*;
        match self {
            Surrounded(expr) => expr.span(),
            Integer(expr) => expr.span(),
            Symbol(expr) => expr.span(),
            StringExpr(expr) => expr.span(),
            InfixExpr(expr) => expr.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Surrounded {
    span: Span,
    pub expr: Box<Expression>,
}

impl Spannable for Surrounded {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Integer {
    span: Span,
    pub value: u16,
}

impl Spannable for Integer {
    fn span(&self) -> Span {
        self.span
    }
}

impl_convert!(Symbol, GlobalSymbol, LocalSymbol);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Symbol {
    GlobalSymbol(GlobalSymbol),
    LocalSymbol(LocalSymbol),
}

impl Spannable for Symbol {
    fn span(&self) -> Span {
        use Symbol::*;
        match self {
            GlobalSymbol(symbol) => symbol.span(),
            LocalSymbol(symbol) => symbol.span(),
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GlobalSymbol {
    span: Span,
    pub name: String,
}

impl Spannable for GlobalSymbol {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalSymbol {
    span: Span,
    pub name: String,
}

impl Spannable for LocalSymbol {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StringExpr {
    span: Span,
    pub value: String,
}

impl Spannable for StringExpr {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InfixExpr {
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
    pub op: InfixOp,
}

impl Spannable for InfixExpr {
    fn span(&self) -> Span {
        self.lhs.span() + self.rhs.span()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InfixOp {
    /// +
    Add,
    /// -
    Sub,
    /// *
    Mul,
    /// /
    Div,
}
