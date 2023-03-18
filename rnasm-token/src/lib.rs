use derive_new::new;
use rnasm_span::{Span, Spannable};

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Token {
    span: Span,
    kind: TokenKind,
}

impl Token {
    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }
}

impl Spannable for Token {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenKind {
    // Special
    NewLine,

    // Literal
    Integer(u16),
    Symbol(String),

    // Keyword
    /// a | A
    RegisterA,
    /// x | X
    RegisterX,
    /// y | Y
    RegisterY,

    // One-character
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Star,
    /// /
    Slash,
    /// .
    Period,
    /// ,
    Comma,
    /// :
    Colon,
    /// #
    Sharp,
    /// <
    LT,
    /// >
    GT,
    /// [
    LSquare,
    /// ]
    RSquare,
    /// (
    LParen,
    /// )
    RParen,
}
