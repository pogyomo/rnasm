#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'a> {
    // Special tokne
    /// End of token
    /// Normally, this will be the end of tokens
    Eof,
    /// Invalid character
    /// Contains character that lexer can't recognized
    Invalid{ ch: char },

    // Multi-character token
    /// Identifier
    /// e.g. 'Ident_example_0000'
    Ident{ literal: &'a str },
    /// Integer literal
    /// e.g. '0xFF_FF', '0733', '%1111_1111'
    Int{ literal: &'a str, base: IntBase },

    // One-character token
    /// '='
    Assign,
    /// '+'
    Plus,
    /// '-'
    Minus,
    /// '*'
    Star,
    /// '/'
    Slash,
    /// '#'
    Sharp,
    /// '$'
    Dollar,
    /// '%'
    Percent,
    /// '@'
    AtSign,
    /// ','
    Comma,
    /// ':'
    Colon,
    /// '.'
    Dot,
    /// '('
    LParen,
    /// ')'
    RParen,
    /// '{'
    LCurly,
    /// '}'
    RCurly,
    /// '['
    LSquare,
    /// ']'
    RSquare,

    // Keyword
    /// All valid mnemonic
    Mnemonic{ kind: Mnemonic },
    /// Registers
    Register{ kind: RegKind },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mnemonic {
    Adc, And, Asl, Bcc, Bcs, Beq, Bit, Bmi, Bne, Bpl, Brk, Bvc, Bvs, Clc,
    Cld, Cli, Clv, Cmp, Cpx, Cpy, Dec, Dex, Dey, Eor, Inc, Inx, Iny, Jmp,
    Jsr, Lda, Ldx, Ldy, Lsr, Nop, Ora, Pha, Php, Pla, Plp, Rol, Ror, Rti,
    Rts, Sbc, Sec, Sed, Sei, Sta, Stx, Sty, Tax, Tay, Tsx, Txa, Txs, Tya,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntBase {
    /// Integer start with '0b' or '%'
    Binary,
    /// Integer start with '0o' or '0'
    Octal,
    /// Integer start with no prefix
    Decimal,
    /// Integer start with '0x' or '$'
    Hexadecimal
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RegKind {
    /// A register
    A,
    /// X register
    X,
    /// Y register
    Y
}
