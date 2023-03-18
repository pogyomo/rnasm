//! Provide functional to convert input into list of token.

use thiserror::Error;
use nonempty::NonEmpty;
use derive_new::new;
use std::num::ParseIntError;
use rnasm_token::{Token, TokenKind};
use rnasm_span::{Span, Spannable};

/// An error which can be returned when lexing input.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum LexerError {
    #[error("unexpected character found")]
    UnexpectedCharacter{ span: Span },
    #[error("failed to parse integer: {reason}")]
    FailedToParseInteger{ span: Span, reason: ParseIntError },
}

impl Spannable for LexerError {
    fn span(&self) -> Span {
        use LexerError::*;
        match *self {
            UnexpectedCharacter { span } => span,
            FailedToParseInteger { span, .. } => span,
        }
    }
}

/// Struct to construct the list of token.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lexer {
    input: Vec<(usize, char)>
}

impl Lexer {
    /// Construct `Lexer` from input.
    pub fn new<S: AsRef<str>>(input: S) -> Self {
        Self {
            input: input.as_ref().char_indices().collect()
        }
    }

    /// Construct list of token by consuming itself.
    pub fn lex(self) -> Result<Vec<Token>, Vec<LexerError>> {
        match NonEmpty::from_vec(self.input) {
            Some(vec) => NonEmptyLexer::new(vec).lex(),
            None => Ok(Vec::new()),
        }
    }
}

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NonEmptyLexer {
    input: NonEmpty<(usize, char)>,
    #[new(value = "0")]
    position: usize,
}

impl NonEmptyLexer {
    fn lex(mut self) -> Result<Vec<Token>, Vec<LexerError>> {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();
        while let Some(token) = self.token() {
            match token {
                Ok(token) => tokens.push(token),
                Err(error) => errors.push(error),
            }
        }
        if errors.len() == 0 {
            Ok(tokens)
        } else {
            Err(errors)
        }
    }
}

impl NonEmptyLexer {
    /// Create token and advance position.
    fn token(&mut self) -> Option<Result<Token, LexerError>> {
        // Skip whitespaces
        while self.consume('\x09') || self.consume('\x20') {}

        // Skip comment
        if let Some(ch) = self.peek() {
            if ch == ';' {
                while let Some(ch) = self.next() {
                    if ch == '\n' {
                        break;
                    }
                }
            }
        }

        if let Some(token) = self.integer() {
            match token {
                Ok(token) => return Some(Ok(token)),
                Err(error) => return Some(Err(error)),
            }
        }

        if let Some(token) = self.symbol() {
            return Some(Ok(token));
        }

        let offset = self.offset();
        let kind = match self.next()? {
            '+'  => TokenKind::Plus,
            '-'  => TokenKind::Minus,
            '*'  => TokenKind::Star,
            '/'  => TokenKind::Slash,
            '.'  => TokenKind::Period,
            ','  => TokenKind::Comma,
            ':'  => TokenKind::Colon,
            '#'  => TokenKind::Sharp,
            '>'  => TokenKind::LT,
            '<'  => TokenKind::GT,
            '['  => TokenKind::LSquare,
            ']'  => TokenKind::RSquare,
            '('  => TokenKind::LParen,
            ')'  => TokenKind::RParen,
            '\n' => TokenKind::NewLine,
            _ => {
                let span = Span::new(offset, self.offset() - offset);
                return Some(Err(LexerError::UnexpectedCharacter { span }))
            }
        };
        let span = Span::new(offset, self.offset() - offset);
        Some(Ok(Token::new(span, kind)))
    }
}

impl NonEmptyLexer {
    /// Try to create integer token. If success, advance position.
    fn integer(&mut self) -> Option<Result<Token, LexerError>> {
        let offset = self.offset();
        let position = self.position;

        // Consume prefix and return the associated radix.
        let radix = if self.consume('0') {
            if self.consume('x') {
                16
            } else if self.consume('b') {
                2
            } else {
                8
            }
        } else if self.consume('$') {
            16
        } else if self.consume('%') {
            2
        } else {
            10
        };

        // If radix is 8 and current character is not a digit, the
        // consumed '0' is a decimal integer.
        match self.peek() {
            Some(ch) => {
                if !ch.is_digit(radix) && radix == 8 {
                    let span = Span::new(offset, self.offset() - offset);
                    let kind = TokenKind::Integer(0);
                    return Some(Ok(Token::new(span, kind)));
                } else if !ch.is_digit(radix) {
                    self.position = position;
                    return None;
                }
            }
            None => {
                if radix == 8 {
                    let span = Span::new(offset, self.offset() - offset);
                    let kind = TokenKind::Integer(0);
                    return Some(Ok(Token::new(span, kind)));
                } else {
                    self.position = position;
                    return None;
                }
            },
        }

        let mut body = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_digit(radix) {
                body.push(ch);
                self.next();
            } else {
                break;
            }
        }

        let span = Span::new(offset, self.offset() - offset);
        match u16::from_str_radix(body.as_str(), radix) {
            Ok(value) => {
                let kind = TokenKind::Integer(value);
                Some(Ok(Token::new(span, kind)))
            }
            Err(e) => {
                Some(Err(LexerError::FailedToParseInteger {
                    span,
                    reason: e
                }))
            }
        }
    }
}

impl NonEmptyLexer {
    /// Try to create symbol token. If success, advance position.
    fn symbol(&mut self) -> Option<Token> {
        let offset = self.offset();

        match self.peek() {
            Some(ch) if ch.is_ascii_alphabetic() || ch == '_' => (),
            _ => return None,
        }

        let mut body = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '.') {
                body.push(ch);
                self.next();
            } else {
                break;
            }
        }

        let span = Span::new(offset, self.offset() - offset);
        let kind = match body.as_str() {
            "a" | "A" => TokenKind::RegisterA,
            "x" | "X" => TokenKind::RegisterX,
            "y" | "Y" => TokenKind::RegisterY,
            _ => TokenKind::Symbol(body),
        };
        Some(Token::new(span, kind))
    }
}

impl NonEmptyLexer {
    /// Return current character's start offset.
    /// If no character available, return input's length.
    fn offset(&self) -> usize {
        match self.input.get(self.position) {
            Some(item) => item.0,
            None => {
                self.input.last().0 + self.input.last().1.len_utf8()
            }
        }
    }

    /// Return current character without advance position.
    fn peek(&self) -> Option<char> {
        Some(self.input.get(self.position)?.1)
    }

    /// Return current character, then advance position.
    fn next(&mut self) -> Option<char> {
        let ch = self.peek();
        self.position += 1;
        ch
    }

    /// If current character is given character, advance position.
    fn consume(&mut self, ch: char) -> bool {
        match self.peek() {
            Some(target) if target == ch => {
                self.next();
                true
            }
            _ => false
        }
    }
}
