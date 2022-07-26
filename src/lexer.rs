#![allow(dead_code)]

use std::cell::Cell;
use std::collections::HashMap;

use crate::token::{Token, IntBase, Mnemonic, RegKind};

use once_cell::sync::Lazy;

pub struct Lexer<'a> {
    input: Cell<&'a str>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Lexer<'a> {
        Lexer {
            input: Cell::new(input),
        }
    }

    pub fn tokenize(&'a self) -> Vec<Token<'a>> {
        let mut ret = Vec::new();
        while let Some(token) = self.token() {
            ret.push(token);
        }
        ret.push(Token::Eof);
        ret
    }
}

impl<'a> Lexer<'a> {
    fn token(&'a self) -> Option<Token<'a>> {
        self.trim_start_with(|c| c.is_ascii_whitespace());
        match self.curr_char()? {
            '+' => {
                self.next_char();
                Some(Token::Plus)
            }
            '-' => {
                self.next_char();
                Some(Token::Minus)
            }
            '*' => {
                self.next_char();
                Some(Token::Star)
            }
            '/' => {
                self.next_char();
                Some(Token::Slash)
            }
            '#' => {
                self.next_char();
                Some(Token::Slash)
            }
            '$' => {
                self.next_char();
                if self.curr_char_is(|c| c.is_ascii_hexdigit()) {
                    return self.integer(16)
                } else {
                    Some(Token::Dollar)
                }
            }
            '%' => {
                self.next_char();
                if self.curr_char_is(|c| c.is_digit(2)) {
                    return self.integer(2)
                } else {
                    Some(Token::Percent)
                }
            }
            ',' => {
                self.next_char();
                Some(Token::Comma)
            }
            ':' => {
                self.next_char();
                Some(Token::Colon)
            }
            '.' => {
                self.next_char();
                Some(Token::Dot)
            }
            '(' => {
                self.next_char();
                Some(Token::LParen)
            }
            ')' => {
                self.next_char();
                Some(Token::RParen)
            }
            '{' => {
                self.next_char();
                Some(Token::LCurly)
            }
            '}' => {
                self.next_char();
                Some(Token::RCurly)
            }
            '[' => {
                self.next_char();
                Some(Token::LSquare)
            }
            ']' => {
                self.next_char();
                Some(Token::RSquare)
            }
            ch if ch.is_ascii_alphabetic() => {
                return self.ident_or_keyword();
            }
            ch if ch.is_ascii_digit() => {
                if ch == '0' {
                    if self.peek_char_is(|c| c == 'x') {
                        self.next_char();
                        self.next_char();
                        return self.integer(16);
                    }
                    if self.peek_char_is(|c| c == 'o') {
                        self.next_char();
                        self.next_char();
                        return self.integer(08);
                    }
                    if self.peek_char_is(|c| c == 'b') {
                        self.next_char();
                        self.next_char();
                        return self.integer(02);
                    }
                    return self.integer(08);
                } else {
                    return self.integer(10);
                }
            }
            ch => {
                self.next_char();
                Some(Token::Invalid { ch })
            }
        }
    }
}

impl<'a> Lexer<'a> {
    fn ident_or_keyword(&'a self) -> Option<Token<'a>> {
        static KEYWORD: Lazy<HashMap<&str, Token>> = Lazy::new(|| {
            let mut ret = HashMap::new();
            ret.insert("a",   Token::Register{ kind: RegKind::A    });
            ret.insert("x",   Token::Register{ kind: RegKind::X    });
            ret.insert("y",   Token::Register{ kind: RegKind::Y    });
            ret.insert("adc", Token::Mnemonic{ kind: Mnemonic::Adc });
            ret
        });

        let literal = self.trim_start_with(|c: char| c.is_ascii_alphanumeric() || c == '_');

        match KEYWORD.get(literal.to_lowercase().as_str()) {
            Some(token) => Some(*token),
            None => Some(Token::Ident { literal }),
        }
    }
}

impl<'a> Lexer<'a> {
    fn integer(&'a self, radix: u32) -> Option<Token<'a>> {
        let cond = |c: char| c.is_digit(radix) || c == '_';
        match radix {
            02 => Some(Token::Int { literal: self.trim_start_with(cond), base: IntBase::Binary }),
            08 => Some(Token::Int { literal: self.trim_start_with(cond), base: IntBase::Octal }),
            10 => Some(Token::Int { literal: self.trim_start_with(cond), base: IntBase::Decimal}),
            16 => Some(Token::Int { literal: self.trim_start_with(cond), base: IntBase::Hexadecimal}),
            _  => None,
        }
    }
}

/// Helper functions
impl<'a> Lexer<'a> {
    fn curr_char(&self) -> Option<char> {
        self.input.get().chars().nth(0)
    }

    fn peek_char(&self) -> Option<char> {
        self.input.get().chars().nth(1)
    }

    fn curr_char_is<F>(&self, cond: F) -> bool
    where
        F: Fn(char) -> bool
    {
        if let Some(ch) = self.curr_char() {
            cond(ch)
        } else {
            false
        }
    }

    fn peek_char_is<F>(&self, cond: F) -> bool
    where
        F: Fn(char) -> bool
    {
        if let Some(ch) = self.peek_char() {
            cond(ch)
        } else {
            false
        }
    }

    fn next_char(&self) {
        let mut chars = self.input.get().chars();
        chars.next();
        self.input.set(chars.as_str());
    }

    fn trim_start_with<F>(&'a self, f: F) -> &'a str
    where
        F: Fn(char) -> bool
    {
        let input = self.input.get();
        let sep   = input.find(|c: char| !f(c)).unwrap_or(input.len());
        self.input.set(&input[sep..]);
        &input[..sep]
    }
}
