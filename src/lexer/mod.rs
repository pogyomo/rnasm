pub mod token;

use std::cell::Cell;
use std::collections::HashMap;

use self::token::{TokenList, Token, IntBase};
use crate::inst::Mnemonic;

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

    /// Construct Vec<Token> from input
    pub fn tokenize(&'a self) -> TokenList<'a> {
        let mut ret = Vec::new();
        while let Some(token) = self.token() {
            ret.push(token);
        }
        ret.push(Token::Eof);
        TokenList::new(ret)
    }
}

impl<'a> Lexer<'a> {
    fn token(&'a self) -> Option<Token<'a>> {
        self.trim_start_with(|c| c.is_ascii_whitespace());
        match self.curr_char()? {
            '=' => {
                self.next_char();
                Some(Token::Assign)
            }
            '<' => {
                self.next_char();
                Some(Token::LTSign)
            }
            '>' => {
                self.next_char();
                Some(Token::GTSign)
            }
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
                if self.peek_char_is(|c| c == '/') {
                    // Trim command such that '// --comment--'
                    self.trim_start_with(|c| c != '\n');
                    self.token()
                } else {
                    self.next_char();
                    Some(Token::Slash)
                }
            }
            '#' => {
                self.next_char();
                Some(Token::Sharp)
            }
            '@' => {
                self.next_char();
                Some(Token::AtSign)
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
            // Registers
            ret.insert("a",   Token::RegisterA);
            ret.insert("x",   Token::RegisterX);
            ret.insert("y",   Token::RegisterY);

            // Mnemonic
            ret.insert("adc", Token::Mnemonic { kind: Mnemonic::Adc } );
            ret.insert("and", Token::Mnemonic { kind: Mnemonic::And } );
            ret.insert("asl", Token::Mnemonic { kind: Mnemonic::Asl } );
            ret.insert("bcc", Token::Mnemonic { kind: Mnemonic::Bcc } );
            ret.insert("bcs", Token::Mnemonic { kind: Mnemonic::Bcs } );
            ret.insert("beq", Token::Mnemonic { kind: Mnemonic::Beq } );
            ret.insert("bit", Token::Mnemonic { kind: Mnemonic::Bit } );
            ret.insert("bmi", Token::Mnemonic { kind: Mnemonic::Bmi } );
            ret.insert("bne", Token::Mnemonic { kind: Mnemonic::Bne } );
            ret.insert("bpl", Token::Mnemonic { kind: Mnemonic::Bpl } );
            ret.insert("brk", Token::Mnemonic { kind: Mnemonic::Brk } );
            ret.insert("bvc", Token::Mnemonic { kind: Mnemonic::Bvc } );
            ret.insert("bvs", Token::Mnemonic { kind: Mnemonic::Bvs } );
            ret.insert("clc", Token::Mnemonic { kind: Mnemonic::Clc } );
            ret.insert("cld", Token::Mnemonic { kind: Mnemonic::Cld } );
            ret.insert("cli", Token::Mnemonic { kind: Mnemonic::Cli } );
            ret.insert("clv", Token::Mnemonic { kind: Mnemonic::Clv } );
            ret.insert("cmp", Token::Mnemonic { kind: Mnemonic::Cmp } );
            ret.insert("cpx", Token::Mnemonic { kind: Mnemonic::Cpx } );
            ret.insert("cpy", Token::Mnemonic { kind: Mnemonic::Cpy } );
            ret.insert("dec", Token::Mnemonic { kind: Mnemonic::Dec } );
            ret.insert("dex", Token::Mnemonic { kind: Mnemonic::Dex } );
            ret.insert("dey", Token::Mnemonic { kind: Mnemonic::Dey } );
            ret.insert("eor", Token::Mnemonic { kind: Mnemonic::Eor } );
            ret.insert("inc", Token::Mnemonic { kind: Mnemonic::Inc } );
            ret.insert("inx", Token::Mnemonic { kind: Mnemonic::Inx } );
            ret.insert("iny", Token::Mnemonic { kind: Mnemonic::Iny } );
            ret.insert("jmp", Token::Mnemonic { kind: Mnemonic::Jmp } );
            ret.insert("jsr", Token::Mnemonic { kind: Mnemonic::Jsr } );
            ret.insert("lda", Token::Mnemonic { kind: Mnemonic::Lda } );
            ret.insert("ldx", Token::Mnemonic { kind: Mnemonic::Ldx } );
            ret.insert("ldy", Token::Mnemonic { kind: Mnemonic::Ldy } );
            ret.insert("lsr", Token::Mnemonic { kind: Mnemonic::Lsr } );
            ret.insert("nop", Token::Mnemonic { kind: Mnemonic::Nop } );
            ret.insert("ora", Token::Mnemonic { kind: Mnemonic::Ora } );
            ret.insert("pha", Token::Mnemonic { kind: Mnemonic::Pha } );
            ret.insert("php", Token::Mnemonic { kind: Mnemonic::Php } );
            ret.insert("pla", Token::Mnemonic { kind: Mnemonic::Pla } );
            ret.insert("plp", Token::Mnemonic { kind: Mnemonic::Plp } );
            ret.insert("rol", Token::Mnemonic { kind: Mnemonic::Rol } );
            ret.insert("ror", Token::Mnemonic { kind: Mnemonic::Ror } );
            ret.insert("rti", Token::Mnemonic { kind: Mnemonic::Rti } );
            ret.insert("rts", Token::Mnemonic { kind: Mnemonic::Rts } );
            ret.insert("sbc", Token::Mnemonic { kind: Mnemonic::Sbc } );
            ret.insert("sec", Token::Mnemonic { kind: Mnemonic::Sec } );
            ret.insert("sed", Token::Mnemonic { kind: Mnemonic::Sed } );
            ret.insert("sei", Token::Mnemonic { kind: Mnemonic::Sei } );
            ret.insert("sta", Token::Mnemonic { kind: Mnemonic::Sta } );
            ret.insert("stx", Token::Mnemonic { kind: Mnemonic::Stx } );
            ret.insert("sty", Token::Mnemonic { kind: Mnemonic::Sty } );
            ret.insert("tax", Token::Mnemonic { kind: Mnemonic::Tax } );
            ret.insert("tay", Token::Mnemonic { kind: Mnemonic::Tay } );
            ret.insert("tsx", Token::Mnemonic { kind: Mnemonic::Tsx } );
            ret.insert("txa", Token::Mnemonic { kind: Mnemonic::Txa } );
            ret.insert("txs", Token::Mnemonic { kind: Mnemonic::Txs } );
            ret.insert("tya", Token::Mnemonic { kind: Mnemonic::Tya } );
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
    /// Get integer token from current input
    fn integer(&'a self, radix: u32) -> Option<Token<'a>> {
        let cond = |c: char| c.is_digit(radix) || c == '_';
        match radix {
            02 => Some(Token::Int {
                literal: self.trim_start_with(cond),
                base: IntBase::Binary
            }),
            08 => Some(Token::Int {
                literal: self.trim_start_with(cond),
                base: IntBase::Octal
            }),
            10 => Some(Token::Int {
                literal: self.trim_start_with(cond), 
                base: IntBase::Decimal
            }),
            16 => Some(Token::Int {
                literal: self.trim_start_with(cond),
                base: IntBase::Hexadecimal
            }),

            // I add this statement because the match have to cover all integer.
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
