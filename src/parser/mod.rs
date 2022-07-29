// Memo: At the begin of all function, current token must be unused token,
// and previous token must be used token.
// 
// Memo: Is there any way to remove (stop to use) self.back_token?

use std::cell::Cell;
use crate::lexer::token::{Token, Mnemonic, IntBase};
use self::ast::{
    Program, Statement, Expression, Assign, Identifier, Instruction,
    AddrMode, Integer, IntegerKind, CurrAddr, EmptyExpr
};
use anyhow::{Result, anyhow};

pub mod ast;

pub struct Parser<'a> {
    /// List of Token that parser use.
    token: Vec<Token<'a>>,

    /// Position of token that is currently used by parser.
    curr: Cell<usize>,
}

impl<'a> Parser<'a> {
    pub fn new(token: Vec<Token<'a>>) -> Parser<'a> {
        Parser { token, curr: Cell::new(0) }
    }

    pub fn parse(&self) -> Result<Program> {
        let mut ret = Vec::new();
        while !self.curr_token_is(&Token::Eof) {
            ret.push(self.statement()?);
            self.next_token();
        }
        Ok(Program::new(ret))
    }
}

impl<'a> Parser<'a> {
    /// In the end of this function, the next token must be unused.
    fn statement(&self) -> Result<Statement> {
        match self.curr_token()? {
            Token::Ident { literal } => {
                self.next_token();
                self.assign(literal.to_string())
            }
            Token::Mnemonic { kind } => {
                self.next_token();
                self.instruction(kind)
            }
            token => Err(anyhow!("There is no statement that start with {:?}", token)),
        }
    }
}

impl<'a> Parser<'a> {
    fn assign(&self, name: String) -> Result<Statement> {
        let expr = match self.curr_token()? {
            Token::Assign => {
                self.next_token();
                self.expression()?
            }
            token => {
                if token != Token::Colon {
                    self.back_token(); // TODO: This operation may be removable
                }
                CurrAddr::new().wrapping()
            }
        };
        Ok(Assign::new(Identifier::new(name), expr).wrapping())
    }
}

impl<'a> Parser<'a> {
    fn instruction(&self, kind: Mnemonic) -> Result<Statement> {
        match self.curr_token()? {
            Token::RegisterA => {
                let expr = EmptyExpr::new().wrapping();
                Ok(Instruction::new(kind, AddrMode::Accumulator, expr).wrapping())
            }
            Token::Sharp => {
                self.next_token();
                let expr = self.expression()?;
                Ok(Instruction::new(kind, AddrMode::Immediate, expr).wrapping())
            }
            Token::AtSign => {
                self.next_token();
                let expr = self.expression()?;
                Ok(Instruction::new(kind, AddrMode::Relative, expr).wrapping())
            }
            Token::LSquare => self.indirect(kind),
            _ => self.absolute_or_zeropage(kind),
        }
    }

    fn indirect(&self, kind: Mnemonic) -> Result<Statement> {
        self.next_token();
        let expr = self.expression()?;

        // Eiter indirect or indirect-y
        if self.expect_peek(&Token::RSquare) {
            if !self.expect_peek(&Token::Comma) {
                return Ok(Instruction::new(kind, AddrMode::Indirect,  expr).wrapping());
            }

            if self.curr_token_is(&Token::Comma) && self.peek_token_is(&Token::RegisterY) {
                self.next_token();
                return Ok(Instruction::new(kind, AddrMode::IndirectY, expr).wrapping());
            } else {
                return Err(anyhow!("Invalid operand that start with '['"));
            }
        }

        // Or, indirect-x
        if !self.expect_peek(&Token::Comma) {
            Err(anyhow!("Invalid operand that start with '['"))?
        }
        if !self.expect_peek(&Token::RegisterX) {
            Err(anyhow!("Invalid operand that start with '['"))?
        }
        if !self.expect_peek(&Token::RSquare) {
            Err(anyhow!("Invalid operand that start with '['"))?
        }
        Ok(Instruction::new(kind, AddrMode::IndirectX, expr).wrapping())
    }

    fn absolute_or_zeropage(&self, kind: Mnemonic) -> Result<Statement> {
        let expr = self.expression()?;

        // If there is no expression in operand, this addressing mod is implied
        // and return early.
        match expr {
            Expression::EmptyExpr(_) => {
                self.back_token();
                return Ok(Instruction::new(kind, AddrMode::Implied, expr).wrapping());
            }
            _ => (),
        }

        if !self.expect_peek(&Token::Comma) {
            return Ok(Instruction::new(kind, AddrMode::AbsoluteOrZeropage, expr).wrapping());
        }

        if self.expect_peek(&Token::RegisterX) {
            return Ok(Instruction::new(kind, AddrMode::AbsoluteOrZeropageX, expr).wrapping());
        }
        if self.expect_peek(&Token::RegisterY) {
            return Ok(Instruction::new(kind, AddrMode::AbsoluteOrZeropageY, expr).wrapping());
        }
        Err(anyhow!("Missing register: expect x or y"))
    }
}

impl<'a> Parser<'a> {
    /// In the end of this function, the next token must be unused.
    fn expression(&self) -> Result<Expression> {
        match self.curr_token()? {
            Token::Ident { literal }     => Ok(self.identifier(literal)?.wrapping()),
            Token::Int { literal, base } => Ok(self.integer(literal, base)?.wrapping()),
            _ => Ok(EmptyExpr::new().wrapping())
        }
    }

    fn identifier(&self, name: &str) -> Result<Identifier> {
        Ok(Identifier::new(name.to_string()))
    }

    fn integer(&self, value: &str, base: IntBase) -> Result<Integer> {
        let value = value.chars().filter(|c| *c != '_').collect::<String>();
        let base  = match base {
            IntBase::Binary      => 2,
            IntBase::Octal       => 8,
            IntBase::Decimal     => 10,
            IntBase::Hexadecimal => 16,
        };

        match u8::from_str_radix(value.as_str(), base) {
            Ok(value) => return Ok(Integer::new(value as u16, IntegerKind::Byte)),
            Err(_) => (),
        }
        match u16::from_str_radix(value.as_str(), base) {
            Ok(value) => Ok(Integer::new(value, IntegerKind::Word)),
            Err(err)  => Err(err)?,
        }
    }
}

impl<'a> Parser<'a> {
    /// Get current token. If it failed, return error
    fn curr_token(&self) -> Result<Token> {
        match self.token.get(self.curr.get() + 0) {
            Some(token) => Ok(*token),
            None => Err(anyhow!("Failed to read curr token: pos {}", self.curr.get())),
        }
    }

    /// Get next token. If it failed, return error
    fn peek_token(&self) -> Result<Token> {
        match self.token.get(self.curr.get() + 1) {
            Some(token) => Ok(*token),
            None => Err(anyhow!("Failed to read next token: pos {}", self.curr.get())),
        }
    }

    fn curr_token_is(&self, token: &Token) -> bool {
        use std::mem;
        match self.curr_token() {
            Ok(val) => mem::discriminant(&val) == mem::discriminant(token),
            Err(_)  => false,
        }
    }

    fn peek_token_is(&self, token: &Token) -> bool {
        use std::mem;
        match self.peek_token() {
            Ok(val) => mem::discriminant(&val) == mem::discriminant(token),
            Err(_)  => false,
        }
    }

    /// If next token is expected token, return true and move the token potition +1
    /// Else, only return false
    fn expect_peek(&self, token: &Token) -> bool {
        if self.peek_token_is(token) {
            self.next_token();
            true
        } else {
            false
        }
    }

    fn back_token(&self) {
        if self.curr.get() > 0 {
            self.curr.set(self.curr.get() - 1);
        }
    }

    fn next_token(&self) {
        if self.token.len() - 1 > self.curr.get() {
            self.curr.set(self.curr.get() + 1);
        }
    }
}
