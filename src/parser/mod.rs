// Memo:
//  At the begin of all function, current token must be unused token,
// and previous token must be used token.
//  At the end of all function, next token must be unused token,
// and current token must be used token.
// 
// Memo:
//  Is there any way to remove (stop to use) self.back_token?

pub mod ast;
mod order;

use std::cell::Cell;
use std::rc::Rc;
use crate::lexer::token::{TokenList, Token, IntBase};
use crate::inst::Mnemonic;
use ast::{Program, Statement, Expression, Assign, Identifier, Instruction, PrefixOp, Prefix};
use ast::{UncertainAddrMode, Integer, CurrAddr, EmptyExpr, InfixOp, Infix};
use order::Order;
use anyhow::{Result, anyhow, Context, bail};

pub struct Parser<'a> {
    /// List of Token that parser use.
    token: &'a TokenList<'a>,

    /// Position of token that is currently used by parser.
    curr_pos: Cell<usize>,
}

impl<'a> Parser<'a> {
    pub fn new(token: &'a TokenList<'a>) -> Parser<'a> {
        Parser { token, curr_pos: Cell::new(0) }
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
    fn statement(&self) -> Result<Statement> {
        match self.curr_token()? {
            Token::Ident { literal } => {
                self.next_token();
                self.assign(literal.to_string())
            }
            Token::Mnemonic { kind } => {
                self.next_token();
                self.instruction(*kind)
            }
            token => Err(anyhow!("There is no statement that start with {:?}", token)),
        }
    }
}

impl<'a> Parser<'a> {
    /// Assign expression to identifier
    ///
    /// 'label:' or 'label = <expression>'
    fn assign(&self, name: String) -> Result<Statement> {
        let expr = match self.curr_token()? {
            Token::Assign => {
                self.next_token();
                self.expression(Order::Lowest)?
            }
            token => {
                if *token != Token::Colon {
                    self.back_token(); // TODO: This operation may be removable
                }
                CurrAddr::new().wrapping()
            }
        };
        Ok(Assign::new(Identifier::new(name), expr).wrapping())
    }
}

impl<'a> Parser<'a> {
    /// Get expression with addressing mode
    fn instruction(&self, kind: Mnemonic) -> Result<Statement> {
        match self.curr_token()? {
            Token::RegisterA => {
                let expr = EmptyExpr::new().wrapping();
                Ok(Instruction::new(kind, UncertainAddrMode::Accumulator, expr).wrapping())
            }
            Token::Sharp => {
                self.next_token();
                let expr = self.expression(Order::Lowest)?;
                let expr = Prefix::new(PrefixOp::TakeLSB, Rc::new(expr)).wrapping();
                Ok(Instruction::new(kind, UncertainAddrMode::Immediate, expr).wrapping())
            }
            Token::AtSign => {
                self.next_token();
                let expr = self.expression(Order::Lowest)?;
                Ok(Instruction::new(kind, UncertainAddrMode::Relative, expr).wrapping())
            }
            Token::LSquare => {
                self.next_token();
                self.indirect(kind)
            }
            _ => {
                self.other_inst(kind)
            }
        }
    }

    fn indirect(&self, kind: Mnemonic) -> Result<Statement> {
        let expr = self.expression(Order::Lowest)?;

        // Eiter indirect or indirect-y
        if self.expect_peek(&Token::RSquare) {
            if !self.expect_peek(&Token::Comma) {
                return Ok(Instruction::new(kind, UncertainAddrMode::Indirect,  expr).wrapping());
            }

            if self.curr_token_is(&Token::Comma) && self.peek_token_is(&Token::RegisterY) {
                self.next_token();
                let expr = Prefix::new(PrefixOp::TakeLSB, Rc::new(expr)).wrapping();
                return Ok(Instruction::new(kind, UncertainAddrMode::IndirectY, expr).wrapping());
            } else {
                return Err(anyhow!("Invalid operand that start with '['"));
            }
        }

        // Or, indirect-x
        if !self.expect_peek(&Token::Comma) {
            bail!("Invalid operand that start with '['")
        }
        if !self.expect_peek(&Token::RegisterX) {
            bail!("Invalid operand that start with '['")
        }
        if !self.expect_peek(&Token::RSquare) {
            bail!("Invalid operand that start with '['")
        }
        let expr = Prefix::new(PrefixOp::TakeLSB, Rc::new(expr)).wrapping();
        Ok(Instruction::new(kind, UncertainAddrMode::IndirectX, expr).wrapping())
    }

    /// Absolute(x, y) or ZeroPage(x, y)
    fn other_inst(&self, kind: Mnemonic) -> Result<Statement> {
        let expr = self.expression(Order::Lowest)?;

        // If there is no expression in operand, this addressing mod is implied
        // and return early.
        match expr {
            Expression::EmptyExpr(_) => {
                self.back_token();
                return Ok(Instruction::new(kind, UncertainAddrMode::Implied, expr).wrapping());
            }
            _ => (),
        }

        // In this time, I don't know the length of operand, so I temporary defined
        // that addressing mode is absolute(none or X or Y).
        if !self.expect_peek(&Token::Comma) {
            let mode = UncertainAddrMode::AbsoluteOrZeroPage;
            return Ok(Instruction::new(kind, mode, expr).wrapping());
        }
        if self.expect_peek(&Token::RegisterX) {
            let mode = UncertainAddrMode::AbsoluteXOrZeroPageX;
            return Ok(Instruction::new(kind, mode, expr).wrapping());
        }
        if self.expect_peek(&Token::RegisterY) {
            let mode = UncertainAddrMode::AbsoluteYOrZeroPageY;
            return Ok(Instruction::new(kind, mode, expr).wrapping());
        }
        Err(anyhow!("Missing register: expect x or y"))
    }
}

impl<'a> Parser<'a> {
    // In the end of this function, the next token must be unused.
    fn expression(&self, order: Order) -> Result<Expression> {
        let mut left = match self.curr_token()? {
            // Literal
            Token::Ident { literal }     => self.identifier(literal)?.wrapping(),
            Token::Int { literal, base } => self.integer(literal, *base)?.wrapping(),

            // Prefix
            Token::LTSign => self.prefix(PrefixOp::TakeLSB)?,
            Token::GTSign => self.prefix(PrefixOp::TakeMSB)?,

            // '(' <expression> ')'
            Token::LParen => self.group()?,

            // No expression
            _ => return Ok(EmptyExpr::new().wrapping()),
        };

        while order < self.peek_order().unwrap_or(Order::Lowest) {
            match self.peek_token()? {
                // Infix operator
                Token::Plus => {
                    self.next_token();
                    left = self.infix(left, InfixOp::Add)?;
                }
                Token::Minus => {
                    self.next_token();
                    left = self.infix(left, InfixOp::Sub)?;
                }
                Token::Star => {
                    self.next_token();
                    left = self.infix(left, InfixOp::Mul)?;
                }
                Token::Slash => {
                    self.next_token();
                    left = self.infix(left, InfixOp::Div)?;
                }
                Token::LShift => {
                    self.next_token();
                    left = self.infix(left, InfixOp::LShift)?;
                }
                Token::RShift => {
                    self.next_token();
                    left = self.infix(left, InfixOp::RShift)?;
                }

                // No operator
                _ => return Ok(left),
            }
        }
        Ok(left)
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

        match u16::from_str_radix(value.as_str(), base) {
            Ok(value) => Ok(Integer::new(value)),
            Err(err)  => Err(err).with_context(|| format!("Integer must be less than 0xFFFF"))?,
        }
    }

    fn prefix(&self, op: PrefixOp) -> Result<Expression> {
        let order = self.curr_order()?;
        self.next_token();
        let right = self.expression(order)?;
        Ok(Prefix::new(op, Rc::new(right)).wrapping())
    }

    fn infix(&self, left: Expression, op: InfixOp) -> Result<Expression> {
        let order = self.curr_order()?;
        self.next_token();
        let right = self.expression(order)?;
        Ok(Infix::new(op, Rc::new(left), Rc::new(right)).wrapping())
    }

    fn group(&self) -> Result<Expression> {
        self.next_token();
        let expr = self.expression(Order::Lowest)?;
        if !self.expect_peek(&Token::RParen) {
            Err(anyhow!("A group have to end with ')'"))
        } else {
            Ok(expr)
        }
    }
}

impl<'a> Parser<'a> {
    /// Get current token. If it failed, return error
    fn curr_token(&self) -> Result<&Token> {
        match self.token.body.get(self.curr_pos.get() + 0) {
            Some(token) => Ok(token),
            None => Err(anyhow!("Failed to read curr token: pos {}", self.curr_pos.get())),
        }
    }

    /// Get next token. If it failed, return error
    fn peek_token(&self) -> Result<&Token> {
        match self.token.body.get(self.curr_pos.get() + 1) {
            Some(token) => Ok(token),
            None => Err(anyhow!("Failed to read next token: pos {}", self.curr_pos.get())),
        }
    }

    fn curr_token_is(&self, token: &Token) -> bool {
        use std::mem;
        match self.curr_token() {
            Ok(val) => mem::discriminant(val) == mem::discriminant(token),
            Err(_)  => false,
        }
    }

    fn peek_token_is(&self, token: &Token) -> bool {
        use std::mem;
        match self.peek_token() {
            Ok(val) => mem::discriminant(val) == mem::discriminant(token),
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

    /// Get given token's order
    fn token_order(token: &Token) -> Order {
        match token {
            Token::LTSign | Token::GTSign => Order::TakeByte,
            Token::Plus   | Token::Minus  => Order::AddAndSub,
            Token::Star   | Token::Slash  => Order::MulAndDiv,
            Token::LShift | Token::RShift => Order::Shift,
            _ => Order::Lowest,
        }
    }

    /// Get current token's order
    fn curr_order(&self) -> Result<Order> {
        Ok(Parser::token_order(self.curr_token()?))
    }

    /// Get next token's order
    fn peek_order(&self) -> Result<Order> {
        Ok(Parser::token_order(self.peek_token()?))
    }

    fn back_token(&self) {
        if self.curr_pos.get() > 0 {
            self.curr_pos.set(self.curr_pos.get() - 1);
        }
    }

    fn next_token(&self) {
        if self.token.body.len() - 1 > self.curr_pos.get() {
            self.curr_pos.set(self.curr_pos.get() + 1);
        }
    }
}
