#![allow(dead_code)]

pub mod ast;

use crate::{lexer::token::Token, parser::ast::{Assign, CurrAddr}};
use self::ast::{Program, Statement, Identifier, Expression, Infix, Prefix};
use std::{error::Error, cell::Cell, rc::Rc};
use thiserror::Error;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum OperatorOrder {
    Lowest,
    Sum,
    Product,
    Prefix, // '#', '@'
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("Failed to get current tokne: {msg}")]
    FailedToGetCurrToken{ msg: String },
    #[error("Unexpected token found: {msg}")]
    UnexpectedTokenFound{ msg: String },
}

pub struct Parser<'a> {
    token: Vec<Token<'a>>,
    curr:  Cell<usize>,
}

impl<'a> Parser<'a> {
    pub fn new(token: Vec<Token<'a>>) -> Parser<'a> {
        Parser { token, curr: Cell::new(0) }
    }

    /// Construct program from Vec<Token>
    pub fn parse(&self) -> Result<Program, Box<dyn Error>> {
        let mut body = Vec::new();
        while !self.curr_token_is(Token::Eof) {
            body.push(self.statement()?);
            self.next_token();
        }
        Ok(Program::new(body))
    }
}

impl<'a> Parser<'a> {
    fn statement(&self) -> Result<Statement, Box<dyn Error>> {
        match self.curr_token().expect("err: stmt") {
            // Assing
            Token::Ident { .. } => {
                let ident = self.identifier();
                if self.peek_token_is(Token::Colon) {
                    self.next_token();
                    return Ok(Assign::new(ident?, CurrAddr::new().wrapping()).wrapping());
                }
                if self.peek_token_is(Token::Assign) {
                    self.next_token();
                    return Ok(Assign::new(ident?, self.expression(OperatorOrder::Lowest)?).wrapping());
                }
                Err(ParseError::UnexpectedTokenFound { msg: "".to_string() })? }
            _ => todo!()
        }
    }

    /// Assume that current token is Token::Ident and return Identifier
    /// If current token is empty or not Token::Ident, return Error
    fn identifier(&self) -> Result<Identifier, Box<dyn Error>> {
        let name = match self.curr_token().ok_or(ParseError::FailedToGetCurrToken { msg: "".to_string() })? {
            Token::Ident { literal } => literal,
            _ => Err(ParseError::UnexpectedTokenFound { msg: "".to_string() })?,
        };
        Ok(Identifier::new(name))
    }

    fn expression(&self, order: OperatorOrder) -> Result<Expression, Box<dyn Error>> {
        let mut left = match self.peek_token().unwrap() {
            // Prefix
            Token::Sharp | Token::AtSign => self.prefix()?.wrapping(),
            Token::Ident { .. }          => self.identifier()?.wrapping(),
            _ => todo!(),
        };

        while !self.peek_token_is(Token::Eof) && order < self.peek_order() {
            match self.peek_token().unwrap() {
                Token::Plus
                | Token::Minus
                | Token::Star
                | Token::Slash => {
                    self.next_token();
                    left = self.infix(left)?.wrapping();
                }
                _ => return Ok(left),
            }
        }

        Ok(left)
    }

    fn prefix(&self) -> Result<Prefix, Box<dyn Error>> {
        let op   = self.peek_token().unwrap();
        self.next_token();
        let expr = self.expression(OperatorOrder::Prefix)?; 
        Ok(Prefix::new(op, Rc::new(expr)))
    }

    fn infix(&'a self, left: Expression<'a>) -> Result<Infix<'a>, Box<dyn Error>> {
        let op = self.curr_token().unwrap();
        let order = self.curr_order();
        self.next_token();
        let right = self.expression(order)?;
        Ok(Infix::new(op, Rc::new(left), Rc::new(right)))
    }
}

/// Helper functions
impl<'a> Parser<'a> {
    fn curr_token(&self) -> Option<Token> {
        match self.token.get(self.curr.get() + 0) {
            Some(token) => Some(*token),
            None => None,
        }
    }

    fn peek_token(&self) -> Option<Token> {
        match self.token.get(self.curr.get() + 1) {
            Some(token) => Some(*token),
            None => None,
        }
    }

    fn curr_token_is(&self, token: Token) -> bool {
        match self.curr_token() {
            Some(target) => target == token,
            None => false
        }
    }

    fn peek_token_is(&self, token: Token) -> bool {
        match self.peek_token() {
            Some(target) => target == token,
            None => false
        }
    }

    fn token_to_order(token: Token) -> OperatorOrder {
        match token {
            Token::Plus | Token::Minus => OperatorOrder::Sum,
            Token::Star | Token::Slash => OperatorOrder::Product,
            _ => OperatorOrder::Lowest,
        }
    }

    fn curr_order(&self) -> OperatorOrder {
        let token = match self.curr_token() {
            Some(token) => token,
            None => return OperatorOrder::Lowest,
        };
        Self::token_to_order(token)
    }

    fn peek_order(&self) -> OperatorOrder {
        let token = match self.peek_token() {
            Some(token) => token,
            None => return OperatorOrder::Lowest,
        };
        Self::token_to_order(token)
    }

    fn next_token(&self) {
        if self.token.len() > self.curr.get() {
            self.curr.set(self.curr.get() + 1);
        }
    }
}
