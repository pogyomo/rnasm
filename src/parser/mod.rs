#![allow(dead_code)]

pub mod ast;

use crate::{lexer::token::Token, parser::ast::{Assign, Identifier, CurrAddr}};

use self::ast::{Program, Statement};

use std::{error::Error, cell::Cell};

pub struct Parser<'a> {
    token: Vec<Token<'a>>,
    curr:  Cell<usize>,
}

impl<'a> Parser<'a> {
    pub fn new(token: Vec<Token<'a>>) -> Parser<'a> {
        Parser { token, curr: Cell::new(0) }
    }

    /// Construct program from Vec<Token>
    pub fn parse(&self) -> Program {
        todo!()
    }
}

impl<'a> Parser<'a> {
    fn statement(&self) -> Result<Statement, Box<dyn Error>> {
        /*
        if let Some(token) = self.curr_token() {
            match token {
                Token::Ident { literal } => {
                    if self.peek_token_is(Token::Assign) {
                        self.assign(literal.to_string())
                    } else if self.peek_token_is(Token::Colon) {
                        Ok(Assign::new(
                            Identifier::new(
                                literal.to_string()
                            ),
                            CurrAddr::new().wrapping()
                        ).wrapping())
                    } else {
                        todo!()
                    }
                }
                _ => todo!()
            }
        } else {
            todo!()
        }
        */
        todo!()
    }

    fn assign(&self, name: String) -> Result<Statement, Box<dyn Error>> {
        todo!()
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
}
