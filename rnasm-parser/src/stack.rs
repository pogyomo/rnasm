//! Provide way to store tokens in order to used.
//!
//! # `TokenStack`
//!
//! This struct will be used to store **searched** tokens.
//!
//! When we try to parse token list, we need get the span of **searched**
//! tokens because the result ast need its span.

use nonempty::NonEmpty;
use std::rc::Rc;
use rnasm_span::{Span, Spannable};
use rnasm_token::Token;

/// A struct which hold more than one token.
pub struct TokenStack {
    tokens: NonEmpty<Rc<Token>>
}

impl TokenStack {
    /// Creat a new `TokenStack` with initial value.
    pub fn new(token: Rc<Token>) -> Self {
        Self { tokens: NonEmpty::new(token) }
    }

    /// Add token to this stack.
    pub fn push(&mut self, token: Rc<Token>) {
        self.tokens.push(token);
    }

    /// Remove top of token.
    pub fn pop(&mut self) -> Option<Rc<Token>> {
        self.tokens.pop()
    }

    /// Get newly added token.
    pub fn last(&mut self) -> Rc<Token> {
        Rc::clone(self.tokens.last())
    }
}

impl Spannable for TokenStack {
    fn span(&self) -> Span {
        let mut span = self.tokens.first().span();
        for token in self.tokens.iter() {
            span = span + token.span();
        }
        span
    }
}
