//! Provide functional to parse given token list.
//!
//! # `Parser`
//!
//! This crate provide `Parser`, which get token list and parse it
//! using recursive descent parsing.
//!
//! # Strategy of parsing
//!
//! In parsing, ast need its span, so I need to hold the **searched** tokens
//! to get the span. For this, I use `TokenStack` to hold it.
//!
//! There exist mainly two pattern to search and hold tokens.
//!
//! 1. Use `next_or_err` to get token for searching token which must exist.
//! If the token is expected token, do something to the token.
//! Otherwise, throw error.
//!
//! 2. Use `peek_or_err` to get token for searching token which maybe exist.
//! If the token is expected token, advance position. Otherwise, pop the token.

use thiserror::Error;
use nonempty::NonEmpty;
use derive_new::new;
use std::rc::Rc;
use rnasm_ast::{
    Statement, Label, LocalLabel, GlobalLabel, Instruction, LabelInstStatement,
    LabelStatement, InstStatement, InstName, PseudoInstruction, PseudoOperand,
    ActualOperand, ActualInstruction, Expression, Accumulator, CastStrategy, 
    Immediate, Indirect, IndexableRegister, Zeropage, AbsoluteOrRelative,
    InfixExpr, InfixOp, Integer, Symbol, LocalSymbol, GlobalSymbol, Surrounded, StringExpr
};
use rnasm_span::{Span, Spannable};
use rnasm_token::{Token, TokenKind};
use stack::TokenStack;

mod stack;

/// An error which can be returned when parse failed.
#[derive(Debug, Error, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParserError {
    #[error("unexpected token found: expect {expect}")]
    UnexpectedTokenFound { span: Span, expect: &'static str },
    #[error("expect token, but not found: expect {expect}")]
    ExpectTokenButNotFound { span: Span, expect: &'static str },
}

impl Spannable for ParserError {
    fn span(&self) -> Span {
        use ParserError::*;
        match *self {
            UnexpectedTokenFound { span, .. } => span,
            ExpectTokenButNotFound { span, .. } => span,
        }
    }
}

/// A struct to provide functional to parse given token list.
#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Parser {
    input: Vec<Token>
}

impl Parser {
    /// Parse given token list by consuming itself.
    /// If parsing failed at more than one statement, return errors.
    pub fn parse(self) -> Result<Vec<Statement>, Vec<ParserError>> {
        // Split given token list into list of tokens where each tokens
        // represent statment.
        let inputs = self.input
            // Each statement is separated by newline.
            .split(|t| matches!(t.kind(), TokenKind::NewLine))
            .collect::<Vec<_>>();

        // Then, parser each statement.
        let mut stmts = Vec::new();
        let mut errors = Vec::new();
        for input in inputs.into_iter() {
            let input = input
                .to_vec()
                .into_iter()
                .map(|v| Rc::new(v))
                .collect::<Vec<_>>();

            match NonEmpty::from_vec(input) {
                Some(vec) => match NonEmptyParser::new(vec).parse() {
                    Ok(stmt) => match stmt {
                        Some(stmt) => stmts.push(stmt),
                        _ => (),
                    }
                    Err(err) => errors.push(err),
                },
                None => (), // When the statement is empty
            }
        }

        // If error occure more than one line, return list of error.
        if errors.len() == 0 {
            Ok(stmts)
        } else {
            Err(errors)
        }
    }
}

type ParseResult<T> = Result<T, ParserError>;

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NonEmptyParser {
    input: NonEmpty<Rc<Token>>,
    #[new(value = "0")]
    position: usize,
}

impl NonEmptyParser {
    fn parse(mut self) -> ParseResult<Option<Statement>> {
        let label = self.parse_label();
        let instruction = self.parse_instruction()?;

        match (label, instruction) {
            (Some(label), Some(instruction)) => {
                Ok(Some(LabelInstStatement::new(label, instruction).into()))
            }
            (Some(label), None) => {
                Ok(Some(LabelStatement::new(label).into()))
            }
            (None, Some(instruction)) => {
                Ok(Some(InstStatement::new(instruction).into()))
            }
            (None, None) => {
                Ok(None)
            }
        }
    }

    /// Try to extract label. Never fail.
    fn parse_label(&mut self) -> Option<Label> {
        macro_rules! peek_or_return {
            ($position:expr) => {
                match self.peek() {
                    Some(token) => token,
                    None => {
                        self.position = $position;
                        return None;
                    }
                }
            };
        }
        macro_rules! next_or_return {
            ($position:expr) => {
                match self.next() {
                    Some(token) => token,
                    None => {
                        self.position = $position;
                        return None;
                    }
                }
            };
        }

        let position = self.position;

        let mut stack = TokenStack::new(peek_or_return!(position));
        let is_local = match stack.last().kind() {
            TokenKind::Period => {
                self.next();
                true
            }
            _ => {
                stack.pop();
                false
            }
        };

        stack.push(next_or_return!(position));
        let name = match stack.last().kind() {
            TokenKind::Symbol(name) => name.clone(),
            _ => {
                self.position = position;
                return None;
            }
        };

        stack.push(next_or_return!(position));
        match stack.last().kind() {
            TokenKind::Colon => (),
            _ => {
                self.position = position;
                return None;
            }
        };

        if is_local {
            Some(LocalLabel::new(stack.span(), name).into())
        } else {
            Some(GlobalLabel::new(stack.span(), name).into())
        }
    }

    fn parse_instruction(&mut self) -> ParseResult<Option<Instruction>> {
        if self.is_eol() {
            return Ok(None);
        }

        let mut stack = TokenStack::new(self.peek_or_err(". or symbol")?);
        let is_pseudo = match stack.last().kind() {
            TokenKind::Period => {
                self.next();
                true
            }
            _ => {
                stack.pop();
                false
            }
        };

        stack.push(self.next_or_err("symbol")?);
        let name = match stack.last().kind() {
            TokenKind::Symbol(name) => name.clone(),
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "symbol"
            })
        };

        if is_pseudo {
            let operand = self.parse_pseudo_operand()?;
            let name = InstName::new(stack.span(), name);
            Ok(Some(PseudoInstruction::new(name, operand).into()))
        } else {
            let operand = self.parse_actual_operand()?;
            let name = InstName::new(stack.span(), name);
            Ok(Some(ActualInstruction::new(name, operand).into()))
        }
    }

    fn parse_pseudo_operand(&mut self) -> ParseResult<Option<PseudoOperand>> {
        if self.is_eol() {
            return Ok(None);
        }

        let head = self.parse_expression()?;
        let mut tail = Vec::new();
        while let Some(token) = self.peek() {
            match token.kind() {
                TokenKind::Comma => {
                    self.next();
                    tail.push(self.parse_expression()?);
                }
                _ => break,
            }
        }
        Ok(Some(PseudoOperand::new(head, tail)))
    }

    fn parse_actual_operand(&mut self) -> ParseResult<Option<ActualOperand>> {
        if self.is_eol() {
            return Ok(None);
        }

        let expect = "one of a, #, [, <, >, (, symbol and integer";
        match self.peek_or_err(expect)?.kind() {
            TokenKind::RegisterA => Ok(Some(self.parse_accumulator()?.into())),
            TokenKind::Sharp => Ok(Some(self.parse_immediate()?.into())),
            TokenKind::LSquare => Ok(Some(self.parse_indirect()?.into())),
            TokenKind::LT => Ok(Some(self.parse_zeropage()?.into())),
            TokenKind::GT => Ok(Some(self.parse_zeropage()?.into())),
            _ => Ok(Some(self.parse_absolute_or_relative()?.into())),
        }
    }

    fn parse_accumulator(&mut self) -> ParseResult<Accumulator> {
        let mut stack = TokenStack::new(self.next_or_err("a")?);
        match stack.last().kind() {
            TokenKind::RegisterA => (),
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "a"
            })
        }
        Ok(Accumulator::new(stack.span()))
    }

    fn parse_immediate(&mut self) -> ParseResult<Immediate> {
        let mut stack = TokenStack::new(self.next_or_err("a")?);
        match stack.last().kind() {
            TokenKind::Sharp => (),
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "#"
            })
        }

        stack.push(self.peek_or_err("any token")?);
        let cast = match stack.last().kind() {
            TokenKind::LT => {
                self.next();
                CastStrategy::Lsb
            }
            TokenKind::GT => {
                self.next();
                CastStrategy::Msb
            }
            _ => {
                stack.pop();
                CastStrategy::Lsb
            }
        };

        let expr = self.parse_expression()?;

        Ok(Immediate::new(stack.span() + expr.span(), cast, expr))
    }

    fn parse_indirect(&mut self) -> ParseResult<Indirect> {
        let mut stack = TokenStack::new(self.next_or_err("[")?);
        match stack.last().kind() {
            TokenKind::LSquare => (),
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "["
            })
        }

        stack.push(self.peek_or_err("any token")?);
        let cast = match stack.last().kind() {
            TokenKind::LT => {
                self.next();
                CastStrategy::Lsb
            }
            TokenKind::GT => {
                self.next();
                CastStrategy::Msb
            }
            _ => {
                stack.pop();
                CastStrategy::Lsb
            }
        };

        let expr = self.parse_expression()?;

        stack.push(self.peek_or_err(",")?);
        let mut register = match stack.last().kind() {
            TokenKind::Comma => {
                self.next();
                stack.push(self.next_or_err("x")?);
                match stack.last().kind() {
                    TokenKind::RegisterX => {
                        Some(IndexableRegister::X)
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "x"
                    })
                }
            }
            _ => {
                stack.pop();
                None
            }
        };

        stack.push(self.next_or_err("]")?);
        match stack.last().kind() {
            TokenKind::RSquare => (),
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "]"
            })
        }

        // If no token available, the y register doesn't exist.
        if self.is_eol() {
            return Ok(Indirect::new(stack.span(), cast, expr, register))
        }

        // Else, the y register must exist.
        stack.push(self.next_or_err(",")?);
        register = match stack.last().kind() {
            TokenKind::Comma => {
                if matches!(register, Some(_)) {
                    return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "no register"
                    })
                }
                stack.push(self.next_or_err("y")?);
                match stack.last().kind() {
                    TokenKind::RegisterY => {
                        Some(IndexableRegister::Y)
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "y"
                    })
                }
            }
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: ","
            })
        };

        Ok(Indirect::new(stack.span(), cast, expr, register))
    }

    fn parse_zeropage(&mut self) -> ParseResult<Zeropage> {
        let mut stack = TokenStack::new(self.next_or_err("< or >")?);
        let cast = match stack.last().kind() {
            TokenKind::LT => CastStrategy::Lsb,
            TokenKind::GT => CastStrategy::Lsb,
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: "< or >"
            })
        };

        let expr = self.parse_expression()?;

        if self.is_eol() {
            let span = stack.span() + expr.span();
            return Ok(Zeropage::new(span, cast, expr, None));
        }

        stack.push(self.next_or_err(",")?);
        let register = match stack.last().kind() {
            TokenKind::Comma => {
                stack.push(self.next_or_err("x or y")?);
                match stack.last().kind() {
                    TokenKind::RegisterX => {
                        Some(IndexableRegister::X)
                    }
                    TokenKind::RegisterY => {
                        Some(IndexableRegister::Y)
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "x or y"
                    })
                }
            }
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: ","
            })
        };

        Ok(Zeropage::new(stack.span(), cast, expr, register))
    }

    fn parse_absolute_or_relative(&mut self) -> ParseResult<AbsoluteOrRelative> {
        let expr = self.parse_expression()?;

        if self.is_eol() {
            let span = expr.span();
            return Ok(AbsoluteOrRelative::new(span, expr, None));
        }

        let mut stack = TokenStack::new(self.next_or_err(",")?);
        let register = match stack.last().kind() {
            TokenKind::Comma => {
                stack.push(self.next_or_err("x or y")?);
                match stack.last().kind() {
                    TokenKind::RegisterX => {
                        Some(IndexableRegister::X)
                    }
                    TokenKind::RegisterY => {
                        Some(IndexableRegister::Y)
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "x or y"
                    })
                }
            }
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect: ","
            })
        };

        let span = expr.span() + stack.span();
        Ok(AbsoluteOrRelative::new(span, expr, register))
    }
}

impl NonEmptyParser {
    fn parse_expression(&mut self) -> ParseResult<Expression> {
        self.parse_additive_expression()
    }

    fn parse_additive_expression(&mut self) -> ParseResult<Expression> {
        let mut lhs = self.parse_multiplicative_expression()?;
        while let Some(token) = self.peek() {
            match token.kind() {
                TokenKind::Plus => {
                    self.next();
                    lhs = InfixExpr::new(
                        Box::new(lhs),
                        Box::new(self.parse_multiplicative_expression()?),
                        InfixOp::Add
                    )
                    .into();
                }
                TokenKind::Minus => {
                    self.next();
                    lhs = InfixExpr::new(
                        Box::new(lhs),
                        Box::new(self.parse_multiplicative_expression()?),
                        InfixOp::Sub
                    )
                    .into();
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_multiplicative_expression(&mut self) -> ParseResult<Expression> {
        let mut lhs = self.parse_primitive_expression()?;
        while let Some(token) = self.peek() {
            match token.kind() {
                TokenKind::Star => {
                    self.next();
                    lhs = InfixExpr::new(
                        Box::new(lhs),
                        Box::new(self.parse_primitive_expression()?),
                        InfixOp::Mul
                    )
                    .into();
                }
                TokenKind::Slash => {
                    self.next();
                    lhs = InfixExpr::new(
                        Box::new(lhs),
                        Box::new(self.parse_primitive_expression()?),
                        InfixOp::Div
                    )
                    .into();
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_primitive_expression(&mut self) -> ParseResult<Expression> {
        let expect = "., (, integer or symbol";
        let mut stack = TokenStack::new(self.next_or_err(expect)?);
        match stack.last().kind() {
            TokenKind::Integer(value) => {
                Ok(Integer::new(stack.span(), *value).into())
            }
            TokenKind::Symbol(name) => {
                let symbol = GlobalSymbol::new(stack.span(), name.clone());
                Ok(Symbol::GlobalSymbol(symbol).into())
            }
            TokenKind::String(value) => {
                Ok(StringExpr::new(stack.span(), value.clone()).into())
            }
            TokenKind::Period => {
                stack.push(self.next_or_err("symbol")?);
                match stack.last().kind() {
                    TokenKind::Symbol(name) => {
                        let symbol = LocalSymbol::new(stack.span(), name.clone());
                        Ok(Symbol::LocalSymbol(symbol).into())
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: "symbol"
                    })
                }
            }
            TokenKind::LParen => {
                let expr = self.parse_expression()?;
                stack.push(self.next_or_err(")")?);
                match stack.last().kind() {
                    TokenKind::RParen => {
                        Ok(Surrounded::new(stack.span(), Box::new(expr)).into())
                    }
                    _ => return Err(ParserError::UnexpectedTokenFound {
                        span: stack.last().span(),
                        expect: ")"
                    })
                }
            }
            _ => return Err(ParserError::UnexpectedTokenFound {
                span: stack.last().span(),
                expect
            })
        }
    }
}

impl NonEmptyParser {
    /// Return current token if available.
    fn peek(&self) -> Option<Rc<Token>> {
        Some(Rc::clone(self.input.get(self.position)?))
    }

    /// Return current token, or error if token is unavailable.
    fn peek_or_err(&self, expect: &'static str) -> ParseResult<Rc<Token>> {
        let span = self.input.last().span();
        self.peek()
            .ok_or(ParserError::ExpectTokenButNotFound { span, expect })
    }

    /// Return current token if available, then advance position.
    fn next(&mut self) -> Option<Rc<Token>> {
        let token = self.peek()?;
        self.position += 1;
        Some(token)
    }

    /// Return current token, or error if token is unavailable.
    /// If available, advance position.
    fn next_or_err(&mut self, expect: &'static str) -> ParseResult<Rc<Token>> {
        let span = self.input.last().span();
        self.next()
            .ok_or(ParserError::ExpectTokenButNotFound { span, expect })
    }

    /// True if no token available.
    fn is_eol(&self) -> bool {
        self.peek().is_none()
    }
}
