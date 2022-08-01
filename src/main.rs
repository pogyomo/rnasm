mod inst;
mod parser;
mod lexer;
mod eval;
mod asm;

use std::rc::Rc;
use std::io::{stdin, Read};
use lexer::Lexer;

use crate::asm::Assembler;
use crate::{parser::Parser, eval::{Eval, env::Environment}};

fn main() {
    loop {
        let mut buf = String::new();
        stdin().read_to_string(&mut buf).unwrap();
        let lexer  = Lexer::new(buf.as_str());
        let token  = lexer.tokenize();
        let parser = Parser::new(&token);
        let prog   = parser.parse().unwrap();
        let eval   = Eval::new(&prog, 0, Rc::new(Environment::new()));
        let list   = eval.eval();
        let asm    = Assembler::new(&list);
        println!("{:#?}", asm.assemble());
        println!("{:#?}", 
                 Assembler::new(
                     &Eval::new(
                         &Parser::new(
                             &Lexer::new(
                                 buf.as_str()
                            ).tokenize()
                         ).parse().unwrap(), 0, Rc::new(Environment::new())
                     ).eval()
                 ).assemble()
             );
    }
}
