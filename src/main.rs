mod inst;
mod parser;
mod lexer;
mod asm;

use std::io::{stdin, Read};
use lexer::Lexer;

use crate::parser::Parser;

fn main() {
    loop {
        let mut buf = String::new();
        stdin().read_to_string(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        let token = lexer.tokenize();
        let parser = Parser::new(&token);
        println!("{:#?}", parser.parse().unwrap());
    }
}
