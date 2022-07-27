mod lexer;
mod parser;

use std::io::stdin;

use crate::{lexer::Lexer, parser::Parser};

fn main() {
    let cin = stdin();
    loop {
        let mut buf = String::new();
        cin.read_line(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        let token = lexer.tokenize();
        let parser = Parser::new(token.clone());
        println!("{:#?}", token);
        println!("{:#?}", parser.parse());
    }
}
