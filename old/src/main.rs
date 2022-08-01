mod lexer;
mod parser;
mod inst;

use std::io::{stdin, Read};
use lexer::Lexer;
use parser::Parser;

fn main() {
    loop {
        let mut buf = String::new();
        stdin().read_to_string(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        let token = lexer.tokenize();
        let parser = Parser::new(&token);
        let prog   = parser.parse().unwrap();
        println!("{:#?}", &prog);
    }
}
