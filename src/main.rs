mod lexer;
mod parser;
mod inst;

use std::io::{stdin, stdout, Write, Read};
use lexer::Lexer;
use parser::Parser;

fn main() {
    loop {
        let mut buf = String::new();
        stdin().read_to_string(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        let token = lexer.tokenize();
        println!("{:#?}", &token);
        println!("{:#?}", Parser::new(token).parse().unwrap());
    }
}
