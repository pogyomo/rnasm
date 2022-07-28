mod lexer;
mod parser;

use std::io::{stdin, stdout, Write};
use lexer::Lexer;
use parser::Parser;

fn main() {
    loop {
        print!(">> ");
        stdout().flush().unwrap();
        let mut buf = String::new();
        stdin().read_line(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        let token = lexer.tokenize();
        println!("{:#?}", &token);
        println!("{:#?}", Parser::new(token).parse());
    }
}
