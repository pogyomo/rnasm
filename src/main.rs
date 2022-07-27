mod lexer;
mod parser;

use std::io::stdin;

use crate::lexer::Lexer;

fn main() {
    let cin = stdin();
    loop {
        let mut buf = String::new();
        cin.read_line(&mut buf).unwrap();
        let lexer = Lexer::new(buf.as_str());
        println!("{:#?}", lexer.tokenize());
    }
}
