use rnasm_lexer::Lexer;
use rnasm_parser::Parser;

fn main() {
    let lexer = Lexer::new("label: lda #$00");
    let parser = Parser::new(lexer.lex().unwrap());
    println!("{:#?}", parser.parse().unwrap());
}
