use std::{env::args, fs::File, io::Read};
use rnasm_codegen::CodeGen;
use rnasm_lexer::Lexer;
use rnasm_parser::Parser;
use rnasm_report::report;
use rnasm_span::Spannable;

fn main() {
    let args = args().collect::<Vec<_>>();
    if args.len() != 2 {
        eprintln!("abort");
        return;
    }

    let mut file = File::open(&args[1]).unwrap();
    let mut input = String::new();
    file.read_to_string(&mut input).unwrap();

    let lexer = Lexer::new(input.clone());
    let tokens = match lexer.lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            for e in e.iter() {
                report(
                    &input,
                    e.span(),
                    &args[1],
                    "while lexing",
                    &e.to_string()
                );
            }
            return;
        }
    };
    let parser = Parser::new(tokens);
    let stmts = match parser.parse() {
        Ok(stmts) => stmts,
        Err(e) => {
            for e in e.iter() {
                report(
                    &input,
                    e.span(),
                    &args[1],
                    "while parsing",
                    &e.to_string()
                );
            }
            return;
        }
    };

    let codegen = CodeGen::new();
    let codes = match codegen.gen(stmts) {
        Ok(codes) => codes,
        Err(e) => {
            report(
                &input,
                e.span(),
                &args[1],
                "while generating",
                &e.to_string()
            );
            return;
        }
    };
    for code in codes.iter() {
        print!("${:04X}", code.0);
        for byte in code.1.iter() {
            print!(" {:02X}", byte);
        }
        println!();
    }
}
