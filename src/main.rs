use clap::Parser as ClapParser;
use rnasm_builder::Builder;
use rnasm_codegen::{BankData, CodeGen};
use rnasm_lexer::Lexer;
use rnasm_parser::Parser;
use rnasm_report::report;
use rnasm_span::Spannable;
use std::{
    collections::HashMap,
    fs::File,
    io::{Read, Write},
};

#[derive(Debug, ClapParser)]
#[command(version, long_about = None)]
#[command(author = "pogyomo")]
#[command(about = "A hobby nes assembler written in rust")]
pub struct Args {
    #[arg(value_name = "FILE", help = "input file name")]
    input: String,
    #[arg(short, value_name = "OUTPUT", help = "output file name")]
    output: Option<String>,
}

/// Convert bank-code associated data into vector where
/// * `code.get(i) == Some(...) => vec.get(i) = Some(...)`
/// * `code.get(i) == None => vec.get(i) = Some(BankData { data: vec![], .. })`
///
/// If given hashmap is empty, returned vector is also empty.
fn linearize_bankdata(mut codes: HashMap<u16, BankData>) -> Vec<BankData> {
    let key_max = match codes.keys().into_iter().max() {
        Some(max) => *max,
        None => return Vec::new(),
    };
    for key in 0..key_max {
        if codes.get(&key).is_none() {
            codes.insert(key, BankData::new(0)); // Add missing keys.
        }
    }

    let mut codes = codes.into_iter().collect::<Vec<_>>();
    codes.sort_by(|a, b| a.0.cmp(&b.0));
    codes.into_iter().map(|v| v.1).collect::<Vec<_>>()
}

fn main() {
    let args = Args::parse();

    let mut file = match File::open(&args.input) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("failed to open file: {}", e);
            eprintln!("abort");
            return;
        }
    };
    let mut input = String::new();
    match file.read_to_string(&mut input) {
        Ok(_) => (),
        Err(e) => {
            eprintln!("failed to read file: {}", e);
            eprintln!("abort");
            return;
        }
    };

    let lexer = Lexer::new(input.clone());
    let tokens = match lexer.lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            for e in e.iter() {
                report(
                    &input,
                    e.span(),
                    &args.input,
                    "while lexing",
                    &e.to_string(),
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
                    &args.input,
                    "while parsing",
                    &e.to_string(),
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
                &args.input,
                "while generating",
                &e.to_string(),
            );
            return;
        }
    };

    // Convert HashMap<u16, BankData> into Vec<BankData>
    // where the converted vector's length is equal to source's max key.
    let prgrom = linearize_bankdata(codes.prgs);
    let chrrom = linearize_bankdata(codes.chrs);

    let builder = Builder::new(prgrom, chrrom, codes.mapper, codes.submapper, codes.mirror);
    let rom = match builder.build() {
        Ok(rom) => rom,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    let output = match args.output {
        Some(output) => output,
        None => "a.nes".to_string(),
    };
    let mut file = match File::create(output) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("failed to create output file: {}", e);
            eprintln!("abort");
            return;
        }
    };
    match file.write_all(&rom) {
        Ok(_) => (),
        Err(e) => {
            eprintln!("failed to write output: {}", e);
            eprintln!("abort");
            return;
        }
    };
}
