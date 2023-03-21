use std::{env::args, fs::File, io::{Read, Write}, collections::HashMap};
use rnasm_builder::{Builder, HeaderMirror};
use rnasm_codegen::CodeGen;
use rnasm_lexer::Lexer;
use rnasm_parser::Parser;
use rnasm_report::report;
use rnasm_span::Spannable;

/// Convert bank-code associated data into vector where
/// * `code.get(i) == Some(...) => vec.get(i) = Some(...)`
/// * `code.get(i) == None => vec.get(i) = Some(vec![])`
///
/// If given hashmap is empty, returned vector is also empty.
fn convert_banked_code(
    mut codes: HashMap<u16, Vec<(u16, Vec<u8>)>>
) -> Vec<Vec<(u16, u8)>> {
    let key_max = match codes.keys().into_iter().max() {
        Some(max) => *max,
        None => return Vec::new(),
    };
    for key in 0..key_max {
        if codes.get(&key).is_none() {
            codes.insert(key, Vec::new()); // Add missing keys.
        }
    }

    let mut codes = codes.into_iter().collect::<Vec<_>>();
    codes.sort_by(|a, b| a.0.cmp(&b.0));
    let codes = codes.into_iter().map(|v| v.1).collect::<Vec<_>>();

    let mut result = Vec::new();
    for code in codes.into_iter() {
        let mut processed_code = Vec::new();
        for (address, bytes) in code.into_iter() {
            for (byte, offset) in bytes.into_iter().zip(0..) {
                processed_code.push((address + offset, byte));
            }
        }
        result.push(processed_code);
    }
    result
}

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

    // Convert HashMap<u16, Vec<(u16, Vec<u8>)> into Vec<Vec<(u16, u8)>>
    // where the converted vector's length is equal to source's max key.
    let prgrom = convert_banked_code(codes.prgs);
    let chrrom = convert_banked_code(codes.chrs);

    let builder = Builder::new(
        prgrom, chrrom, codes.mapper, codes.submapper, codes.mirror
    );
    let rom = match builder.build() {
        Ok(rom) => rom,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    let mut file = File::create("a.nes").unwrap();
    file.write_all(&rom).unwrap();
}
