use rnasm_span::Span;
use unicode_width::UnicodeWidthStr;

/// Report error to stderr.
pub fn report(input: &str, span: Span, name: &str, what: &str, msg: &str) {
    let start = start(input, span);
    let end = end(input, span);

    let lines = input.lines().collect::<Vec<_>>();
    if start.0 == end.0 {
        let line = lines[start.0 - 1];
        let linenum = " ".repeat(start.0.to_string().width());
        let padding = " ".repeat(line[..start.1].width());
        let indicator = "^".repeat(line[start.1..end.1].width());
        eprintln!("[error] {} at {}", what, name);
        eprintln!("{} | {}", start.0, line);
        eprintln!("{}   {}{} {}", linenum, padding, indicator, msg);
    } else {
        eprintln!("[error] {} at {}", what, name);

        let line = lines[start.0 - 1];
        let linenum = " ".repeat(end.0.to_string().width());
        let padding = " ".repeat(line[..start.1].width());
        let indicator = "^".repeat(line[start.1..].width());
        eprintln!("{} | {}", start.0, line);
        eprintln!("{} : {}{}", linenum, padding, indicator);

        let line = lines[end.0 - 1];
        let linenum = " ".repeat(end.0.to_string().width());
        let indicator = "^".repeat(line[..end.1].width());
        eprintln!("{} | {}", end.0, line);
        eprintln!("{}   {} {}", linenum, indicator, msg);
    }
}

/// Return start line (1-indexing) and start offset on the line.
fn start(input: &str, span: Span) -> (usize, usize) {
    let mut start = (1, 0);
    for (offset, ch) in input.char_indices() {
        if offset >= span.offset() {
            break;
        }

        if ch == '\n' {
            start.0 += 1;
            start.1 = 0;
        } else {
            start.1 += ch.len_utf8();
        }
    }
    start
}

/// Return end line (1-indexing) and end offset on the line.
fn end(input: &str, span: Span) -> (usize, usize) {
    let mut end = (1, 0);
    for (offset, ch) in input.char_indices() {
        if offset >= span.offset() + span.len() {
            break;
        }

        if ch == '\n' {
            end.0 += 1;
            end.1 = 0;
        } else {
            end.1 += ch.len_utf8();
        }
    }
    end
}
