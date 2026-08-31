use std::io::Write;
use std::path::PathBuf;

use clap::Parser;

use lento::parser::parse_program;

/// Lento command line: parse a file, or drop into an interactive REPL.
#[derive(Parser, Debug)]
#[command(name = "lento", version, about)]
struct Cli {
    /// Parse a Lento source file. Omitted, runs the REPL.
    ///
    /// A default positional: `lento foo.lt` parses the file, while `lento`
    /// with no arguments drops into the interactive REPL.
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

    /// Run the interactive REPL, even when a FILE is given.
    #[arg(short, long, conflicts_with = "file")]
    interactive: bool,
}

fn read_line(prompt: Option<&str>) -> Option<String> {
    if let Some(prompt) = prompt {
        print!("{}", prompt);
        std::io::stdout().flush().unwrap();
    }
    let mut input = String::new();
    match std::io::stdin().read_line(&mut input) {
        Ok(0) => None, // EOF
        Ok(_) => Some(input.trim_end().to_string()),
        Err(_) => None, // treat I/O error as EOF too
    }
}

fn run_repl() {
    while let Some(input) = read_line(Some(">>> ")) {
        match parse_program(&input) {
            Ok(ast) => println!("{ast:#?}"),
            Err(e) => println!("Error: {}", e),
        }
    }
}

fn parse_file(path: &std::path::Path) {
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("Error reading {}: {}", path.display(), e);
            std::process::exit(1);
        }
    };
    match parse_program(&src) {
        Ok(ast) => println!("{ast:#?}"),
        Err(e) => {
            eprintln!("Parse error in {}:\n{}", path.display(), e);
            std::process::exit(1);
        }
    }
}

fn main() {
    let cli = Cli::parse();
    if cli.interactive {
        run_repl();
    } else {
        match &cli.file {
            Some(path) => parse_file(path),
            None => run_repl(),
        }
    }
}
