use std::io::Write;
use std::path::PathBuf;

use clap::Parser;

use lento::parser::parse_program;
use lento::pprint::format_program;

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

    /// Pretty-print the parsed AST back to Lento source instead of the
    /// internal AST dump.
    #[arg(short, long)]
    format: bool,
}

fn display(ast: &lento::ast::Program, format: bool) {
    if format {
        print!("{}", format_program(ast));
    } else {
        println!("{ast:#?}");
    }
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

fn run_repl(format: bool) {
    while let Some(input) = read_line(Some(">>> ")) {
        match parse_program(&input) {
            Ok(ast) => display(&ast, format),
            Err(e) => println!("Error: {}", e),
        }
    }
}

fn parse_file(path: &std::path::Path, format: bool) -> Result<(), String> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| format!("Error reading {}: {}", path.display(), e))?;
    let ast = parse_program(&src)
        .map_err(|e| format!("Parse error in {}:\n{}", path.display(), e))?;
    display(&ast, format);
    Ok(())
}

fn main() {
    let cli = Cli::parse();
    let result = if cli.interactive {
        run_repl(cli.format);
        Ok(())
    } else {
        match &cli.file {
            Some(path) => parse_file(path, cli.format),
            None => {
                run_repl(cli.format);
                Ok(())
            }
        }
    };
    if let Err(e) = result {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
