use std::io::Write;
use std::path::PathBuf;

use clap::Parser;

use lento::parser::parse_program;
use lento::pprint::format_program;

/// Lento command line: parse a file, or drop into an interactive REPL.
#[derive(Parser, Debug)]
#[command(name = "lento", version, about)]
struct Cli {
    /// A Lento source file. Omitted, runs the REPL.
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

    /// Run the interactive REPL, even when a FILE is given.
    #[arg(short, long, conflicts_with = "file")]
    interactive: bool,

    /// For the FILE: print the parsed AST and stop.
    #[arg(long, requires = "file", conflicts_with = "print_code")]
    print_ast: bool,

    /// For the FILE: print the pretty-printed source and stop.
    #[arg(long, requires = "file", conflicts_with = "print_ast")]
    print_code: bool,
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

/// Read and parse a FILE, yielding the AST.
fn load(path: &std::path::Path) -> Result<lento::ast::Program, String> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| format!("Error reading {}: {}", path.display(), e))?;
    parse_program(&src).map_err(|e| format!("Parse error in {}:\n{}", path.display(), e))
}

/// Evaluate a parsed program. Not yet implemented.
///
/// `fn` clauses are desugared into `let` bindings first, so the interpreter
/// never has to handle an `FnDecl`.
fn interpret(ast: &lento::ast::Program) -> Result<(), String> {
    let _desugared = lento::ast::desugar_program(ast);
    todo!("interpreter")
}

fn main() -> Result<(), String> {
    let cli = Cli::parse();
    if cli.interactive {
        run_repl();
        return Ok(());
    }
    match &cli.file {
        Some(path) => {
            if cli.print_ast {
                let ast = load(path)?;
                println!("{ast:#?}");
                Ok(())
            } else if cli.print_code {
                let ast = load(path)?;
                print!("{}", format_program(&ast));
                Ok(())
            } else {
                // Default mode: interpret the program.
                let ast = load(path)?;
                interpret(&ast)
            }
        }
        None => {
            run_repl();
            Ok(())
        }
    }
}
