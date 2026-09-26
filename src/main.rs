use std::io::Write;
use std::path::PathBuf;

use clap::Parser;

use lento::parser::parse_program;
use lento::pprint::format_program;

#[derive(Parser, Debug)]
#[command(name = "lento", version, about)]
struct Cli {
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,
    #[arg(short, long, conflicts_with = "file")]
    interactive: bool,
    #[arg(long, requires = "file", conflicts_with = "print_code")]
    print_ast: bool,
    #[arg(long, requires = "file", conflicts_with = "print_ast")]
    print_code: bool,
    #[arg(long, requires = "file", conflicts_with_all = ["print_ast", "print_code"])]
    fmt: bool,
}

fn read_line(prompt: Option<&str>) -> Option<String> {
    if let Some(prompt) = prompt {
        print!("{}", prompt);
        std::io::stdout().flush().unwrap();
    }
    let mut input = String::new();
    match std::io::stdin().read_line(&mut input) {
        Ok(0) => None,
        Ok(_) => Some(input.trim_end().to_string()),
        Err(_) => None,
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

fn load(path: &std::path::Path) -> Result<lento::ast::Program, String> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| format!("Error reading {}: {}", path.display(), e))?;
    parse_program(&src).map_err(|e| format!("Parse error in {}:\n{}", path.display(), e))
}

fn interpret(ast: &lento::ast::Program) -> Result<(), String> {
    let desugared = lento::ast::desugar_program(ast);
    let value = lento::eval::eval_program(&desugared)?;
    if matches!(desugared.statements.last(), Some(lento::ast::Stmt::Expr(_)))
        && !matches!(value, lento::eval::Value::Unit)
    {
        println!("{value}");
    }
    Ok(())
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
            } else if cli.fmt {
                let ast = load(path)?;
                std::fs::write(path, format_program(&ast))
                    .map_err(|e| format!("Error writing {}: {}", path.display(), e))?;
                Ok(())
            } else {
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
