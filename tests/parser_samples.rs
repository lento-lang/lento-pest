// Full-pipeline sample tests: every `tests/samples/*.lt` must parse,
// type-check, and evaluate without error.

use std::fs;
use std::path::Path;

#[test]
fn samples_parse_check_and_evaluate() {
    let dir = Path::new("tests/samples");
    let mut failed = Vec::new();

    for entry in fs::read_dir(dir).expect("samples dir exists") {
        let path = entry.expect("read entry").path();
        if path.extension().map(|e| e == "lt").unwrap_or(false) {
            let source = fs::read_to_string(&path).expect("read sample");
            if let Err(e) = run(&source) {
                failed.push((path.display().to_string(), e));
            }
        }
    }

    assert!(
        failed.is_empty(),
        "{} sample(s) failed:\n{}",
        failed.len(),
        failed
            .iter()
            .map(|(f, e)| format!("{f}:\n{e}\n"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

fn run(source: &str) -> Result<(), String> {
    let ast = parse_program(source).map_err(|e| format!("parse error: {e}"))?;
    let desugared = desugar_program(&ast);
    lento::typecheck::check_program(&desugared)?;
    lento::eval::eval_program(&desugared).map(|_| ())
}

use lento::ast::desugar_program;
use lento::parser::parse_program;
