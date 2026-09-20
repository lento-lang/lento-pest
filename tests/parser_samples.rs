// Full-pipeline sample tests: every `tests/samples/**/*.lt` must parse,
// type-check, and evaluate without error. Samples are organized into
// categorical subdirectories (basics, matching, types, specs); the walk
// here is recursive, so new categories need no harness changes.

use std::fs;
use std::path::{Path, PathBuf};

use lento::ast::desugar_program;
use lento::parser::parse_program;

#[test]
fn samples_parse_check_and_evaluate() {
    let mut samples = Vec::new();
    collect_samples(Path::new("tests/samples"), &mut samples);
    samples.sort();
    assert!(
        !samples.is_empty(),
        "no samples found under tests/samples/"
    );

    let mut failed = Vec::new();
    for path in &samples {
        let source = fs::read_to_string(path).expect("read sample");
        if let Err(e) = run(&source) {
            failed.push((path.display().to_string(), e));
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

/// Depth-first collection of `.lt` files under `dir`.
fn collect_samples(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .expect("samples dir exists")
        .map(|e| e.expect("read entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_samples(&path, out);
        } else if path.extension().map(|e| e == "lt").unwrap_or(false) {
            out.push(path);
        }
    }
}

fn run(source: &str) -> Result<(), String> {
    let ast = parse_program(source).map_err(|e| format!("parse error: {e}"))?;
    let desugared = desugar_program(&ast);
    lento::typecheck::check_program(&desugared)?;
    lento::eval::eval_program(&desugared).map(|_| ())
}
