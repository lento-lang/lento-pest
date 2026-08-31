use std::fs;
use std::path::Path;

#[test]
fn parses_all_samples() {
    let dir = Path::new("tests/samples");
    let mut failed = Vec::new();

    for entry in fs::read_dir(dir).expect("samples dir exists") {
        let path = entry.expect("read entry").path();
        if path.extension().map(|e| e == "lt").unwrap_or(false) {
            let source = fs::read_to_string(&path).expect("read sample");
            match lento::parser::parse_program(&source) {
                Ok(_) => {}
                Err(e) => failed.push((path.display().to_string(), e.to_string())),
            }
        }
    }

    assert!(
        failed.is_empty(),
        "{} sample(s) failed to parse:\n{}",
        failed.len(),
        failed
            .iter()
            .map(|(f, e)| format!("{}:\n{}\n", f, e))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
