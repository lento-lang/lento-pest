// Full-pipeline sample tests: every `tests/samples/**/*.lt` must parse,
// load and evaluate without error through the CLI in standalone mode. Many
// samples define their own types and classes with prelude names. Samples are
// organized into
// categorical subdirectories (basics, matching, types, specs); the walk
// here is recursive, so new categories need no harness changes.

use std::fs;
use std::path::{Path, PathBuf};

#[test]
fn samples_parse_check_and_evaluate() {
    let mut samples = Vec::new();
    collect_samples(Path::new("tests/samples"), &mut samples);
    samples.sort();
    assert!(!samples.is_empty(), "no samples found under tests/samples/");

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
    let path = std::env::temp_dir().join(format!("lento-parser-sample-{}.lt", std::process::id()));
    std::fs::write(&path, source).map_err(|e| format!("write sample: {e}"))?;
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_lento_rust"))
        .arg("--no-prelude")
        .arg(&path)
        .output()
        .map_err(|e| format!("run CLI: {e}"))?;
    let _ = std::fs::remove_file(&path);
    if result.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&result.stderr).into_owned())
    }
}
