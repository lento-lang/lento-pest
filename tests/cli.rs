use std::process::Command;

#[test]
fn file_evaluation_loads_prelude_by_default() {
    let path = std::env::temp_dir().join(format!("lento-prelude-{}.lt", std::process::id()));
    std::fs::write(&path, "Less\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lento_rust"))
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Less");
}

#[test]
fn no_prelude_flag_disables_prelude_declarations() {
    let path = std::env::temp_dir().join(format!("lento-no-prelude-{}.lt", std::process::id()));
    std::fs::write(&path, "Less\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lento_rust"))
        .arg("--no-prelude")
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("Less"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn function_parameter_assignment_uses_the_lambda_cell() {
    let path = std::env::temp_dir().join(format!("lento-mutable-{}.lt", std::process::id()));
    std::fs::write(&path, "fn increment x = x = x + 1\nincrement 1\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lento_rust"))
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "2");
}
