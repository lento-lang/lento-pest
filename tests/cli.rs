use std::process::Command;

#[test]
fn prelude_flag_loads_class_declarations() {
    let path = std::env::temp_dir().join(format!("lento-prelude-{}.lt", std::process::id()));
    std::fs::write(&path, "Less\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lento_rust"))
        .arg("--prelude")
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Less");
}
