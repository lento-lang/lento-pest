use lento::analysis::analyze_program;
use lento::parser::parse_program;

fn analyze(source: &str) -> Result<(), String> {
    let program = parse_program(source).map_err(|error| error.to_string())?;
    analyze_program(&program).map(|_| ())
}

#[test]
fn canonical_pipeline_accepts_polymorphic_identity() {
    analyze("fn id x = x\nassert (id 1 == 1)\n").expect("identity should analyze");
}

#[test]
fn canonical_pipeline_keeps_wip_exhaustiveness_errors() {
    let error = analyze("fn f b = match b { true => 1 }\n").expect_err("match is incomplete");
    assert!(error.contains("non-exhaustive"), "{error}");
}

#[test]
fn canonical_pipeline_installs_sum_constructors() {
    analyze(
        "type Option a = Some a | None\n         fn get option = match option { Some value => value, None => 0 }\n         assert (get (Some 5) == 5)\n",
    )
    .expect("sum constructors should analyze");
}

#[test]
fn canonical_pipeline_rejects_namespace_collisions() {
    let error = analyze("let f = 1\nfn f x = x\n").expect_err("collision should fail");
    assert!(error.contains("declaration collision"), "{error}");
}
