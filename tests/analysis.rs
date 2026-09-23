use lento::analysis::analyze_program;
use lento::parser::parse_program;

fn analyze(source: &str) -> Result<(), String> {
    let program = parse_program(source).map_err(|error| error.to_string())?;
    analyze_program(&program).map(|_| ())
}

fn analysis(source: &str) -> Result<lento::analysis::Analysis, String> {
    let program = parse_program(source).map_err(|error| error.to_string())?;
    analyze_program(&program)
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
fn runtime_uses_resolved_sum_metadata() {
    let program = parse_program(
        "type Option a = Some a | None\n         Some 5\n",
    )
    .expect("program should parse");
    let analysis = analyze_program(&program).expect("sum type should analyze");
    let lowered = lento::semantics::lower_analyzed_program(&program, &analysis.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &analysis.declarations)
        .expect("metadata-installed constructor should evaluate");
    assert_eq!(value.to_string(), "Some(5)");
}

#[test]
fn typed_lowering_executes_analyzed_function_bodies_in_source_order() {
    let program = parse_program(
        "fn increment x = x + 1\n         let value = increment 4\n         value\n",
    )
    .expect("program should parse");
    let analysis = analyze_program(&program).expect("program should analyze");
    let lowered = lento::semantics::lower_analyzed_program(&program, &analysis.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &analysis.declarations)
        .expect("typed lowering should execute");
    assert_eq!(value.to_string(), "5");
}

#[test]
fn canonical_pipeline_rejects_namespace_collisions() {
    let error = analyze("let f = 1\nfn f x = x\n").expect_err("collision should fail");
    assert!(error.contains("declaration collision"), "{error}");
}


#[test]
fn canonical_pipeline_validates_class_implementations() {
    analyze(
        "class Comparable a { spec compare : a -> a -> int }\n         type Cat = { name: str }\n         impl Comparable Cat { fn compare (x: Cat) (y: Cat) = 0 }\n",
    )
    .expect("valid class implementation should analyze");
}

#[test]
fn canonical_pipeline_rejects_incomplete_class_implementation() {
    let error = analyze(
        "class Comparable a { spec compare : a -> a -> int; spec equal : a -> a -> bool }\n         impl Comparable int { fn compare x y = 0 }\n",
    )
    .expect_err("missing class method should be rejected");
    assert!(error.contains("missing required method"), "unexpected error: {error}");
}

#[test]
fn canonical_pipeline_rejects_extra_class_methods() {
    let error = analyze(
        "class Comparable a { spec compare : a -> a -> int }\n         impl Comparable int { fn other x = 0 }\n",
    )
    .expect_err("extra class method should be rejected");
    assert!(error.contains("not required"));
}

#[test]
fn canonical_pipeline_rejects_overlapping_implementations() {
    let error = analyze(
        "class Comparable a { spec compare : a -> a -> int }\n         impl Comparable int { fn compare x y = 0 }\n         impl Comparable int { fn compare x y = 1 }\n",
    )
    .expect_err("duplicate implementation should be rejected");
    assert!(error.contains("overlapping"));
}


#[test]
fn canonical_pipeline_type_checks_where_refinements() {
    analyze(
        "spec positive:\n         (x: int) -> int\n         where\n             x > 0\n",
    )
    .expect("well-typed refinement should analyze");
}

#[test]
fn canonical_pipeline_rejects_unknown_where_names() {
    let error = analyze(
        "spec positive:\n         (x: int) -> int\n         where\n             y > 0\n",
    )
    .expect_err("unknown refinement name should fail");
    assert!(error.contains("unbound variable"));
}

#[test]
fn canonical_pipeline_rejects_non_boolean_where_refinements() {
    let error = analyze(
        "spec positive:\n         (x: int) -> int\n         where\n             x + 1\n",
    )
    .expect_err("non-boolean refinement should fail");
    assert!(error.contains("must be boolean"));
}


#[test]
fn canonical_analysis_exposes_resolved_type_metadata() {
    let result = analysis(
        "type Option a = Some a | None\n         type User = { name: str }\n",
    )
    .expect("declarations should resolve");
    let option = result
        .declarations
        .types
        .iter()
        .find(|ty| ty.name == "Option")
        .expect("Option metadata");
    assert_eq!(option.constructors.len(), 2);
    assert_eq!(option.constructors[0].name, "Some");
    let user = result
        .declarations
        .types
        .iter()
        .find(|ty| ty.name == "User")
        .expect("User metadata");
    assert_eq!(user.fields.len(), 1);
    assert_eq!(user.fields[0].0, "name");
}


#[test]
fn canonical_analysis_exposes_class_dispatch_metadata() {
    let result = analysis(
        "class Comparable a { spec compare : a -> a -> int }\n         impl Comparable int { fn compare x y = 0 }\n",
    )
    .expect("class declarations should resolve");
    assert_eq!(result.declarations.classes[0].methods, vec!["compare"]);
    assert_eq!(result.declarations.instances[0].class, "Comparable");
    assert_eq!(result.declarations.instances[0].methods, vec!["compare"]);
}


#[test]
fn canonical_pipeline_rejects_partial_refinement_function_use() {
    let error = analyze(
        "spec positive:\n         (x: int) -> int\n         where\n             x > 0\n         let saved = positive\n",
    )
    .expect_err("refinement-bearing function must not escape as a value");
    assert!(error.contains("partial application"), "{error}");
}


#[test]
fn canonical_analysis_populates_typed_bodies_and_schemes() {
    let result = analysis("fn id x = x\n").expect("function should analyze");
    let set = &result.typed.overloads[0];
    let clause = &set.specializations[0].clauses[0];
    assert_eq!(set.name, "id");
    assert_eq!(clause.source_index, 0);
    assert!(matches!(
        clause.body.kind,
        lento::semantics::TypedExprKind::Var(_)
    ));
    assert!(!set.specializations[0].scheme.body.free_vars().is_empty());
}


#[test]
fn canonical_typed_expressions_keep_recursive_annotations() {
    let result = analysis("fn add_one x = x + 1\n").expect("function should analyze");
    let body = &result.typed.overloads[0].specializations[0].clauses[0].body;
    let lento::semantics::TypedExprKind::Composite { children, .. } = &body.kind else {
        panic!("binary expression should retain its typed children");
    };
    assert_eq!(children.len(), 2);
    assert_eq!(
        children[0].ty,
        lento::types::MonoType::Constructor("int".into(), vec![])
    );
    assert_eq!(
        children[1].ty,
        lento::types::MonoType::Constructor("int".into(), vec![])
    );
}

#[test]
fn canonical_typed_program_keeps_top_level_let_and_expression_types() {
    let result = analysis("let value = 1\nvalue + 2\n").expect("program should analyze");
    assert_eq!(result.typed.lets.len(), 1);
    assert_eq!(result.typed.exprs.len(), 1);
    assert_eq!(
        result.typed.lets[0].value.ty,
        lento::types::MonoType::Constructor("int".into(), vec![])
    );
    assert_eq!(
        result.typed.exprs[0].ty,
        lento::types::MonoType::Constructor("int".into(), vec![])
    );
}

#[test]
fn canonical_pipeline_resolves_fully_typed_overload_calls() {
    let result = analysis("fn id x = x\nlet value = id 1\n")
        .expect("fully applied call should resolve");
    let lento::semantics::TypedExprKind::Call {
        specialization, ..
    } = &result.typed.lets[0].value.kind
    else {
        panic!("top-level value should retain its call node");
    };
    assert_eq!(*specialization, Some(0));
}

#[test]
fn canonical_pipeline_resolves_class_method_instances() {
    analyze(
        "class Eq a { spec eq : a -> a -> bool }\n         impl Eq int { fn eq x y = x == y }\n         assert (eq 1 1)\n",
    )
    .expect("concrete class method should resolve through its instance");
}

#[test]
fn canonical_pipeline_rejects_missing_class_instance() {
    let error = analyze(
        "class Eq a { spec eq : a -> a -> bool }\n         assert (eq 1 1)\n",
    )
    .expect_err("missing class instance should fail");
    assert!(error.contains("no instance"), "{error}");
}
