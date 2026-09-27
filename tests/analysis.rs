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

#[cfg(feature = "canonical-smt")]
#[test]
fn canonical_smt_proves_refinement_postconditions() {
    analyze(
        "spec increment:\n             (x: int) -> (r: int)\n             where\n                 x < 9223372036854775807,\n                 r > x\n         fn increment x = x + 1\n",
    )
    .expect("SMT should prove the postcondition when increment cannot overflow");
}

#[cfg(feature = "canonical-smt")]
#[test]
fn canonical_smt_rejects_increment_at_i64_max() {
    let error = analyze(
        "spec increment:\n             (x: int) -> (r: int)\n             where\n                 x < 9223372036854775807,\n                 r > x\n         fn increment x = x + 1\n         increment 9223372036854775807\n",
    )
    .expect_err("the precondition must reject the overflowing input");
    assert!(error.contains("precondition"), "{error}");
}

#[cfg(feature = "canonical-smt")]
#[test]
fn canonical_smt_rejects_false_refinement_postconditions() {
    let error = analyze(
        "spec unchanged:\n             (x: int) -> (r: int)\n             where\n                 r > x\n         fn unchanged x = x\n",
    )
    .expect_err("SMT should find a counterexample");
    assert!(error.contains("postcondition"), "{error}");
}

#[test]
fn canonical_pipeline_accepts_polymorphic_identity() {
    analyze("fn id x = x\nassert (id 1 == 1)\n").expect("identity should analyze");
}

#[test]
fn canonical_pipeline_rejects_unsupported_intrinsic_types() {
    let error = analyze("concat 1 2\n").expect_err("concat must reject integers");
    assert!(error.contains("concat"), "{error}");
}

#[test]
fn prelude_len_uses_type_specific_native_intrinsics() {
    let program = parse_program(include_str!("../src/prelude.lt")).expect("prelude should parse");
    let analysis = analyze_program(&program).expect("prelude should analyze");
    let len = analysis
        .declarations
        .classes
        .iter()
        .find(|class| class.name == "Len")
        .expect("Len class should exist");
    assert_eq!(len.parameters, vec!["e"]);
    assert_eq!(
        analysis
            .declarations
            .instances
            .iter()
            .filter(|instance| instance.class == "Len")
            .count(),
        2
    );
    let generic_len = analysis
        .declarations
        .instances
        .iter()
        .find(|instance| instance.class == "Len" && !instance.quantified.is_empty())
        .expect("list Len implementation should be polymorphic");
    assert!(!generic_len.target.is_empty());
}

#[test]
fn prelude_algebraic_types_and_combinators_work_through_the_canonical_pipeline() {
    let source = format!(
        "{}\n{}",
        include_str!("../src/prelude.lt"),
        "assert (is_some (Some 1))\n\
         assert (is_some (Some \"hello\"))\n\
         assert (is_none None)\n\
         assert (unwrap_or 0 (Some 3) == 3)\n\
         assert (unwrap_or 7 None == 7)\n\
         assert (unwrap_or \"fallback\" (Some \"value\") == \"value\")\n\
         assert (map (x => x + 1) (Some 2) == Some 3)\n\
         assert (is_none (map (x => x + 1) None))\n\
         assert (is_ok (Ok 3))\n\
         assert (is_err (Err \"bad\"))\n\
         let success : Result<int, str> = Ok 3\n\
         let failure : Result<int, str> = Err \"bad\"\n\
         assert (is_ok success)\n\
         assert (is_err failure)\n\
         assert (map (x => x + 1) (Ok 2) == Ok 3)\n\
         assert (is_err (map (x => x + 1) (Err \"bad\")))\n\
         assert (map_err (s => concat s \"!\") (Err \"bad\") == Err \"bad!\")\n\
         assert (map_err (s => concat s \"!\") (Ok 2) == Ok 2)\n\
         assert (and_then (x => Ok (x + 1)) (Ok 2) == Ok 3)\n\
         assert (is_err (and_then (x => Ok (x + 1)) (Err \"bad\")))\n\
         (Left 1, Right \"right\", Break \"stop\", Continue 2, Unbounded, Included 3, Excluded 4)\n",
    );
    let program = parse_program(&source).expect("prelude and consumers should parse");
    let result = analyze_program(&program).expect("prelude and consumers should analyze");
    assert_eq!(
        result
            .overloads
            .iter()
            .find(|set| set.name == "map")
            .expect("map overloads should be collected")
            .specializations
            .len(),
        2
    );
    let lowered = lento::semantics::lower_analyzed_program(&result.source, &result.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &result.declarations)
        .expect("prelude combinators and constructors should evaluate");
    assert_eq!(
        value.to_string(),
        "(Left(1), Right(right), Break(stop), Continue(2), Unbounded, Included(3), Excluded(4))"
    );
}

#[test]
fn prelude_map_rejects_unrelated_argument_types() {
    let source = format!("{}\nmap (x => x) 42\n", include_str!("../src/prelude.lt"));
    let program = parse_program(&source).expect("program should parse");
    let error = analyze_program(&program).expect_err("map needs an Option or Result");
    assert!(error.contains("no overload of `map`"), "{error}");
}

#[test]
fn implementation_type_variables_require_impl_quantifiers() {
    let error = analyze("class Seq a { spec reverse : a -> a }\nimpl Seq [a] { fn reverse xs = xs }\n")
        .expect_err("unbound implementation type variable should fail");
    assert!(error.contains("unknown implementation type 'a'"), "{error}");
}

#[test]
fn constrained_impl_quantifiers_require_prerequisite_instances() {
    let result = analysis(
        "class Seq a { spec reverse : a -> a }\n\
         class Show a { spec show : a -> str }\n\
         impl Show int { fn show x = \"int\" }\n\
         impl all a: Show a. Seq [a] { fn reverse xs = xs }\n\
         reverse ([1])\n",
    )
    .expect("constrained implementation should resolve through Show int");
    let seq_instance = result
        .declarations
        .instances
        .iter()
        .find(|instance| instance.class == "Seq")
        .expect("Seq instance metadata");
    assert_eq!(seq_instance.constraints[0].name, "Show");

    let error = analyze(
        "class Seq a { spec reverse : a -> a }\n\
         class Show a { spec show : a -> str }\n\
         impl all a: Show a. Seq [a] { fn reverse xs = xs }\n\
         reverse ([1])\n",
    )
    .expect_err("constrained implementation must require Show int");
    assert!(error.contains("no instance"), "{error}");
}

#[test]
fn canonical_pipeline_keeps_wip_exhaustiveness_errors() {
    let error = analyze("fn f b = match b { true => 1 }\n").expect_err("match is incomplete");
    assert!(error.contains("non-exhaustive"), "{error}");
}

#[test]
fn typed_match_arms_contribute_to_exhaustiveness() {
    analyze("fn f value = match value { (n: int) => 1, (s: str) => 1 }\n")
        .expect("typed arms should cover their declared domains");
}

#[test]
fn anonymous_sum_annotations_are_structural() {
    analyze(
        "let identity : [int | str] -> [int | str] = value => value\n",
    )
    .expect("identical anonymous sum annotations should unify structurally");
}

#[test]
fn bracketed_union_is_a_mixed_list_element_type() {
    analyze("let values : [int | str] = [1, \"hi\"]\n")
        .expect("bracketed unions should type-check mixed lists");
}

#[test]
fn untyped_record_rest_binding_infers_an_open_row() {
    analyze(
        "let record = { name: \"hi\", count: 1 }\n\
         let { name, ...other } = record\n\
         name\n",
    )
    .expect("record rest bindings should infer an open row");
}

#[test]
fn untyped_function_rest_pattern_accepts_extra_fields() {
    analyze(
        "fn add_on_a { a: a, ...rest } = a\n\
         add_on_a { a: 1, extra: \"ok\" }\n",
    )
    .expect("function rest patterns should accept extra fields");
}

#[test]
fn quantified_record_rows_preserve_extra_fields() {
    analyze(
        "spec keep_name:\n\
             all rest. (value: { name: str, ...rest }) -> { name: str, ...rest }\n\
         fn keep_name value = value\n\
         keep_name { name: \"hi\", count: 1 }\n",
    )
    .expect("quantified record rows should preserve extra fields");
}

#[test]
fn quantified_variant_rows_accept_extra_constructors() {
    analyze(
        "type Option = Some int | None\n\
         spec unwrap:\n\
             all rest. (value: Some int | None | ...rest) -> Some int | None | ...rest\n\
         fn unwrap value = value\n\
         unwrap (Some 1)\n",
    )
    .expect("quantified variant rows should accept extra constructors");
}

#[test]
fn record_subtyping_accepts_extra_fields_at_calls() {
    analyze(
        "spec get_x: { x: int } -> int\n\
         fn get_x value = value.x\n\
         get_x { x: 1, y: \"extra\" }\n",
    )
    .expect("a function requiring x should accept records with extra fields");
}

#[test]
fn closed_record_coercion_discards_extra_fields() {
    let result = analysis(
        "fn keep_a (value: { a: int }) = value\n\
         keep_a { a: 1, b: 2 }\n",
    )
    .expect("a wider record should satisfy a closed record parameter");
    let lowered = lento::semantics::lower_analyzed_program(&result.source, &result.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &result.declarations)
        .expect("closed record coercion should evaluate");
    assert_eq!(value.to_string(), "{a: 1}");
}

#[test]
fn inline_module_use_imports_names_directly() {
    analyze(
        "mod math {\n\
             fn sqrt value = value\n\
         }\n\
         use math\n\
         sqrt 9\n",
    )
    .expect("use should import module declarations directly");
}

#[test]
fn inline_module_use_lowers_and_evaluates() {
    let program = parse_program(
        "mod math {\n\
             fn sqrt value = value\n\
         }\n\
         use math\n\
         sqrt 9\n",
    )
    .expect("module source should parse");
    let result = analysis(
        "mod math {\n\
             fn sqrt value = value\n\
         }\n\
         use math\n\
         sqrt 9\n",
    )
    .expect("module source should analyze");
    let lowered = lento::semantics::lower_analyzed_program(&result.source, &result.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &result.declarations)
        .expect("module source should evaluate");
    assert_eq!(value.to_string(), "9");
    assert_eq!(program.statements.len(), 3);
}

#[test]
fn top_level_declarations_shadow_imported_names() {
    analyze(
        "mod math {\n\
             fn value = 1\n\
         }\n\
         use math\n\
         let value = 2\n\
         value\n",
    )
    .expect("root declarations should shadow imported names");
}

#[test]
fn dotted_use_imports_nested_module_names() {
    analyze(
        "mod math {\n\
             mod integer {\n\
                 fn identity value = value\n\
             }\n\
         }\n\
         use math.integer\n\
         identity 9\n",
    )
    .expect("dotted use should resolve nested modules");
}

#[test]
fn sibling_files_are_automatic_modules() {
    let directory = std::env::temp_dir().join(format!("lento-modules-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("temporary module directory should be created");
    let root = directory.join("main.lt");
    std::fs::write(
        &root,
        "use math\n\
         sqrt 9\n",
    )
    .expect("root module should be written");
    std::fs::write(
        directory.join("math.lt"),
        "fn sqrt value = value\n",
    )
    .expect("sibling module should be written");

    let program = lento::parser::parse_file(&root).expect("file modules should parse");
    let result = lento::analysis::analyze_program(&program).expect("file modules should analyze");
    let lowered = lento::semantics::lower_analyzed_program(&result.source, &result.typed);
    let value = lento::eval::eval_program_with_declarations(&lowered, &result.declarations)
        .expect("file modules should evaluate");
    assert_eq!(value.to_string(), "9");
    std::fs::remove_dir_all(directory).expect("temporary module directory should be removed");
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
fn canonical_pipeline_rejects_ambiguous_global_class_method_names() {
    let error = analyze(
        "class First a { spec compare : a -> a -> int }\n         class Second a { spec compare : a -> a -> int }\n",
    )
    .expect_err("method names currently require a unique global scheme");
    assert!(error.contains("global method overload resolution"), "{error}");
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
fn canonical_pipeline_prebinds_recursive_lets() {
    analyze("let loop = x => loop x\n")
        .expect("recursive ordinary let should be visible while inferring its value");
}

#[test]
fn canonical_pipeline_applies_value_restriction_to_mutable_lets() {
    let error = analyze("let mut id = x => x\nlet first = id 1\nlet second = id \"text\"\n")
        .expect_err("mutable binding must not be generalized");
    assert!(error.contains("top-level let inference failed"), "{error}");
}

#[test]
fn canonical_pipeline_uses_let_annotations_to_solve_constraints() {
    analyze(
        "class Show a { spec show : a -> str }\n\
         impl Show int { fn show x = \"int\" }\n\
         let f : int -> str = x => show x\n",
    )
    .expect("annotation should solve the class constraint");

    let error = analyze("let f : int -> str = x => x + 1\n")
        .expect_err("annotation mismatch must be rejected");
    assert!(error.contains("top-level annotation failed"), "{error}");

    let error = analyze(
        "class Show a { spec show : a -> str }\n\
         let f : str -> str = x => show x\n",
    )
        .expect_err("concrete unsatisfied class constraint must be rejected");
    assert!(error.contains("no instance") || error.contains("unsupported"), "{error}");
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
fn canonical_overload_schemes_preserve_and_select_class_instances() {
    let result = analysis(
        "class Eq a { spec eq : a -> a -> bool }\n         impl Eq int { fn eq x y = x == y }\n         fn same x y = eq x y\n         let result = same 1 1\n",
    )
    .expect("the concrete call should select the Eq int instance");
    let same = result
        .typed
        .overloads
        .iter()
        .find(|set| set.name == "same")
        .expect("same overload should be in typed program");
    assert_eq!(same.specializations[0].scheme.constraints.len(), 1);
    let lento::semantics::TypedExprKind::Call {
        specialization, ..
    } = &result.typed.lets[0].value.kind
    else {
        panic!("same call should remain a typed call");
    };
    assert_eq!(*specialization, Some(0));
}

#[test]
fn canonical_overload_calls_reject_missing_class_instances() {
    let error = analyze(
        "class Eq a { spec eq : a -> a -> bool }\n         impl Eq int { fn eq x y = x == y }\n         fn same x y = eq x y\n         let result = same \"a\" \"a\"\n",
    )
    .expect_err("Eq str has no instance");
    assert!(error.contains("no instance"), "{error}");
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
