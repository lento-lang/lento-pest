// Tests for the semantic declaration-collection phase: `spec`/`fn`
// declarations are gathered into `FunctionGroup`s by lexical scope and name,
// independent of statement adjacency, and collisions with non-function
// bindings are rejected.

use lento::ast::{Decl, Stmt};
use lento::parser::parse_program;
use lento::semantics::{collect_function_groups, CollectErrorKind};

fn group_names(program_src: &str) -> Vec<String> {
    let ast = parse_program(program_src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    collected
        .function_groups
        .iter()
        .map(|g| g.name.clone())
        .collect()
}

#[test]
fn clauses_separated_by_specs_types_and_unrelated_decls_form_one_group() {
    // Adjacency must not define semantic grouping: `f`'s clauses are split by
    // a spec, a type declaration, and an unrelated function.
    let src = "\
fn f x = x
spec f: all a. a -> a
type alias = int
fn g y = y
fn f 0 = 0
";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();

    let f = collected
        .function_groups
        .iter()
        .find(|g| g.name == "f")
        .expect("one group for f");
    assert_eq!(f.raw_clauses.len(), 2);
    assert_eq!(f.explicit_specs.len(), 1);
    assert_eq!(f.explicit_specs[0].decl.name, "f");

    // Source order is metadata: clause indices ascend with source position
    // and the span covers the whole declaration range.
    assert_eq!(f.source_indices, vec![0, 4]);
    assert_eq!(f.source_span, (0, 4));

    let g = collected
        .function_groups
        .iter()
        .find(|g| g.name == "g")
        .expect("one group for g");
    assert_eq!(g.raw_clauses.len(), 1);

    // Non-function statements survive in source order outside the groups.
    assert_eq!(collected.statements.len(), 1);
    assert!(matches!(
        collected.statements[0],
        Stmt::Decl(Decl::Type(_))
    ));
}

#[test]
fn source_order_preserved_as_clause_metadata() {
    let src = "\
fn map f [] = []
fn map f [x, ...xs] = concat [f x] (map f xs)
";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let map = &collected.function_groups[0];
    assert_eq!(map.name, "map");
    assert_eq!(map.raw_clauses.len(), 2);
    assert_eq!(map.source_indices, vec![0, 1]);
}

#[test]
fn fn_group_conflicts_with_let_binding_of_same_name() {
    let src = "\
fn f x = x
let f = 42
";
    let ast = parse_program(src).unwrap();
    let err = collect_function_groups(&ast).unwrap_err();
    match err.kind {
        CollectErrorKind::Conflict {
            name,
            other_kind,
            spans,
        } => {
            assert_eq!(name, "f");
            assert_eq!(other_kind, "let");
            assert_eq!(spans, vec![0, 1]);
        }
        other => panic!("expected Conflict, got {other:?}"),
    }
}

#[test]
fn fn_group_conflicts_with_type_synonym_of_same_name() {
    let src = "\
type parse = int
fn parse x = x
";
    let ast = parse_program(src).unwrap();
    let err = collect_function_groups(&ast).unwrap_err();
    assert!(matches!(
        err.kind,
        CollectErrorKind::Conflict {
            other_kind: "type",
            ..
        }
    ));
}

#[test]
fn spec_for_non_function_binding_is_rejected() {
    // A spec cannot hang off a `let` binding with no clauses at all.
    let src = "\
spec x: int
let x = 1
";
    let ast = parse_program(src).unwrap();
    let err = collect_function_groups(&ast).unwrap_err();
    match err.kind {
        CollectErrorKind::SpecOnNonFunction {
            name, other_kind, ..
        } => {
            assert_eq!(name, "x");
            assert_eq!(other_kind, "let");
        }
        other => panic!("expected SpecOnNonFunction, got {other:?}"),
    }
}

#[test]
fn spec_only_group_for_abstract_declaration_is_collected() {
    // A spec with no clauses and no conflicting binding is a valid (abstract)
    // group awaiting an implementation.
    let src = "spec convert: all a. a -> str\n";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    assert_eq!(group_names(src), vec!["convert"]);
    assert_eq!(collected.function_groups[0].raw_clauses.len(), 0);
    assert_eq!(collected.function_groups[0].explicit_specs.len(), 1);
}

#[test]
fn unrelated_names_do_not_collide() {
    let src = "\
fn f x = x
let g = f 1
fn h y = y
";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    assert_eq!(collected.function_groups.len(), 2);
    assert_eq!(collected.statements.len(), 1);
}
