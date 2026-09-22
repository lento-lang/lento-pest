// Tests for partitioning clauses into specializations.

use lento::infer::{base_env, InferCtx};
use lento::parser::parse_program;
use lento::semantics::collect_function_groups;
use lento::specialize::partition;
use lento::types::MonoType;

fn partition_src(src: &str) -> lento::specialize::OverloadSet {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    partition(&mut ctx, group, &env).unwrap()
}

#[test]
fn value_pattern_variants_of_same_type_share_one_specialization() {
    // `[]` and `[x, ...xs]` both refine the same [a] domain -> one
    // specialization with two clauses in source order.
    let set = partition_src("fn map2 f [] = []\nfn map2 f [x, ...xs] = [f x]");
    assert_eq!(set.specializations.len(), 1, "value variants share a specialization");
    assert_eq!(set.specializations[0].clauses.len(), 2);
    // Source order preserved for pattern dispatch.
    assert!(set.specializations[0].clauses[0].source_index
        < set.specializations[0].clauses[1].source_index);
}

#[test]
fn concrete_annotation_forms_distinct_specialization() {
    // `fn parse x = ...` (generic) and `fn parse (x : bytes) = ...` are
    // different specializations: bytes -> _ strictly specializes a -> _.
    let set = partition_src("fn parse x = x\nfn parse (x : bytes) = x");
    assert_eq!(
        set.specializations.len(),
        2,
        "generic and bytes-annotated clauses are distinct specializations"
    );
}

#[test]
fn different_arity_forms_different_specializations() {
    // Unary and binary clauses never merge, even with compatible domains.
    let set = partition_src("fn f x = x\nfn f x y = x");
    assert_eq!(set.specializations.len(), 2, "different arity => different specialization");
}

#[test]
fn two_incompatible_nominal_domains_split() {
    // int domain and str domain with same arity: distinct specializations.
    let set = partition_src("fn g (x : int) = x\nfn g (x : str) = x");
    assert_eq!(set.specializations.len(), 2);
}

#[test]
fn a_to_ast_and_bytes_to_ast_are_never_merged() {
    // The instruction's key case: never merge `a -> Ast` and `bytes -> Ast`
    // merely because they unify.
    let set = partition_src("fn p (x : bytes) = x\nfn p x = x");
    assert_eq!(set.specializations.len(), 2, "must not merge strict specialization with generic");
}

#[test]
fn single_clause_forms_single_specialization() {
    let set = partition_src("fn id x = x");
    assert_eq!(set.specializations.len(), 1);
    assert_eq!(set.specializations[0].clauses.len(), 1);
}

#[test]
fn specialization_scheme_is_function_type() {
    let set = partition_src("fn add a b = a + b");
    let scheme = &set.specializations[0].scheme;
    assert!(matches!(scheme.body, MonoType::Function(_, _)));
}

#[test]
fn three_value_clauses_one_specialization() {
    // Multiple literal/wildcard patterns over int share one specialization.
    let set = partition_src("fn h 0 = 0\nfn h 1 = 1\nfn h n = n");
    assert_eq!(set.specializations.len(), 1);
    assert_eq!(set.specializations[0].clauses.len(), 3);
}

#[test]
fn equivalent_generic_clauses_merge() {
    // Two polymorphic identity-shaped clauses (different var names) merge.
    let set = partition_src("fn k x = x\nfn k y = y");
    assert_eq!(set.specializations.len(), 1);
    assert_eq!(set.specializations[0].clauses.len(), 2);
}

#[test]
fn same_annotation_value_variants_merge() {
    // `(x : int) 0` and `(x : int) n` share the SAME declared restriction, so
    // they merge into one specialization (the literal `0` is a value-shape
    // variant, not a boundary).
    let set = partition_src("fn f (x : int) 0 = x\nfn f (x : int) n = x");
    assert_eq!(set.specializations.len(), 1, "same declared restriction merges");
    assert_eq!(set.specializations[0].clauses.len(), 2);
}

#[test]
fn redundant_generic_annotation_does_not_split() {
    // `(x : a)` induces no restriction (bare variable), so it merges with the
    // unannotated generic identity.
    let set = partition_src("fn id2 x = x\nfn id2 (x : a) = x");
    assert_eq!(set.specializations.len(), 1, "redundant generic annotation is not a boundary");
    assert_eq!(set.specializations[0].clauses.len(), 2);
}

#[test]
fn distinct_declared_restrictions_split() {
    // `(x : int)` vs `(x : str)` are distinct declared restrictions.
    let set = partition_src("fn g (x : int) = x\nfn g (x : str) = x");
    assert_eq!(set.specializations.len(), 2);
}
