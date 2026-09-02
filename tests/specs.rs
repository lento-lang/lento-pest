// Tests for associating specs with specializations.

use lento::infer::{base_env, InferCtx};
use lento::parser::parse_program;
use lento::semantics::{collect_function_groups, SpecOrigin};
use lento::specialize::partition;
use lento::specs::{associate_specs, SpecErrorKind};
use lento::types::TypeVarSupply;

fn associate(src: &str) -> lento::specs::SpecAssociation {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    associate_specs(&mut supply, group, &set).unwrap()
}

fn associate_err(src: &str) -> SpecErrorKind {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    associate_specs(&mut supply, group, &set).unwrap_err().kind
}

#[test]
fn spec_satisfied_by_matching_implementation() {
    // spec id : all a. a -> a  implemented by  fn id x = x
    let assoc = associate("spec id: all a. a -> a\nfn id x = x");
    assert_eq!(assoc.bindings.len(), 1);
    assert!(matches!(assoc.bindings[0].origin, SpecOrigin::Explicit(_)));
    assert!(assoc.unsatisfied.is_empty());
}

#[test]
fn omitted_spec_synthesizes_implicit_spec() {
    // No spec at all: the specialization gets an implicit spec with
    // Inferred provenance. The checking path is identical to an explicit one.
    let assoc = associate("fn id x = x");
    assert_eq!(assoc.bindings.len(), 1);
    assert!(matches!(assoc.bindings[0].origin, SpecOrigin::Inferred(_)));
    // The implicit spec is the specialization's own principal scheme.
    assert_eq!(assoc.bindings[0].spec.quantified.len(), 1);
}

#[test]
fn explicit_and_inferred_specs_coexist() {
    // Generic clause matches the explicit spec; the annotated clause gets an
    // implicit spec (it is a deliberate specialization, not an instance of
    // the generic contract's only clause... actually bytes IS an instance of
    // a -> a, so the annotated specialization also satisfies the explicit
    // spec).
    let assoc = associate("spec f: all a. a -> a\nfn f x = x\nfn f (x : bytes) = x");
    assert_eq!(assoc.bindings.len(), 2);
    // Both specializations satisfy `all a. a -> a` (bytes -> bytes is an
    // instance), so both bind to the explicit spec.
    assert!(assoc
        .bindings
        .iter()
        .all(|b| matches!(b.origin, SpecOrigin::Explicit(_))));
}

#[test]
fn unsatisfied_explicit_spec_is_an_error() {
    // spec says int -> int, but the only clause is str -> str: not an
    // instance, so the spec is unsatisfied.
    let err = associate_err("spec g: int -> int\nfn g (x : str) = x");
    assert!(matches!(err, SpecErrorKind::UnsatisfiedSpec { .. }));
}

#[test]
fn abstract_spec_only_group_is_allowed() {
    // A spec with no clauses at all is an abstract declaration: collected,
    // no implementation required.
    let ast = parse_program("spec convert: all a. a -> str").unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    let assoc = associate_specs(&mut supply, group, &set).unwrap();
    assert!(assoc.bindings.is_empty());
}

#[test]
fn more_general_implementation_satisfies_specific_spec() {
    // spec h : int -> int; implementation is the fully polymorphic identity.
    // A more-general implementation satisfies a more-specific spec.
    let assoc = associate("spec h: int -> int\nfn h x = x");
    assert_eq!(assoc.bindings.len(), 1);
    assert!(matches!(assoc.bindings[0].origin, SpecOrigin::Explicit(_)));
    assert!(assoc.unsatisfied.is_empty());
}

#[test]
fn concrete_spec_not_discharged_by_unrelated_concrete_impl() {
    // spec k : str -> str with only an int -> int implementation: unsatisfied.
    let err = associate_err("spec k: str -> str\nfn k (x : int) = x");
    assert!(matches!(err, SpecErrorKind::UnsatisfiedSpec { .. }));
}

#[test]
fn several_implementations_can_share_one_spec() {
    // Both the empty-list and cons clauses of `len2` live in ONE
    // specialization, which satisfies the spec once.
    let assoc = associate("spec len2: all a. [a] -> int\nfn len2 [] = 0\nfn len2 [x, ...xs] = 1");
    assert_eq!(assoc.bindings.len(), 1);
    assert!(matches!(assoc.bindings[0].origin, SpecOrigin::Explicit(_)));
}
