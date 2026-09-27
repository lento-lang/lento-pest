// Tests for spec association under the corrected semantic model:
//   - satisfaction is directional subsumption (impl at least as general);
//   - implementations with zero specs are valid (inferred signature);
//   - one specialization must cover an entire spec;
//   - abstract (spec-only) groups are exempt.

use lento::infer::{base_env, InferCtx};
use lento::parser::parse_program;
use lento::semantics::collect_function_groups;
use lento::specialize::partition;
use lento::specs::{associate_specs, SignatureOrigin, SpecErrorKind};
use lento::types::TypeVarSupply;
use std::collections::BTreeMap;

fn associate(src: &str) -> lento::specs::SpecAssociation {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    associate_specs(&mut supply, group, &set, &BTreeMap::new()).unwrap()
}

fn associate_err(src: &str) -> SpecErrorKind {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    associate_specs(&mut supply, group, &set, &BTreeMap::new())
        .unwrap_err()
        .kind
}

#[test]
fn general_implementation_satisfies_specific_spec() {
    // ∀a. a->a  satisfies  spec int -> int  (Instances(int->int) ⊆ Instances(∀a.a->a)).
    let assoc = associate("spec h: int -> int\nfn h x = x");
    assert_eq!(assoc.signatures.len(), 1);
    assert!(matches!(assoc.signatures[0].origin, SignatureOrigin::SpecAssisted(_)));
    assert!(assoc.unsatisfied.is_empty());
}

#[test]
fn concrete_implementation_does_not_satisfy_universal_spec() {
    // int->int does NOT satisfy spec all a. a -> a.
    let err = associate_err("spec f: all a. a -> a\nfn f (x : int) = x");
    assert!(matches!(err, SpecErrorKind::UnsatisfiedSpec { .. }));
}

#[test]
fn implementation_with_no_spec_gets_inferred_signature_not_obligation() {
    // No spec: valid, and the signature is Inferred (not a spec obligation).
    let assoc = associate("fn id x = x");
    assert_eq!(assoc.signatures.len(), 1);
    assert!(matches!(assoc.signatures[0].origin, SignatureOrigin::Inferred));
    // The inferred signature is generalized (quantifies its variable).
    assert_eq!(assoc.signatures[0].scheme.quantified.len(), 1);
}

#[test]
fn declared_spec_signature_uses_spec_scheme() {
    let assoc = associate("spec id: all a. a -> a\nfn id x = x");
    assert_eq!(assoc.signatures.len(), 1);
    assert!(matches!(assoc.signatures[0].origin, SignatureOrigin::SpecAssisted(_)));
}

#[test]
fn unrelated_concrete_impl_leaves_spec_unsatisfied() {
    // spec str -> str; only an int->int implementation exists.
    let err = associate_err("spec k: str -> str\nfn k (x : int) = x");
    assert!(matches!(err, SpecErrorKind::UnsatisfiedSpec { .. }));
}

#[test]
fn abstract_spec_only_group_is_allowed() {
    let ast = parse_program("spec convert: all a. a -> str").unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    let mut supply = TypeVarSupply::new();
    let assoc = associate_specs(&mut supply, group, &set, &BTreeMap::new()).unwrap();
    assert!(assoc.signatures.is_empty());
}

#[test]
fn value_pattern_clauses_in_one_specialization_cover_spec() {
    // [] and cons clauses form ONE specialization covering [a] -> int.
    let assoc = associate("spec len2: all a. [a] -> int\nfn len2 [] = 0\nfn len2 [x, ...xs] = 1");
    assert_eq!(assoc.signatures.len(), 1);
    assert!(matches!(assoc.signatures[0].origin, SignatureOrigin::SpecAssisted(_)));
}

#[test]
fn extra_specialization_without_spec_is_not_an_error() {
    // The annotated `bytes` specialization has no spec of its own; that is
    // valid (specs optional). The generic spec is still covered by the
    // generic clause's specialization.
    let assoc = associate("spec p: all a. a -> a\nfn p x = x\nfn p (x : bytes) = x");
    assert_eq!(assoc.signatures.len(), 2);
    // At least one signature is Declared (covering the spec); the other may be
    // Declared too (bytes->bytes also satisfies ∀a.a->a) — either way, no error
    // and both specializations get a signature.
    assert!(assoc
        .signatures
        .iter()
        .any(|s| matches!(s.origin, SignatureOrigin::SpecAssisted(_))));
    assert!(assoc.unsatisfied.is_empty());
}

#[test]
fn shared_open_row_must_absorb_consistently() {
    // The implementation's row variable appears in both parameter and result
    // positions; riding spec fields into one position must not silently
    // accept a contradictory shape in the other.
    let contradictory = associate_err(
        "spec f : { x: int, y: int } -> { x: int, y: int, z: int }\n\
         fn f value = value",
    );
    assert!(
        matches!(contradictory, SpecErrorKind::UnsatisfiedSpec { .. }),
        "expected the contradictory row shape to be rejected, got {contradictory:?}"
    );
}

#[test]
fn open_row_binding_respects_spec_field_types() {
    // `y` rides the row on the parameter side with type int; the result
    // side then demands y : str, which the bound row cannot provide.
    let contradictory = associate_err(
        "spec f : { x: int, y: int } -> { x: str, y: bool }\n\
         fn f value = { y: false }",
    );
    assert!(
        matches!(contradictory, SpecErrorKind::UnsatisfiedSpec { .. }),
        "expected the type-contradictory ride to be rejected, got {contradictory:?}"
    );
}

#[test]
fn open_row_ride_rejects_spec_demanding_unknown_field() {
    // The implementation only reads `x`; the spec's result demands `z`,
    // which the row pinned on the parameter side cannot supply. This is the
    // headline case the absorb binding fixes (accepted before it).
    let rejected = associate_err(
        "spec f : { x: int, y: int } -> { x: int, y: int, z: int }\n\
         fn f { x, ...rest } = { x: x, ...rest }",
    );
    assert!(
        matches!(rejected, SpecErrorKind::UnsatisfiedSpec { .. }),
        "expected the unknown-field demand to be rejected, got {rejected:?}"
    );
}

#[test]
fn open_row_ride_accepts_consistent_shape() {
    // The spec's extra field `y` rides the row in both positions with the
    // same shape, so the single binding satisfies both demands.
    let assoc = associate(
        "spec f : { x: int, y: int } -> { x: int, y: int }\n\
         fn f { x, ...rest } = { x: x, ...rest }",
    );
    assert!(assoc.unsatisfied.is_empty(), "{:?}", assoc.unsatisfied);
}

#[test]
fn open_row_binding_rejects_wider_result_demand() {
    // The row is pinned to `y : [int | str]` on the parameter side; the
    // result demands `y : [int | str | bool]`, which the image cannot
    // provide. The pinned image must satisfy the demand, not the reverse.
    let rejected = associate_err(
        "spec f : { x: int, y: [int | str] } -> { x: int, y: [int | str | bool] }\n\
         fn f { x, ...rest } = { x: x, ...rest }",
    );
    assert!(
        matches!(rejected, SpecErrorKind::UnsatisfiedSpec { .. }),
        "expected the wider result demand to be rejected, got {rejected:?}"
    );
}

#[test]
fn open_row_binding_accepts_narrower_result_demand() {
    // Reverse of the previous case: the image pinned on the parameter side
    // is wider than the result demand, so it satisfies it.
    let assoc = associate(
        "spec f : { x: int, y: [int | str | bool] } -> { x: int, y: [int | str] }\n\
         fn f { x, ...rest } = { x: x, ...rest }",
    );
    assert!(assoc.unsatisfied.is_empty(), "{:?}", assoc.unsatisfied);
}
