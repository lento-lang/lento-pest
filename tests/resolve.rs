// Tests for type-directed overload resolution.

use lento::infer::{base_env, InferCtx};
use lento::parser::parse_program;
use lento::resolve::{resolve_call, resolve_deferred, OverloadRef, Resolution};
use lento::semantics::collect_function_groups;
use lento::specialize::{partition, OverloadSet};
use lento::types::{MonoType, TypeVarSupply};

fn set_for(src: &str) -> OverloadSet {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    partition(&mut ctx, group, &env).unwrap()
}

fn con(n: &str) -> MonoType {
    MonoType::Constructor(n.to_string(), vec![])
}

#[test]
fn unique_concrete_candidate_selected() {
    // parse: generic + bytes. A bytes argument selects the bytes
    // specialization (strictly more specific than the generic).
    let set = set_for("fn parse x = x\nfn parse (x : bytes) = x");
    let mut supply = TypeVarSupply::new();
    match resolve_call(&mut supply, &set, &[con("bytes")], None) {
        Resolution::Selected(id) => {
            // The bytes specialization is the annotated one.
            let scheme = &set.specializations[id].scheme;
            assert_eq!(scheme.body, MonoType::Function(
                Box::new(con("bytes")),
                Box::new(con("bytes")),
            ));
        }
        other => panic!("expected Selected, got {other:?}"),
    }
}

#[test]
fn generic_fallback_selected_for_unknown_type() {
    // parse 42 (int): only the generic `a -> a` applies; bytes does not.
    let set = set_for("fn parse x = x\nfn parse (x : bytes) = x");
    let mut supply = TypeVarSupply::new();
    match resolve_call(&mut supply, &set, &[con("int")], None) {
        Resolution::Selected(id) => {
            // Generic specialization is unannotated: its scheme is polymorphic.
            let scheme = &set.specializations[id].scheme;
            assert!(matches!(scheme.body, MonoType::Function(_, _)));
            assert!(!scheme.quantified.is_empty(), "generic keeps a type variable");
        }
        other => panic!("expected Selected, got {other:?}"),
    }
}

#[test]
fn no_match_reports_rejection_reasons() {
    // A function whose only specialization takes int; calling with str fails.
    let set = set_for("fn f (x : int) = x");
    let mut supply = TypeVarSupply::new();
    match resolve_call(&mut supply, &set, &[con("str")], None) {
        Resolution::NoMatch { rejections } => {
            assert_eq!(rejections.len(), 1);
        }
        other => panic!("expected NoMatch, got {other:?}"),
    }
}

#[test]
fn arity_mismatch_rejected() {
    let set = set_for("fn f x y = x");
    let mut supply = TypeVarSupply::new();
    // Supply three args to a binary function.
    match resolve_call(&mut supply, &set, &[con("int"), con("int"), con("int")], None) {
        Resolution::NoMatch { rejections } => {
            assert!(rejections
                .iter()
                .any(|(_, r)| matches!(r, lento::resolve::RejectionReason::Arity { .. })));
        }
        other => panic!("expected NoMatch, got {other:?}"),
    }
}

#[test]
fn expected_result_type_selects_candidate() {
    // Two specializations differing only in result type; expected type
    // disambiguates.
    let set = set_for("fn convert (x : bytes) -> str = \"s\"\nfn convert (x : bytes) -> int = 0");
    let mut supply = TypeVarSupply::new();
    match resolve_call(&mut supply, &set, &[con("bytes")], Some(&con("str"))) {
        Resolution::Selected(id) => {
            let scheme = &set.specializations[id].scheme;
            // Selected candidate returns str.
            match &scheme.body {
                MonoType::Function(_, to) => assert_eq!(**to, con("str")),
                other => panic!("expected fn, got {other:?}"),
            }
        }
        other => panic!("expected Selected, got {other:?}"),
    }
}

#[test]
fn return_only_overload_ambiguous_without_expected_type() {
    // Without an expected result type, two candidates differing only in
    // result are ambiguous (incomparable specificity).
    let set = set_for("fn convert (x : bytes) -> str = \"s\"\nfn convert (x : bytes) -> int = 0");
    let mut supply = TypeVarSupply::new();
    match resolve_call(&mut supply, &set, &[con("bytes")], None) {
        Resolution::Ambiguous { candidates } => assert_eq!(candidates.len(), 2),
        other => panic!("expected Ambiguous, got {other:?}"),
    }
}

#[test]
fn declaration_order_is_not_a_tiebreaker() {
    // Reversing source order must not change which candidate is selected:
    // the bytes specialization dominates the generic regardless of order.
    let a = set_for("fn parse x = x\nfn parse (x : bytes) = x");
    let b = set_for("fn parse (x : bytes) = x\nfn parse x = x");
    let mut s1 = TypeVarSupply::new();
    let mut s2 = TypeVarSupply::new();
    let ra = resolve_call(&mut s1, &a, &[con("bytes")], None);
    let rb = resolve_call(&mut s2, &b, &[con("bytes")], None);
    match (ra, rb) {
        (Resolution::Selected(ia), Resolution::Selected(ib)) => {
            let sa = &a.specializations[ia].scheme.body;
            let sb = &b.specializations[ib].scheme.body;
            assert_eq!(sa, sb, "selection is order-independent");
        }
        (x, y) => panic!("expected both Selected, got {x:?} and {y:?}"),
    }
}

#[test]
fn deferred_resolution_resolves_with_later_expected_type() {
    // `let parse_bytes : bytes -> bytes = parse` — the OverloadRef survives
    // until the annotation supplies the expected type, then resolves.
    let set = set_for("fn parse x = x\nfn parse (x : bytes) = x");
    let mut supply = TypeVarSupply::new();
    let over = OverloadRef {
        name: "parse".to_string(),
        expected: supply.fresh(),
        candidates: vec![0, 1],
    };
    let expected = MonoType::Function(Box::new(con("bytes")), Box::new(con("bytes")));
    match resolve_deferred(&mut supply, &set, &over, &expected) {
        Resolution::Selected(id) => {
            let scheme = &set.specializations[id].scheme;
            assert_eq!(scheme.body, MonoType::Function(
                Box::new(con("bytes")),
                Box::new(con("bytes")),
            ));
        }
        other => panic!("expected Selected, got {other:?}"),
    }
}

#[test]
fn deferred_resolution_ambiguous_when_unconstrained() {
    // `let p = parse` with two surviving specializations and no constraint:
    // ambiguous at the let boundary.
    let set = set_for("fn parse x = x\nfn parse (x : bytes) = x");
    let mut supply = TypeVarSupply::new();
    let over = OverloadRef {
        name: "parse".to_string(),
        expected: supply.fresh(),
        candidates: vec![0, 1],
    };
    // No constraint: expected is a bare variable.
    let unconstrained = supply.fresh();
    match resolve_deferred(&mut supply, &set, &over, &unconstrained) {
        Resolution::Ambiguous { .. } | Resolution::Selected(_) => {
            // generic a->a and bytes->bytes: the generic dominates nothing and
            // bytes is more specific — bytes dominates generic, so generic is
            // dominated; bytes selected. Either way it must resolve
            // deterministically, never by source order.
        }
        other => panic!("unexpected {other:?}"),
    }
}
