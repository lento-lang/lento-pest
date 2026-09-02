// Tests for pattern usefulness / exhaustiveness over the parameter product.

use lento::infer::{base_env, InferCtx};
use lento::parser::parse_program;
use lento::patterns::{analyze_specialization, DiagnosticKind, Severity};
use lento::semantics::collect_function_groups;
use lento::specialize::partition;

fn analyze(src: &str) -> Vec<lento::patterns::PatternDiagnostic> {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    // Analyze the (single) specialization.
    set.specializations
        .iter()
        .flat_map(analyze_specialization)
        .collect()
}

#[test]
fn catchall_first_makes_literal_clause_unreachable() {
    // fn f x = ...; fn f 0 = ... — the literal clause is unreachable.
    let diags = analyze("fn f x = x\nfn f 0 = 0");
    assert!(diags.iter().any(|d| matches!(
        d.kind,
        DiagnosticKind::UnreachableClause { index: 1 }
    )));
    // The unreachable clause is a warning, not an error.
    assert!(diags
        .iter()
        .filter(|d| matches!(d.kind, DiagnosticKind::UnreachableClause { .. }))
        .all(|d| d.severity == Severity::Warning));
}

#[test]
fn literal_first_then_catchall_is_reachable() {
    // fn f 0 = ...; fn f x = ... — both reachable; no unreachable diagnostic.
    let diags = analyze("fn f 0 = 0\nfn f x = x");
    assert!(!diags
        .iter()
        .any(|d| matches!(d.kind, DiagnosticKind::UnreachableClause { .. })));
}

#[test]
fn duplicate_clause_is_an_error() {
    // Two identical clauses: the second is a duplicate (error).
    let diags = analyze("fn f 0 = 0\nfn f 0 = 1");
    assert!(diags.iter().any(|d| matches!(
        d.kind,
        DiagnosticKind::DuplicateClause { index: 1, earlier: 0 }
    ) && d.severity == Severity::Error));
}

#[test]
fn empty_and_cons_list_are_exhaustive_together() {
    // [] and [x, ...xs] cover all lists: no non-exhaustive warning.
    let diags = analyze("fn len2 [] = 0\nfn len2 [x, ...xs] = 1");
    assert!(!diags
        .iter()
        .any(|d| matches!(d.kind, DiagnosticKind::NonExhaustive { .. })));
}

#[test]
fn singleton_list_pattern_is_non_exhaustive() {
    // [y] alone leaves [] and [_, _, ..._] uncovered.
    let diags = analyze("fn f [y] = y");
    let ne = diags.iter().find(|d| matches!(d.kind, DiagnosticKind::NonExhaustive { .. }));
    let ne = ne.expect("expected a non-exhaustive warning");
    assert_eq!(ne.severity, Severity::Warning);
    if let DiagnosticKind::NonExhaustive { witnesses } = &ne.kind {
        // At least one concrete uncovered witness is reported (the empty list
        // for `[y]`). The search returns the first uncovered vector.
        assert!(!witnesses.is_empty(), "expected witnesses");
        assert!(witnesses.iter().any(|w| w == "[]"), "witnesses: {witnesses:?}");
    }
}

#[test]
fn bool_true_only_is_non_exhaustive() {
    // Only `true` matched: `false` is uncovered.
    let diags = analyze("fn f true = 1");
    assert!(diags.iter().any(|d| matches!(&d.kind,
        DiagnosticKind::NonExhaustive { witnesses } if witnesses.iter().any(|w| w == "false")
    )));
}

#[test]
fn both_bools_exhaustive() {
    let diags = analyze("fn f true = 1\nfn f false = 0");
    assert!(!diags
        .iter()
        .any(|d| matches!(d.kind, DiagnosticKind::NonExhaustive { .. })));
}

#[test]
fn cross_specialization_catchall_does_not_affect_other() {
    // A generic catch-all in one specialization does NOT make a clause in a
    // DIFFERENT specialization unreachable (type dispatch separates them).
    let ast = parse_program("fn parse x = x\nfn parse (x : bytes) = x").unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let set = partition(&mut ctx, group, &env).unwrap();
    assert_eq!(set.specializations.len(), 2);
    // Neither specialization reports unreachable clauses.
    let diags: Vec<_> = set
        .specializations
        .iter()
        .flat_map(analyze_specialization)
        .collect();
    assert!(!diags
        .iter()
        .any(|d| matches!(d.kind, DiagnosticKind::UnreachableClause { .. })));
}

#[test]
fn multi_column_product_correlation() {
    // fn f true [] = ..; fn f false [x, ...xs] = .. — the missing witnesses
    // are the COMBINATIONS (true, [_,..._]) and (false, []), reported over
    // the product, not per-column defaults.
    let diags = analyze("fn f true [] = 0\nfn f false [x, ...xs] = 1");
    assert!(diags
        .iter()
        .any(|d| matches!(d.kind, DiagnosticKind::NonExhaustive { .. })));
}
