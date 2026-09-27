// Tests for the internal Hindley–Milner type representation: fresh
// variables, capture-avoiding substitution, occurs check, unification,
// instantiation, generalization, alpha-equivalence/canonicalization, and
// surface-type lowering (no inferred variable is ever `Ty::Named`).

use std::collections::BTreeMap;

use lento::ast::{Constraint, Ty};
use lento::types::{
    alpha_equiv, canonicalize, dominates, generalize, implementation_covers_spec, instantiate,
    is_instance, lower_ty, skolemize, unify, MonoSumAlt, MonoType, SchemeConstraint, Substitution,
    TypeEnv, TypeScheme, TypeVarSupply, UnifyError,
};

fn var(id: u32) -> MonoType {
    MonoType::Var(id)
}

fn con(name: &str, args: Vec<MonoType>) -> MonoType {
    MonoType::Constructor(name.to_string(), args)
}

fn arrow(from: MonoType, to: MonoType) -> MonoType {
    MonoType::Function(Box::new(from), Box::new(to))
}

fn list(inner: MonoType) -> MonoType {
    MonoType::List(Box::new(inner))
}

#[test]
fn solved_record_tail_is_materialized_by_substitution() {
    let mut subst = Substitution::new();
    let open = MonoType::Record { fields: vec![("a".into(), con("int", vec![]))], rest: Some(42) };
    let closed = MonoType::Record { fields: vec![("a".into(), con("int", vec![])), ("b".into(), con("str", vec![]))], rest: None };
    unify(&mut subst, &open, &closed).unwrap();
    assert_eq!(subst.apply(&open), closed);
}

#[test]
fn independently_reconciled_rows_do_not_share_a_fresh_tail() {
    let mut subst = Substitution::new();
    let open = |name: &str, tail| MonoType::Record { fields: vec![(name.into(), con("int", vec![]))], rest: Some(tail) };
    unify(&mut subst, &open("a", 10), &open("b", 11)).unwrap();
    unify(&mut subst, &open("c", 12), &open("d", 13)).unwrap();
    assert_ne!(subst.apply(&var(10)), subst.apply(&var(12)));
}

#[test]
fn nominal_sums_keep_identity_and_structural_sums_check_payloads() {
    use lento::types::MonoSumAlt;
    let sum = |name: &str, payload: &str| MonoType::Sum {
        name: name.into(), args: vec![],
        alts: vec![MonoSumAlt::Constructor { name: "Some".into(), payload: Some(con(payload, vec![])) }],
    };
    assert!(unify(&mut Substitution::new(), &sum("Left", "int"), &sum("Right", "int")).is_err());
    assert!(unify(&mut Substitution::new(), &sum("<sum:1>", "int"), &sum("<sum:1>", "str")).is_err());
}

// -- fresh variables --------------------------------------------------------

#[test]
fn fresh_variables_are_distinct_and_monotonic() {
    let mut supply = TypeVarSupply::new();
    let a = supply.fresh();
    let b = supply.fresh();
    let c = supply.fresh();
    assert_eq!(a, var(0));
    assert_eq!(b, var(1));
    assert_eq!(c, var(2));
    assert_ne!(a, b);
}

// -- substitution -----------------------------------------------------------

#[test]
fn substitution_applies_recursively() {
    let mut s = Substitution::new();
    s.insert(0, con("int", vec![]));
    // ?0 -> [?0] with ?0 |-> int  ==  int -> [int]
    let ty = arrow(var(0), list(var(0)));
    assert_eq!(
        s.apply(&ty),
        arrow(con("int", vec![]), list(con("int", vec![])))
    );
}

#[test]
fn substitution_composition_is_sequential() {
    // s1: ?0 |-> ?1 ; s2: ?1 |-> int. (s2 ∘ s1)(?0) = int.
    let s1 = Substitution::singleton(0, var(1));
    let s2 = Substitution::singleton(1, con("int", vec![]));
    let composed = s2.compose(&s1);
    assert_eq!(composed.apply(&var(0)), con("int", vec![]));
    assert_eq!(composed.apply(&var(1)), con("int", vec![]));
}

#[test]
fn substitution_under_binder_is_capture_avoiding() {
    // Scheme ∀?1. ?0 -> ?1 with subst ?1 |-> int: the quantified ?1 must NOT
    // be substituted; the free ?0 is untouched because the subst says nothing
    // about it.
    let scheme = TypeScheme {
        quantified: vec![1],
        constraints: vec![],
        body: arrow(var(0), var(1)),
    };
    let s = Substitution::singleton(1, con("int", vec![]));
    let out = s.apply_scheme(&scheme);
    assert_eq!(out.body, arrow(var(0), var(1)));
    assert_eq!(out.quantified, vec![1]);
}

// -- occurs check / unification ----------------------------------------------

#[test]
fn occurs_check_rejects_infinite_types() {
    // ?0 ~ [?0] would be infinite.
    let mut s = Substitution::new();
    let err = unify(&mut s, &var(0), &list(var(0))).unwrap_err();
    assert!(matches!(err, UnifyError::Occurs { var: 0, .. }));
}

#[test]
fn unification_binds_variables() {
    // unify(?0 -> ?1, int -> str) = {?0 |-> int, ?1 |-> str}
    let mut s = Substitution::new();
    unify(
        &mut s,
        &arrow(var(0), var(1)),
        &arrow(con("int", vec![]), con("str", vec![])),
    )
    .unwrap();
    assert_eq!(s.apply(&var(0)), con("int", vec![]));
    assert_eq!(s.apply(&var(1)), con("str", vec![]));
}

#[test]
fn unification_rejects_mismatched_constructors() {
    let mut s = Substitution::new();
    let err = unify(&mut s, &con("int", vec![]), &con("str", vec![])).unwrap_err();
    assert!(matches!(err, UnifyError::Mismatch { .. }));
}

#[test]
fn nominal_sum_and_named_type_representations_agree() {
    let option = MonoType::Sum {
        name: "Option".into(),
        args: vec![var(0)],
        alts: vec![
            MonoSumAlt::Constructor { name: "None".into(), payload: None },
            MonoSumAlt::Constructor { name: "Some".into(), payload: Some(var(0)) },
        ],
    };
    let named = con("Option", vec![con("int", vec![])]);
    let mut substitution = Substitution::new();
    unify(&mut substitution, &option, &named).expect("same nominal sum should unify");
    assert_eq!(substitution.apply(&var(0)), con("int", vec![]));
    assert!(unify(&mut Substitution::new(), &option, &con("Other", vec![var(0)])).is_err());

    let implementation = TypeScheme {
        quantified: vec![0],
        constraints: vec![],
        body: arrow(option, con("bool", vec![])),
    };
    let specification = TypeScheme {
        quantified: vec![1],
        constraints: vec![],
        body: arrow(con("Option", vec![var(1)]), con("bool", vec![])),
    };
    assert!(implementation_covers_spec(&mut TypeVarSupply::new(), &implementation, &specification));
}

#[test]
fn unification_rejects_arity_mismatch() {
    let mut s = Substitution::new();
    let err = unify(
        &mut s,
        &MonoType::Tuple(vec![con("int", vec![])]),
        &MonoType::Tuple(vec![con("int", vec![]), con("int", vec![])]),
    )
    .unwrap_err();
    assert!(matches!(err, UnifyError::Mismatch { .. }));
}

#[test]
fn unification_is_structural_for_functions_tuples_and_lists() {
    // unify(?0 -> (?1, [?1]), str -> (bool, [bool]))
    let mut s = Substitution::new();
    unify(
        &mut s,
        &arrow(
            var(0),
            MonoType::Tuple(vec![var(1), list(var(1))]),
        ),
        &arrow(
            con("str", vec![]),
            MonoType::Tuple(vec![con("bool", vec![]), list(con("bool", vec![]))]),
        ),
    )
    .unwrap();
    assert_eq!(s.apply(&var(0)), con("str", vec![]));
    assert_eq!(s.apply(&var(1)), con("bool", vec![]));
}

// -- instantiation / generalization -------------------------------------------

#[test]
fn instantiation_refreshes_quantified_variables() {
    // ∀?5. ?5 -> ?5 instantiates to ?0 -> ?0 with a fresh supply: the two
    // occurrences share ONE fresh variable.
    let mut supply = TypeVarSupply::new();
    let scheme = TypeScheme {
        quantified: vec![5],
        constraints: vec![],
        body: arrow(var(5), var(5)),
    };
    let (body, _) = instantiate(&mut supply, &scheme);
    assert_eq!(body, arrow(var(0), var(0)));
    // A second instantiation gets a different variable.
    let (body2, _) = instantiate(&mut supply, &scheme);
    assert_eq!(body2, arrow(var(1), var(1)));
}

#[test]
fn generalization_quantifies_only_variables_not_free_in_env() {
    // env: { y : ?0 }. Generalize ?0 -> ?1: ?0 is free in env, so only ?1 is
    // quantified.
    let mut env = TypeEnv::new();
    env.insert("y".to_string(), TypeScheme::mono(var(0)));
    let scheme = generalize(&env, &arrow(var(0), var(1)), vec![]);
    assert_eq!(scheme.quantified, vec![1]);
    assert_eq!(scheme.body, arrow(var(0), var(1)));

    // With an empty env both are quantified.
    let scheme = generalize(&TypeEnv::new(), &arrow(var(0), var(1)), vec![]);
    assert_eq!(scheme.quantified, vec![0, 1]);
}

// -- alpha-equivalence / canonicalization --------------------------------------

#[test]
fn alpha_equivalent_schemes_canonicalize_equal() {
    // ∀?7. ?7 -> ?7  ==  ∀?2. ?2 -> ?2
    let a = TypeScheme {
        quantified: vec![7],
        constraints: vec![],
        body: arrow(var(7), var(7)),
    };
    let b = TypeScheme {
        quantified: vec![2],
        constraints: vec![],
        body: arrow(var(2), var(2)),
    };
    assert!(alpha_equiv(&a, &b));
    assert_eq!(canonicalize(&a), canonicalize(&b));
}

#[test]
fn alpha_inequivalent_schemes_differ() {
    // ∀ab. a -> b  !=  ∀a. a -> a
    let a = TypeScheme {
        quantified: vec![0, 1],
        constraints: vec![],
        body: arrow(var(0), var(1)),
    };
    let b = TypeScheme {
        quantified: vec![0],
        constraints: vec![],
        body: arrow(var(0), var(0)),
    };
    assert!(!alpha_equiv(&a, &b));
}

#[test]
fn canonicalization_orders_by_first_occurrence() {
    // ∀?3 ?1. ?1 -> ?3  canonicalizes to ∀0 1. 0 -> 1 (body order, not id
    // order).
    let s = TypeScheme {
        quantified: vec![3, 1],
        constraints: vec![],
        body: arrow(var(1), var(3)),
    };
    let canon = canonicalize(&s);
    assert_eq!(canon.quantified, vec![0, 1]);
    assert_eq!(canon.body, arrow(var(0), var(1)));
}

#[test]
fn canonicalization_includes_constraint_only_variables() {
    // `all a :: Ord. int -> int` — `a` occurs only in the constraint.
    let s = TypeScheme {
        quantified: vec![4],
        constraints: vec![SchemeConstraint {
            name: "Ord".to_string(),
            args: vec![var(4)],
        }],
        body: arrow(con("int", vec![]), con("int", vec![])),
    };
    let canon = canonicalize(&s);
    assert_eq!(canon.quantified, vec![0]);
    assert_eq!(canon.constraints[0].args, vec![var(0)]);
}

// -- surface-type lowering ------------------------------------------------------

#[test]
fn lower_ty_resolves_quantified_binders_to_variables() {
    // `all a b. a -> b` lowers `a`/`b` to the binder variables, everything
    // else to constructors.
    let mut binders = BTreeMap::new();
    binders.insert("a".to_string(), var(10));
    binders.insert("b".to_string(), var(11));
    let surface = Ty::Arrow {
        from: Box::new(Ty::Named {
            name: "a".to_string(),
            args: vec![],
        }),
        to: Box::new(Ty::Named {
            name: "b".to_string(),
            args: vec![],
        }),
    };
    assert_eq!(lower_ty(&surface, &binders), arrow(var(10), var(11)));
}

#[test]
fn lower_ty_keeps_unknown_names_as_constructors_never_variables() {
    // `int -> [str]` with no binders: real nominal types, no variables.
    let surface = Ty::Arrow {
        from: Box::new(Ty::Named {
            name: "int".to_string(),
            args: vec![],
        }),
        to: Box::new(Ty::List(Box::new(Ty::Named {
            name: "str".to_string(),
            args: vec![],
        }))),
    };
    assert_eq!(
        lower_ty(&surface, &BTreeMap::new()),
        arrow(con("int", vec![]), list(con("str", vec![])))
    );
}

#[test]
fn lower_ty_never_turns_a_bare_parameter_name_into_a_nominal_type() {
    // The old `param_type(x)` produced `Ty::Named("x")`. Lowering a surface
    // type for a parameter must go through the binder environment: an
    // unbound name stays a constructor (it names a *type*, not a variable);
    // parameter types come from `TypeVarSupply::fresh`, never from names.
    let surface = Ty::Named {
        name: "x".to_string(),
        args: vec![],
    };
    assert_eq!(
        lower_ty(&surface, &BTreeMap::new()),
        con("x", vec![])
    );
    // With a binder in scope the same name resolves to that variable.
    let mut binders = BTreeMap::new();
    binders.insert("x".to_string(), var(3));
    assert_eq!(lower_ty(&surface, &binders), var(3));
}

#[test]
fn lower_ty_handles_tuples_arrows_and_memory_markers() {
    let surface = Ty::Tuple(vec![
        Ty::Arrow {
            from: Box::new(Ty::Named {
                name: "int".into(),
                args: vec![],
            }),
            to: Box::new(Ty::Named {
                name: "int".into(),
                args: vec![],
            }),
        },
        Ty::Ref(Box::new(Ty::Named {
            name: "str".into(),
            args: vec![],
        })),
        Ty::Mut(Box::new(Ty::Named {
            name: "bool".into(),
            args: vec![],
        })),
    ]);
    let lowered = lower_ty(&surface, &BTreeMap::new());
    assert_eq!(
        lowered,
        MonoType::Tuple(vec![
            arrow(con("int", vec![]), con("int", vec![])),
            MonoType::Ref(Box::new(con("str", vec![]))),
            MonoType::Mut(Box::new(con("bool", vec![]))),
        ])
    );
}

#[test]
fn lower_ty_lowers_constraint_arguments() {
    let mut binders = BTreeMap::new();
    binders.insert("a".to_string(), var(0));
    let c = Constraint {
        name: "Ord".to_string(),
        args: vec![Ty::Named {
            name: "a".to_string(),
            args: vec![],
        }],
    };
    let lowered = lento::types::lower_constraint(&c, &binders);
    assert_eq!(lowered.name, "Ord");
    assert_eq!(lowered.args, vec![var(0)]);
}

// -- skolemization / subsumption / specificity --------------------------------

#[test]
fn skolemization_uses_rigid_fresh_variables() {
    let mut supply = TypeVarSupply::new();
    let scheme = TypeScheme {
        quantified: vec![9],
        constraints: vec![],
        body: arrow(var(9), list(var(9))),
    };
    let (body, skolems) = skolemize(&mut supply, &scheme);
    assert_eq!(skolems, vec![0]);
    assert_eq!(body, arrow(var(0), list(var(0))));
}

#[test]
fn more_general_is_instance_of_less_general_direction() {
    let mut supply = TypeVarSupply::new();
    // int -> int is an instance of ∀a. a -> a.
    let general = TypeScheme {
        quantified: vec![0],
        constraints: vec![],
        body: arrow(var(0), var(0)),
    };
    let concrete = TypeScheme::mono(arrow(con("int", vec![]), con("int", vec![])));
    assert!(is_instance(&mut supply, &general, &concrete));
    // ∀a. a -> a is NOT an instance of int -> int.
    assert!(!is_instance(&mut supply, &concrete, &general));
}

#[test]
fn instance_respects_structure() {
    let mut supply = TypeVarSupply::new();
    // ∀a b. a -> b has int -> str as an instance but not vice versa.
    let general = TypeScheme {
        quantified: vec![0, 1],
        constraints: vec![],
        body: arrow(var(0), var(1)),
    };
    let concrete = TypeScheme::mono(arrow(con("int", vec![]), con("str", vec![])));
    assert!(is_instance(&mut supply, &general, &concrete));
    assert!(!is_instance(&mut supply, &concrete, &general));
}

#[test]
fn bytes_ast_does_not_dominate_generic_but_generic_does_not_dominate_bytes() {
    // `bytes -> Ast` is a strict specialization of `∀a. a -> Ast`:
    // dominates(bytes -> Ast, ∀a. a -> Ast) holds, and the reverse does not.
    let mut supply = TypeVarSupply::new();
    let generic = TypeScheme {
        quantified: vec![0],
        constraints: vec![],
        body: arrow(var(0), con("Ast", vec![])),
    };
    let bytes = TypeScheme::mono(arrow(con("bytes", vec![]), con("Ast", vec![])));
    assert!(dominates(&mut supply, &bytes, &generic));
    assert!(!dominates(&mut supply, &generic, &bytes));
}

#[test]
fn equivalent_schemes_do_not_strictly_dominate() {
    let mut supply = TypeVarSupply::new();
    // Two alpha-equivalent schemes: each is an instance of the other, so
    // neither strictly dominates.
    let a = TypeScheme {
        quantified: vec![0],
        constraints: vec![],
        body: arrow(var(0), var(0)),
    };
    let b = TypeScheme {
        quantified: vec![5],
        constraints: vec![],
        body: arrow(var(5), var(5)),
    };
    assert!(!dominates(&mut supply, &a, &b));
    assert!(!dominates(&mut supply, &b, &a));
}
