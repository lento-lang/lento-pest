// Tests for bidirectional clause inference: parameter patterns are checked
// against fresh type variables, annotations unify, bodies infer, and the
// clause type is the curried `P1 -> ... -> Pn -> R`.

use lento::infer::{base_env, ctor, infer_clause, infer_function_group, InferCtx, TypeErrorKind};
use lento::parser::parse_program;
use lento::semantics::collect_function_groups;
use lento::types::{MonoType, TypeEnv};

fn var(id: u32) -> MonoType {
    MonoType::Var(id)
}
fn arrow(a: MonoType, b: MonoType) -> MonoType {
    MonoType::Function(Box::new(a), Box::new(b))
}
fn list(a: MonoType) -> MonoType {
    MonoType::List(Box::new(a))
}
fn con(n: &str) -> MonoType {
    MonoType::Constructor(n.to_string(), vec![])
}

/// Parse a single `fn` clause and infer it in a fresh context.
fn infer_one(src: &str) -> (MonoType, InferCtx) {
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let clause = infer_clause(&mut ctx, &group.raw_clauses[0], &env).unwrap();
    (clause.ty, ctx)
}

#[test]
fn identity_clause_infers_a_to_a() {
    // fn id x = x   ==>   ?0 -> ?0
    let (ty, ctx) = infer_one("fn id x = x");
    let ty = ctx.resolve(&ty);
    assert_eq!(ty, arrow(var(0), var(0)));
}

#[test]
fn constant_clause_infers_input_to_int() {
    // fn const x = 42   ==>   ?0 -> int
    let (ty, ctx) = infer_one("fn const x = 42");
    let ty = ctx.resolve(&ty);
    assert_eq!(ty, arrow(var(0), ctor::int()));
}

#[test]
fn two_params_curry() {
    // fn add a b = a + b   ==>   int -> int -> int (arithmetic unifies operands)
    let (ty, ctx) = infer_one("fn add a b = a + b");
    let ty = ctx.resolve(&ty);
    // Both params unify to one numeric type var, result is that type.
    match ty {
        MonoType::Function(a, rest) => match *rest {
            MonoType::Function(b, r) => {
                assert_eq!(*a, *b);
                assert_eq!(*b, *r);
            }
            other => panic!("expected curried fn, got {other:?}"),
        },
        other => panic!("expected fn type, got {other:?}"),
    }
}

#[test]
fn parameter_annotation_constrains_type() {
    // fn f (x : int) = x   ==>   int -> int
    let (ty, ctx) = infer_one("fn f (x : int) = x");
    let ty = ctx.resolve(&ty);
    assert_eq!(ty, arrow(ctor::int(), ctor::int()));
}

#[test]
fn annotation_mismatch_with_body_is_rejected() {
    // fn f (x : int) = "s"   -- body str, x int; no direct conflict here since
    // body doesn't use x. But a declared return conflicts:
    // fn f (x : int) -> str = x  is fine (int vs str on return) -> error.
    let ast = parse_program("fn f (x : int) -> str = x").unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let err = infer_clause(&mut ctx, &group.raw_clauses[0], &env).unwrap_err();
    assert!(matches!(err.kind, TypeErrorKind::Unify(_)));
}

#[test]
fn tuple_pattern_destructures() {
    // fn fst (a, b) = a   ==>   (?0, ?1) -> ?0
    let (ty, ctx) = infer_one("fn fst (a, b) = a");
    let ty = ctx.resolve(&ty);
    match ty {
        MonoType::Function(param, ret) => match *param {
            MonoType::Tuple(items) => {
                assert_eq!(items.len(), 2);
                assert_eq!(items[0], *ret);
            }
            other => panic!("expected tuple param, got {other:?}"),
        },
        other => panic!("expected fn type, got {other:?}"),
    }
}

#[test]
fn list_pattern_binds_element_type() {
    // fn head2 [x] = x   ==>   [?0] -> ?0  (element binds to the param's elem)
    let (ty, ctx) = infer_one("fn head2 [x] = x");
    let ty = ctx.resolve(&ty);
    match ty {
        MonoType::Function(param, ret) => match *param {
            MonoType::List(elem) => assert_eq!(*elem, *ret),
            other => panic!("expected list param, got {other:?}"),
        },
        other => panic!("expected fn type, got {other:?}"),
    }
}

#[test]
fn literal_pattern_constrains_domain() {
    // fn f 0 = "zero"   ==>   int -> str
    let (ty, ctx) = infer_one("fn f 0 = \"zero\"");
    let ty = ctx.resolve(&ty);
    assert_eq!(ty, arrow(ctor::int(), ctor::str()));
}

#[test]
fn declared_return_type_unifies_with_body() {
    // fn f x -> int = x   ==>   int -> int
    let (ty, ctx) = infer_one("fn f x -> int = x");
    let ty = ctx.resolve(&ty);
    assert_eq!(ty, arrow(ctor::int(), ctor::int()));
}

#[test]
fn unbound_variable_is_reported() {
    let ast = parse_program("fn f x = y").unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let err = infer_clause(&mut ctx, &group.raw_clauses[0], &env).unwrap_err();
    assert!(matches!(err.kind, TypeErrorKind::UnboundVariable(n) if n == "y"));
}

#[test]
fn map_clauses_share_one_group_and_infer_list_types() {
    // The two value-pattern clauses refine the same [a] second-parameter
    // domain. Non-recursive bodies keep the test focused on grouping + the
    // shared list domain (recursion is the SCC phase's concern).
    let src = "fn map2 f [] = []\nfn map2 f [x, ...xs] = [f x]";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    assert_eq!(group.raw_clauses.len(), 2);

    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let inferred = infer_function_group(&mut ctx, group, &env).unwrap();
    assert_eq!(inferred.clause_types.len(), 2);
    // Both clauses have list-shaped second params, refining one [a] domain.
    for ty in &inferred.clause_types {
        match ty {
            MonoType::Function(_, rest) => match &**rest {
                MonoType::Function(param, _) => {
                    assert!(matches!(ctx.resolve(param), MonoType::List(_)))
                }
                other => panic!("expected curried fn, got {other:?}"),
            },
            other => panic!("expected fn type, got {other:?}"),
        }
    }
}

#[test]
fn clause_types_keep_pattern_and_type_dispatch_separate() {
    // Both the inferred type AND the pattern vector are retained.
    let src = "fn g (a, b) = a";
    let ast = parse_program(src).unwrap();
    let collected = collect_function_groups(&ast).unwrap();
    let group = &collected.function_groups[0];
    let mut ctx = InferCtx::new();
    let env = base_env(&mut ctx.supply);
    let clause = infer_clause(&mut ctx, &group.raw_clauses[0], &env).unwrap();
    assert_eq!(clause.patterns.len(), 1);
    assert!(matches!(
        clause.patterns[0].kind,
        lento::ast::PatKind::Tuple(_)
    ));
    // Type is a function from a tuple, not a tuple of functions.
    assert!(matches!(ctx.resolve(&clause.ty), MonoType::Function(_, _)));
}

#[test]
fn base_env_has_intrinsics() {
    let mut supply = lento::types::TypeVarSupply::new();
    let env: TypeEnv = base_env(&mut supply);
    assert!(env.contains_key("concat"));
    assert!(env.contains_key("map"));
    assert!(env.contains_key("head"));
}

#[test]
fn application_of_intrinsic_infers() {
    // fn f xs = concat xs xs  ==>  a -> a
    let (ty, ctx) = infer_one("fn f xs = concat xs xs");
    let ty = ctx.resolve(&ty);
    match ty {
        MonoType::Function(param, ret) => {
            assert_eq!(ctx.resolve(&param), ctx.resolve(&ret));
        }
        other => panic!("expected fn type, got {other:?}"),
    }
    let _ = (list, con);
}
