// `desugar_program` turns every `fn` clause into a `let` binding so the
// evaluator never sees an `FnDecl`. Consecutive clauses of the same name and
// arity group into one `let f = ... => match ... { ... }`.

use lento::ast::{desugar_program, Decl, Expr, Stmt};
use lento::parser::parse_program;

/// True if `e` is (inside lambdas) a `match` expression.
fn is_match(e: &Expr) -> bool {
    match e {
        Expr::Match(_) => true,
        Expr::Lambda(l) => is_match(&l.body),
        _ => false,
    }
}

#[test]
fn desugar_leaves_no_fn_decls() {
    let src = std::fs::read_to_string("tests/samples/matching/match.lt").unwrap();
    let ast = parse_program(&src).unwrap();
    let out = desugar_program(&ast);

    for stmt in &out.statements {
        assert!(
            !matches!(stmt, Stmt::Decl(Decl::Fn(_))),
            "desugared program still contains an FnDecl"
        );
    }
}

#[test]
fn same_name_arity_clauses_group_into_single_let() {
    // `factorial` and `zip` each have two same-name clauses; each group must
    // collapse to exactly one `let` whose value ends in a `match`.
    let src = std::fs::read_to_string("tests/samples/matching/match.lt").unwrap();
    let ast = parse_program(&src).unwrap();
    let out = desugar_program(&ast);

    let mut factorial_lets = 0;
    let mut zip_lets = 0;
    for stmt in &out.statements {
        if let Stmt::Decl(Decl::Let(l)) = stmt {
            let name = match &l.pattern.kind {
                lento::ast::PatKind::Var(n) => n.clone(),
                _ => String::new(),
            };
            match name.as_str() {
                "factorial" => {
                    factorial_lets += 1;
                    assert!(is_match(&l.value), "factorial should desugar to a match");
                }
                "zip" => {
                    zip_lets += 1;
                    assert!(is_match(&l.value), "zip should desugar to a match");
                }
                _ => {}
            }
        }
    }
    assert_eq!(factorial_lets, 1, "factorial clauses should group into one let");
    assert_eq!(zip_lets, 1, "zip clauses should group into one let");
}

#[test]
fn lone_clause_desugars_to_plain_lambda() {
    // `fn len xs = xs.len` is a single clause: target desugar should be a
    // plain curried lambda with no `match`.
    let src = "fn len xs = xs.len\n";
    let ast = parse_program(src).unwrap();
    let out = desugar_program(&ast);
    assert_eq!(out.statements.len(), 1);
    match &out.statements[0] {
        Stmt::Decl(Decl::Let(l)) => {
            assert!(matches!(l.value, Expr::Lambda(_)));
            assert!(!is_match(&l.value), "lone clause should not wrap in match");
        }
        other => panic!("expected a let, got {other:?}"),
    }
}

#[test]
fn non_fn_statements_pass_through() {
    let src = "let x = 1 + 2\nfn add a b = a + b\nlet y = x * 3\n";
    let ast = parse_program(src).unwrap();
    let out = desugar_program(&ast);
    let kind_of = |s: &Stmt| match s {
        Stmt::Decl(Decl::Let(_)) => "let",
        Stmt::Decl(Decl::Fn(_)) => "fn",
        Stmt::Decl(Decl::Spec(_)) => "spec",
        Stmt::Decl(Decl::Type(_)) => "type",
        Stmt::Decl(Decl::Class(_)) => "class",
        Stmt::Decl(Decl::Impl(_)) => "impl",
        Stmt::Expr(_) => "expr",
    };
    let kinds: Vec<&str> = out.statements.iter().map(kind_of).collect();
    assert_eq!(kinds, vec!["let", "let", "let"]);
}
