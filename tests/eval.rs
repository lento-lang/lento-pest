use lento::ast::desugar_program;
use lento::eval::{Binding, Env, Value};
use lento::parser::parse_program;

fn eval(src: &str) -> Result<Value, String> {
    let ast = parse_program(src).map_err(|e| e.to_string())?;
    let desugared = desugar_program(&ast);
    lento::eval::eval_program(&desugared)
}

fn eval_with_env(src: &str) -> Result<(Value, Env), String> {
    let ast = parse_program(src).map_err(|e| e.to_string())?;
    let desugared = desugar_program(&ast);
    let mut env = lento::eval::initial_env();
    let value = lento::eval::eval_program_in_env(&desugared, &mut env)?;
    Ok((value, env))
}

fn assert_int(value: Value, expected: i64) {
    match value {
        Value::Int(actual) => assert_eq!(actual, expected),
        other => panic!("expected int {expected}, got {other:?}"),
    }
}

#[test]
fn let_mut_assignment_updates_binding() {
    let value = eval("let mut counter = 0\ncounter = counter + 1\ncounter\n").unwrap();
    assert_int(value, 1);
}

#[test]
fn block_scope_clones_env_but_shares_cells() {
    let value = eval("let mut x = 1\n{x = x + 1\n}\nx\n").unwrap();
    assert_int(value, 2);
}

#[test]
fn multi_statement_block_returns_final_expression() {
    let value = eval("let result = {\n    let base = 1\n    let bump = 2\n    base + bump\n}\nresult\n").unwrap();
    assert_int(value, 3);
}

#[test]
fn closures_capture_shared_cells() {
    let value = eval("let mut x = 1\nlet bump = _ => x = x + 1\nbump 0\nx\n").unwrap();
    assert_int(value, 2);
}

#[test]
fn closures_observe_later_mutation() {
    let value = eval("let mut x = 1\nlet read = _ => x\nx = 7\nread 0\n").unwrap();
    assert_int(value, 7);
}

#[test]
fn immutable_let_is_stored_inline() {
    let (_, env) = eval_with_env("let x = 1\n").unwrap();
    assert!(matches!(env.get("x"), Some(Binding::Inline(Value::Int(1)))));
}

#[test]
fn mutable_let_is_stored_in_shared_cell() {
    let (_, env) = eval_with_env("let mut x = 1\n").unwrap();
    assert!(matches!(env.get("x"), Some(Binding::Cell { mutable: true, .. })));
}

#[test]
fn recursive_function_binding_uses_immutable_cell() {
    let (_, env) = eval_with_env("fn id x = x\n").unwrap();
    assert!(matches!(env.get("id"), Some(Binding::Cell { mutable: false, .. })));
}

#[test]
fn grouped_function_clauses_evaluate_via_match() {
    let value = eval("fn factorial 0 = 1\nfn factorial n = n * factorial (n - 1)\nfactorial 5\n").unwrap();
    assert_int(value, 120);
}

#[test]
fn member_len_and_index_work_on_lists() {
    let value = eval("let xs = [10, 20, 30]\n(xs.len, xs[1])\n").unwrap();
    match value {
        Value::Tuple(items) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(&items[0], Value::Int(3)));
            assert!(matches!(&items[1], Value::Int(20)));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn inner_bindings_do_not_escape_block_scope() {
    let err = eval("{let y = 1\n}\ny\n").unwrap_err();
    assert!(err.contains("undefined variable 'y'"));
}

#[test]
fn assignment_to_immutable_binding_fails() {
    let err = eval("let x = 1\nx = 2\n").unwrap_err();
    assert!(err.contains("cannot assign to immutable binding 'x'"));
}

#[test]
fn ref_on_inline_immutable_binding_fails() {
    let err = eval("let x = 1\nref x\n").unwrap_err();
    assert!(err.contains("cannot take ref of immutable binding 'x'"));
}

#[test]
fn len_intrinsic_works_on_list_tuple_and_string() {
    let value = eval("let xs = [1, 2, 3]\nlet pair = (1, 2)\nlet s = \"abc\"\n(len xs, len pair, len s)\n").unwrap();
    match value {
        Value::Tuple(items) => {
            assert_eq!(items.len(), 3);
            assert!(matches!(&items[0], Value::Int(3)));
            assert!(matches!(&items[1], Value::Int(2)));
            assert!(matches!(&items[2], Value::Int(3)));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn divide_and_mod_by_zero_return_errors_not_panics() {
    let div_err = eval("1 / 0\n").unwrap_err();
    assert!(div_err.contains("integer error in /"));

    let mod_err = eval("1 % 0\n").unwrap_err();
    assert!(mod_err.contains("integer error in %"));
}

#[test]
fn assert_intrinsic_handles_true_and_false() {
    assert!(matches!(eval("assert true\n").unwrap(), Value::Unit));
    let err = eval("assert false\n").unwrap_err();
    assert!(err.contains("assert failed"));
}

#[test]
fn print_intrinsics_return_unit() {
    assert!(matches!(eval("print \"x\"\n").unwrap(), Value::Unit));
    assert!(matches!(eval("println \"x\"\n").unwrap(), Value::Unit));
}
