use std::collections::HashMap;

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

fn eval_in_existing_env(src: &str, env: &mut Env) -> Result<Value, String> {
    let ast = parse_program(src).map_err(|e| e.to_string())?;
    let desugared = desugar_program(&ast);
    lento::eval::eval_program_in_env(&desugared, env)
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
fn list_spread_patterns_work_in_match_and_functions() {
    let value = eval(
        "let len = xs => match xs {\n    [] => 0\n    [x, ...xs] => 1 + len xs\n}\nfn zip [] [] = []\nfn zip [x, ...xs] [y, ...ys] = {\n    let pair = [(x, y)]\n    let rest = zip xs ys\n    concat pair rest\n}\n(len [1, 2, 3], zip [1, 2] [3, 4])\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Int(3)));
            assert!(matches!(&items[1], Value::List(v) if matches!(v.as_slice(), [Value::Tuple(a), Value::Tuple(b)]
                if matches!(a.as_slice(), [Value::Int(1), Value::Int(3)])
                && matches!(b.as_slice(), [Value::Int(2), Value::Int(4)]))));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn record_spread_pattern_binds_rest_record() {
    let mut env = lento::eval::initial_env();
    env.insert(
        "rec".to_string(),
        Binding::Inline(Value::Record(HashMap::from([
            ("x".to_string(), Value::Int(1)),
            ("y".to_string(), Value::Int(2)),
            ("z".to_string(), Value::Int(3)),
        ]))),
    );

    let value = eval_in_existing_env(
        "match rec {\n    {x: x, ...rest} => (x, rest)\n}\n",
        &mut env,
    )
    .unwrap();

    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Int(1)));
            assert!(matches!(&items[1], Value::Record(fields)
                if matches!(fields.get("y"), Some(Value::Int(2)))
                && matches!(fields.get("z"), Some(Value::Int(3)))
                && !fields.contains_key("x")));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn fn_block_syntax_evaluates_and_pretty_prints_in_block_form() {
    // Destructuring parameters are parenthesized, and the block body is
    // introduced with `=` so the header/body boundary is unambiguous.
    let src = "fn pick_x ({x: x, ...rest}) = {\n    (x, rest)\n}\n";
    let ast = parse_program(src).unwrap();
    let printed = lento::pprint::format_program(&ast);
    // The printer keeps the `fn` source form; the record parameter is
    // parenthesized so it cannot be confused with the block body.
    assert!(printed.contains("fn pick_x ({x: x, ...rest}) = {"));

    let mut env = lento::eval::initial_env();
    env.insert(
        "rec".to_string(),
        Binding::Inline(Value::Record(HashMap::from([
            ("x".to_string(), Value::Int(7)),
            ("y".to_string(), Value::Int(9)),
        ]))),
    );
    let value = eval_in_existing_env("fn pick_x ({x: x, ...rest}) = {\n    (x, rest)\n}\npick_x rec\n", &mut env).unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Int(7)));
            assert!(matches!(&items[1], Value::Record(fields)
                if matches!(fields.get("y"), Some(Value::Int(9)))
                && !fields.contains_key("x")));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
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

#[test]
fn list_intrinsics_work() {
    let value = eval(
        "let xs = [1, 2]\nlet ys = [3, 4]\nlet empty = []\n(concat xs ys, head ys, tail xs, is_empty empty, is_empty xs)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert_eq!(items.len(), 5);
            assert!(matches!(&items[0], Value::List(v) if matches!(v.as_slice(), [Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4)])));
            assert!(matches!(&items[1], Value::Int(3)));
            assert!(matches!(&items[2], Value::List(v) if matches!(v.as_slice(), [Value::Int(2)])));
            assert!(matches!(&items[3], Value::Bool(true)));
            assert!(matches!(&items[4], Value::Bool(false)));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn concat_is_curried() {
    let value = eval("let join = concat [1, 2]\njoin [3, 4]\n").unwrap();
    assert!(matches!(value, Value::List(v) if matches!(v.as_slice(), [Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4)])));
}

#[test]
fn head_and_tail_error_on_empty_list() {
    let head_err = eval("head []\n").unwrap_err();
    assert!(head_err.contains("head expects a non-empty list"));

    let tail_err = eval("tail []\n").unwrap_err();
    assert!(tail_err.contains("tail expects a non-empty list"));
}

#[test]
fn numeric_intrinsics_work() {
    let value = eval(
        "let neg = 0 - 5\nlet negf = 0.0 - 1.5\nlet a = abs neg\nlet b = abs negf\nlet c = min 3 8\nlet d = max 3.5 2\n(a, b, c, d)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Int(5)));
            assert!(matches!(&items[1], Value::Float(v) if (*v - 1.5).abs() < 1e-9));
            assert!(matches!(&items[2], Value::Int(3)));
            assert!(matches!(&items[3], Value::Float(v) if (*v - 3.5).abs() < 1e-9));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn string_intrinsics_work() {
    let value = eval(
        "let joined = concat \"foo\" \"bar\"\nlet has = contains joined \"oba\"\nlet s = to_string 42\nlet n = parse_int \"42\"\nlet lo = min \"aa\" \"ab\"\nlet hi = max \"aa\" \"ab\"\n(joined, has, s, n, lo, hi)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Str(v) if v == "foobar"));
            assert!(matches!(&items[1], Value::Bool(true)));
            assert!(matches!(&items[2], Value::Str(v) if v == "42"));
            assert!(matches!(&items[3], Value::Int(42)));
            assert!(matches!(&items[4], Value::Str(v) if v == "aa"));
            assert!(matches!(&items[5], Value::Str(v) if v == "ab"));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn parse_int_and_contains_type_errors_are_reported() {
    let parse_err = eval("parse_int \"nope\"\n").unwrap_err();
    assert!(parse_err.contains("parse_int could not parse 'nope'"));

    let contains_err = eval("contains 1 2\n").unwrap_err();
    assert!(contains_err.contains("contains expects (string, string) or (list, value)"));
}

#[test]
fn take_drop_reverse_and_slice_work() {
    let value = eval(
        "let xs = [1, 2, 3, 4]\nlet s = \"abcd\"\n(take 2 xs, drop 2 xs, reverse xs, slice 1 2 xs, take 2 s, drop 2 s, reverse s, slice 1 2 s)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::List(v) if matches!(v.as_slice(), [Value::Int(1), Value::Int(2)])));
            assert!(matches!(&items[1], Value::List(v) if matches!(v.as_slice(), [Value::Int(3), Value::Int(4)])));
            assert!(matches!(&items[2], Value::List(v) if matches!(v.as_slice(), [Value::Int(4), Value::Int(3), Value::Int(2), Value::Int(1)])));
            assert!(matches!(&items[3], Value::List(v) if matches!(v.as_slice(), [Value::Int(2), Value::Int(3)])));
            assert!(matches!(&items[4], Value::Str(v) if v == "ab"));
            assert!(matches!(&items[5], Value::Str(v) if v == "cd"));
            assert!(matches!(&items[6], Value::Str(v) if v == "dcba"));
            assert!(matches!(&items[7], Value::Str(v) if v == "bc"));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn join_and_split_work() {
    let value = eval(
        "let parts = [\"a\", \"b\", \"c\"]\nlet joined = join \"-\" parts\nlet split_back = split \"-\" joined\n(joined, split_back)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::Str(v) if v == "a-b-c"));
            assert!(matches!(&items[1], Value::List(v) if matches!(v.as_slice(), [Value::Str(a), Value::Str(b), Value::Str(c)] if a == "a" && b == "b" && c == "c")));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn slice_like_intrinsics_report_bad_indices() {
    let err = eval("take (0 - 1) [1, 2]\n").unwrap_err();
    assert!(err.contains("take expects a non-negative integer index/count"));
}

#[test]
fn join_requires_strings() {
    let err = eval("join \",\" [1, 2]\n").unwrap_err();
    assert!(err.contains("join expects a list of strings"));
}

#[test]
fn higher_order_list_intrinsics_work() {
    let value = eval(
        "let xs = range 1 6\nlet doubled = map (x => x * 2) xs\nlet evens = filter (x => x % 2 == 0) xs\nlet total = foldl (acc => x => acc + x) 0 xs\nlet has_big = any (x => x > 4) xs\nlet all_small = all (x => x < 6) xs\n(doubled, evens, total, has_big, all_small)\n",
    )
    .unwrap();
    match value {
        Value::Tuple(items) => {
            assert!(matches!(&items[0], Value::List(v) if matches!(v.as_slice(), [Value::Int(2), Value::Int(4), Value::Int(6), Value::Int(8), Value::Int(10)])));
            assert!(matches!(&items[1], Value::List(v) if matches!(v.as_slice(), [Value::Int(2), Value::Int(4)])));
            assert!(matches!(&items[2], Value::Int(15)));
            assert!(matches!(&items[3], Value::Bool(true)));
            assert!(matches!(&items[4], Value::Bool(true)));
        }
        other => panic!("expected tuple, got {other:?}"),
    }
}

#[test]
fn range_descends_when_start_is_greater() {
    let value = eval("range 5 2\n").unwrap();
    assert!(matches!(value, Value::List(v) if matches!(v.as_slice(), [Value::Int(5), Value::Int(4), Value::Int(3)])));
}

#[test]
fn higher_order_intrinsics_report_predicate_errors() {
    let err = eval("any (x => x + 1) [1, 2]\n").unwrap_err();
    assert!(err.contains("any predicate must return bool"));
}
