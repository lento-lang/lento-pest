// Type-checker integration tests: positive inference, new type syntax
// (sums, records, synonyms), spec conformance, and negative cases.

use lento::ast::desugar_program;
use lento::eval;
use lento::parser::parse_program;

fn checked(src: &str) -> lento::ast::Program {
    let ast = parse_program(src).expect("parse");
    let desugared = desugar_program(&ast);
    if let Err(e) = lento::typecheck::check_program(&desugared) {
        panic!("expected {src:?} to type-check, got: {e}");
    }
    desugared
}

fn check(src: &str) -> Result<(), String> {
    let ast = parse_program(src).map_err(|e| e.to_string())?;
    let desugared = desugar_program(&ast);
    lento::typecheck::check_program(&desugared)
}

fn check_ok(src: &str) {
    if let Err(e) = check(src) {
        panic!("expected {src:?} to type-check, got: {e}");
    }
}

fn check_err(src: &str, expected: &str) {
    match check(src) {
        Ok(()) => panic!("expected {src:?} to fail checking with '{expected}'"),
        Err(e) => assert!(
            e.contains(expected),
            "expected error containing {expected:?}, got: {e}"
        ),
    }
}

fn eval_checked(src: &str) -> Result<eval::Value, String> {
    let program = checked(src);
    eval::eval_program(&program)
}

// -- inference --------------------------------------------------------------

#[test]
fn infers_polymorphic_identity() {
    check_ok("fn id x = x\nassert (id 1 == 1)\nassert (id \"a\" == \"a\")\n");
}

#[test]
fn infers_constraint_polymorphic_arithmetic() {
    check_ok("let double = x => x + x\nassert (double 21 == 42)\nassert (double 1.5 == 3.0)\n");
}

#[test]
fn infers_list_element_types() {
    check_ok("let xs = [1, 2, 3]\nassert (head xs == 1)\n");
    check_err("let xs = [1, \"a\"]\n", "cannot unify");
}

#[test]
fn rejects_type_mismatched_operands() {
    check_err("1 + \"a\"\n", "cannot unify int with str");
    check_err("1 < true\n", "cannot unify int with bool");
}

#[test]
fn rejects_unknown_variables_and_fields() {
    check_err("nope\n", "undefined variable 'nope'");
    check_err("let r = { x: 1 }\nr.y\n", "has no field 'y'");
    check_err("nope 1\n", "undefined variable 'nope'");
}

#[test]
fn row_polymorphic_field_access() {
    check_ok("fn getx r = r.x\nassert (getx { x: 1, y: 2 } == 1)\nassert (getx { x: 9 } == 9)\n");
    check_err("fn getx r = r.x\ngetx 5\n", "cannot unify");
}

#[test]
fn assignment_requires_mutable_binding() {
    check_ok("let mut x = 1\nx = 2\nassert (x == 2)\n");
    check_err("let x = 1\nx = 2\n", "cannot assign to immutable binding");
}

#[test]
fn rejects_unsolved_constraints_on_concrete_types() {
    check_err("abs [1, 2]\n", "no Num instance");
    check_err("concat 1 2\n", "no Concat instance");
    check_err("take 1 5\n", "no Seq instance");
}
#[test]
fn literal_arithmetic_types_are_checked() {
    check_ok("assert (1 + 2 == 3)\nassert (1.5 + 2.5 == 4.0)\nassert (\"a\" + \"b\" == \"ab\")\n");
    check_err("1 % 2.0\n", "cannot unify int with float");
}

#[test]
fn typed_patterns_check_against_scruitinee() {
    check_ok("let x = 5\nmatch x { (n : int) => n }\n");
    check_err(
        "let x = 5\nmatch x { (s : str) => s }\n",
        "cannot unify str with int",
    );
}

// -- sum type syntaxes -------------------------------------------------------

#[test]
fn unbracketed_constructor_sums() {
    check_ok(
        "type Option a = Some a | None\n\
         let o : Option int = Some 5\n\
         fn get opt = match opt { Some v => v, None => 0 }\n\
         assert (get o == 5)\nassert (get None == 0)\n",
    );
}

#[test]
fn unbracketed_bare_sums() {
    check_ok(
        "type Id = int | str\n\
         let n : Id = 42\n\
         fn show id = match id { (x : int) => 1, (s : str) => 2 }\n\
         assert (show n == 1)\n",
    );
}

#[test]
fn bracketed_sums_match_unbracketed_semantics() {
    // The bracketed form is the same sum-type syntax in any type position,
    // including inside block scope where constructor names are local.
    check_ok(
        "type A = Some int | None\n\
         let x : A = Some 1\n\
         fn getA v = match v { Some i => i, None => 0 }\n\
         assert (getA x == 1)\n\
         let check = {\n\
             type B = [Some int | None]\n\
             let getB = v => match v { Some i => i, None => 0 }\n\
             let y : B = Some 1\n\
             getB y\n\
         }\n\
         assert (check == 1)\n",
    );
    // Lists and sums remain distinct: `[T]` is a list type.
    check_ok(
        "type IntList = [int]\n\
         let xs : IntList = [1, 2]\n\
         assert (head xs == 1)\n",
    );
}

#[test]
fn mixed_constructor_and_bare_alternatives() {
    check_ok(
        "type Answer = Yes | No | int\n\
         let a : Answer = Yes\n\
         let n : Answer = 7\n\
         fn show v = match v { Yes => \"y\", No => \"n\", (i : int) => to_string i }\n\
         assert (show a == \"y\")\nassert (show n == \"7\")\n",
    );
}

#[test]
fn applied_types_work_as_constructor_payloads() {
    // In unbracketed sums an uppercase identifier is always a constructor;
    // applied types belong in payloads (parens) or the bracketed form.
    check_ok(
        "type Maybe a = Some a | None\n\
         type Holder = Hold (Maybe int) | Empty\n\
         let h : Holder = Hold (Some 5)\n\
         fn unwrap v = match v { Hold m => m, Empty => None }\n\
         fn get o = match o { Some x => x, None => 0 }\n\
         assert (get (unwrap h) == 5)\n",
    );
}

// -- sum types ---------------------------------------------------------------

#[test]
fn constructor_sums_roundtrip() {
    let value = eval_checked(
        "type Option a = Some a | None\n\
         fn get opt = match opt { Some v => v, None => 0 }\n\
         concat to_string (get (Some 5)) \"\"\n",
    )
    .unwrap();
    assert!(matches!(value, eval::Value::Str(ref s) if s == "5"));
}

#[test]
fn constructor_arity_is_checked() {
    check_err(
        "type Option a = Some a | None\nSome 1 2\n",
        "cannot call a sum value",
    );
    check_err(
        "type Option a = Some a | None\nNone 1\n",
        "cannot call a sum value",
    );
    check_err(
        "type Option a = Some a | None\nmatch None { Some x => x }\n",
        "never matches a scrutinee of tag 'None'",
    );
    check_err(
        "type Option a = Some a | None\nmatch Some 1 { Some => 0 }\n",
        "expects a payload pattern",
    );
    check_err(
        "type Option a = Some a | None\nlet x = Some \"a\"\nlet y : Option int = x\n",
        "cannot unify int with str",
    );
}

#[test]
fn constructor_payloads_are_checked() {
    check_err(
        "type Option a = Some a | None\nlet o : Option int = Some \"a\"\n",
        "cannot unify int with str",
    );
    check_ok("type Option a = Some a | None\nlet o : Option int = Some 5\n");
}

#[test]
fn bare_sum_members_inject_and_match() {
    let value = eval_checked(
        "type Id = int | str\n\
         let n : Id = 42\n\
         match n { (x : int) => x, (s : str) => 0 }\n",
    )
    .unwrap();
    assert!(matches!(value, eval::Value::Int(42)));
}

#[test]
fn bare_sum_rejects_non_members() {
    check_err("type Id = int | str\nlet x : Id = true\n", "not an alternative");
}

#[test]
fn typed_arms_infer_sum_scruitinee_at_call_site() {
    check_ok(
        "type Id = int | str\n\
         let n : Id = 42\n\
         fn show id = match id { (x : int) => 1, (s : str) => 2 }\n\
         assert (show n == 1)\n",
    );
}

#[test]
fn sums_are_generative() {
    check_err(
        "type A = int | str\ntype B = int | str\nlet x : A = 5\nlet y : B = x\n",
        "cannot unify",
    );
}

#[test]
fn constructor_names_must_exist() {
    check_err("match 1 { Nope => 0 }\n", "unknown constructor");
    check_err("Nope\n", "undefined variable 'Nope'");
}

// -- record types ------------------------------------------------------------

#[test]
fn record_type_annotations_are_checked() {
    check_ok("type Point = { x: int, y: int }\nlet p : Point = { x: 1, y: 2 }\n");
    check_err(
        "type Point = { x: int, y: int }\nlet p : Point = { x: 1 }\n",
        "lacks fields",
    );
    check_err(
        "type Point = { x: int, y: int }\nlet p : Point = { x: 1, y: \"a\" }\n",
        "cannot unify int with str",
    );
}

#[test]
fn record_types_flow_through_functions() {
    check_ok(
        "type Point = { x: int, y: int }\n\
         fn sum p = p.x + p.y\n\
         assert (sum { x: 1, y: 2 } == 3)\n",
    );
    check_err(
        "type Point = { x: int, y: int }\n\
         fn sum (p : Point) = p.x + p.y\n\
         sum { x: 1 }\n",
        "lacks fields",
    );
}

// -- synonyms ----------------------------------------------------------------

#[test]
fn synonyms_expand() {
    check_ok(
        "type Meters = int\n\
         let h : Meters = 180\n\
         assert (h + 1 == 181)\n",
    );
    check_err(
        "type Meters = int\nlet h : Meters = \"tall\"\n",
        "cannot unify int with str",
    );
}

#[test]
fn parameterized_types_check_arity() {
    check_err(
        "type Option a = Some a | None\nlet o : Option = Some 1\n",
        "expects 1 argument(s)",
    );
    check_err("let o : Missing = 1\n", "unknown type 'Missing'");
}

// -- specs -------------------------------------------------------------------

#[test]
fn spec_conformance_passes() {
    check_ok(
        "spec identity:\n    all a.\n    a -> a\n\nfn identity x = x\n",
    );
    check_ok(
        "spec double:\n    all a :: Add.\n    a -> a\n\nfn double x = x + x\n",
    );
}

#[test]
fn spec_conformance_rejects_narrower_definitions() {
    check_err(
        "spec identity:\n    all a.\n    a -> a\n\nfn identity x = x + 1\n",
        "does not match its spec",
    );
    check_err(
        "spec f:\n    all a.\n    a -> a\n\nfn f (x : int) = x\n",
        "does not match its spec",
    );
}

#[test]
fn spec_constraint_coverage_is_required() {
    check_err(
        "spec f:\n    all a :: Num.\n    a -> a\n\nfn f x = x\n",
        "does not satisfy constraint",
    );
}

#[test]
fn duplicate_declarations_are_rejected() {
    check_err("type A = int\ntype A = str\n", "duplicate type declaration");
    check_err(
        "type O = [Some int | None]\ntype P = [Some int | No]\n",
        "duplicate constructor",
    );
}

#[test]
fn statement_spans_appear_in_errors() {
    let err = check("let x = 1\n1 + \"a\"\n").unwrap_err();
    assert!(err.contains("line 2"), "error should carry line info: {err}");
}

// -- regression: existing behavior under the checker -------------------------

#[test]
fn intrinsic_signatures_are_polymorphic() {
    check_ok(
        "assert (head [1, 2] == 1)\nassert (head [\"a\", \"b\"] == \"a\")\n\
         assert (map (x => x + 1) [1, 2] == [2, 3])\n\
         assert (min 3 8 == 3)\nassert (min \"a\" \"b\" == \"a\")\n",
    );
}

#[test]
fn empty_list_and_match_types_unify() {
    check_ok(
        "fn len xs = match xs {\n    [] => 0\n    [x, ...rest] => 1 + len rest\n}\n\
         assert (len [1, 2, 3] == 3)\n",
    );
}
