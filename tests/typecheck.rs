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
fn assignment_checks_value_against_binding_type() {
    check_ok("let mut x = 1\nx = 2\nx = x + 1\nassert (x == 3)\n");
    check_err("let mut x = 1\nx = \"hello\"\n", "cannot unify");
    check_err("let mut f = x => x + 1\nf = \"oops\"\n", "cannot unify");
}

#[test]
fn annotation_forces_pending_constraint_solving() {
    // The annotation binds the Num constraint's variable to str after
    // solve_pending runs; the constraint must still be verified.
    check_err(
        "let f : str -> str = x => x * x\n",
        "no Num instance",
    );
    // Re-annotating a generalized value: the pending Num constraint must
    // not survive unverified either.
    let g = "let g = x => x * x\nlet h : str -> str = g\n";
    check_err(g, "no Num instance");
    // Concrete-but-valid constraints stay fine.
    check_ok("let f : int -> int = x => x * x\nassert (f 3 == 9)\n");
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
        "constructor 'Some' expects 1 argument",
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
fn parameterized_synonyms_apply_their_arguments() {
    // Two uses of the same parameterized synonym must share constraints:
    // Wrapper<int> is not interchangeable with Wrapper<str>.
    check_ok(
        "type Wrapper a = { value: a }\n\
         let w : Wrapper<int> = { value: 1 }\n\
         assert (w.value == 1)\n",
    );
    check_err(
        "type Wrapper a = { value: a }\nlet w : Wrapper<int> = { value: \"oops\" }\n",
        "cannot unify",
    );
    check_err(
        "type Wrapper a = { value: a }\n\
         let w : Wrapper<int> = { value: 1 }\n\
         let v : Wrapper<str> = w\n",
        "cannot unify",
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
fn member_len_matches_len_class() {
    // Tuples and lists are concrete Len instances; `.len` must type-check
    // the same way the len intrinsic (and the runtime) treats them.
    check_ok("let t = (1, 2, 3)\nassert (t.len == 3)\n");
    check_ok("assert ([1, 2].len == 2)\n");
    check_ok("assert ((\"a\", \"b\").len == 2)\n");
    // Non-len fields on tuples still fail, and a closed record's `.len`
    // stays a plain field lookup.
    check_err("(1, 2).nope\n", "cannot access field");
    check_err("let r = { x: 1 }\nr.len\n", "has no field 'len'");
}

#[test]
fn spec_after_definition_is_checked() {
    // A spec declared after its definition used to be recorded but never
    // verified, because check_specs_for only fires when the definition's
    // let is processed.
    check_ok(
        "fn identity x = x\nspec identity:\n    all a.\n    a -> a\n",
    );
    check_err(
        "fn broken x = x + 1\nspec broken:\n    all a.\n    a -> a\n",
        "does not match its spec",
    );
}

#[test]
fn spec_without_definition_is_rejected() {
    // A spec naming a binding that never exists used to pass silently.
    check_err(
        "spec ghost:\n    all a.\n    a -> a\n",
        "has no matching definition",
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
        "fn len xs = match xs {\n    [] => 0,\n    [x, ...rest] => 1 + len rest\n}\n\
         assert (len [1, 2, 3] == 3)\n",
    );
}

// -- where-clause refinements ------------------------------------------------

const DIVIDE_SPEC: &str = "spec divide:\n    (x: int) -> (y: int) -> (r: int)\n    where\n        y != 0\n\nfn divide x y = x / y\n";

#[test]
fn where_preconditions_checked_at_callsites() {
    check_ok(&format!("{DIVIDE_SPEC}assert (divide 20 4 == 5)\n"));
    check_err(
        &format!("{DIVIDE_SPEC}assert (divide 20 0 == 0)\n"),
        "violates precondition",
    );
}

#[test]
fn where_preconditions_track_symbolic_callers() {
    // Provable caller context: the precondition holds for all x.
    check_ok(&format!(
        "{DIVIDE_SPEC}fn helper x = divide 2 1\nassert (helper 9 == 2)\n"
    ));
    // Unprovable symbolic y: counterexample reported at the call site.
    check_err(
        &format!("{DIVIDE_SPEC}fn helper y = divide 2 y\n"),
        "violates precondition",
    );
}

#[test]
fn where_partial_application_rejected() {
    check_err(
        &format!("{DIVIDE_SPEC}let g = divide 20\n"),
        "partial application",
    );
    check_err(
        &format!("{DIVIDE_SPEC}let g = divide\n"),
        "cannot be used as a value",
    );
}

#[test]
fn where_postcondition_verified() {
    check_ok(
        "spec square:\n    (x: int) -> (r: int)\n    where\n        r == x * x\n\nfn square x = x * x\nassert (square 7 == 49)\n",
    );
    check_err(
        "spec bad:\n    (x: int) -> (r: int)\n    where\n        r == x * x\n\nfn bad x = x + x\n",
        "violates postcondition",
    );
}

#[test]
fn where_unknown_identifier_rejected() {
    check_err(
        "spec f:\n    (x: int) -> int\n    where\n        z != 0\n\nfn f x = x\n",
        "unknown identifier 'z'",
    );
}

#[test]
fn where_unsupported_parameter_type_rejected() {
    check_err(
        "spec f:\n    (x: str) -> str\n    where\n        x != \"\"\n\nfn f x = x\n",
        "not int/float/bool",
    );
}

// -- match exhaustiveness ----------------------------------------------------

const OPTION_DECL: &str = "type Option a = Some a | None\n";

#[test]
fn exhaustive_constructor_sums_pass() {
    check_ok(&format!(
        "{OPTION_DECL}fn get o = match o {{ Some x => x, None => 0 }}\nassert (get (Some 3) == 3)\n"
    ));    check_ok(&format!(
        "{OPTION_DECL}fn f o = match o {{ None => 0, other => 1 }}\n"
    ));
    // An irrefutable typed pattern on the sum covers everything.
    check_ok(&format!(
        "{OPTION_DECL}fn f o = match o {{ (v: Option<int>) => 1 }}\n"
    ));
}

#[test]
fn exhaustive_hybrid_sums_pass() {
    check_ok(
        "type Id = int | str\nfn f x = match x { (n: int) => n, (s: str) => 0 }\n",
    );
    // The sum's own type as a typed pattern is irrefutable.
    check_ok("type Id = int | str\nfn f x = match x { (v: Id) => 1 }\n");
}

#[test]
fn exhaustive_bool_and_list_and_record_pass() {
    check_ok("fn f b = match b { true => 1, false => 0 }\n");
    check_ok("fn f xs = match xs { [] => 0, [x, ...rest] => x }\n");
    check_ok(
        "type Point = { x: int, y: int }\nfn f p = match p { { x: a, y: b } => a + b }\n",
    );
    // A record pattern only names the fields it needs (at-least semantics).
    check_ok("type Point = { x: int, y: int }\nfn f p = match p { { x: a } => a }\n");
}

#[test]
fn exhaustive_tuple_products_pass() {
    // Annotated scrutinee over a record of sums: the columns are known
    // sums, so the product must be covered cell by cell.
    check_ok(&format!(
        "{OPTION_DECL}type Pair = {{ a: Option int, b: Option int }}\n\
         fn f (p: Pair) = match p {{\n\
         \x20   {{ a: Some x, b: Some y }} => x + y,\n\
         \x20   {{ a: Some x, b: None }} => x,\n\
         \x20   {{ a: None, b: Some y }} => y,\n\
         \x20   {{ a: None, b: None }} => 0\n\
         }}\nassert (f {{ a: Some 1, b: None }} == 1)\n"
    ));
}

#[test]
fn nonexhaustive_matches_are_rejected() {
    // Missing nullary constructor.
    check_err(&format!("{OPTION_DECL}fn f o = match o {{ Some x => x }}\n"), "not exhaustive");
    // Missing constructor with payload: None alone does not cover Some.
    check_err(&format!("{OPTION_DECL}fn f o = match o {{ None => 0 }}\n"), "not exhaustive");
    // Missing bare alternative. The scrutinee must be pinned to the sum
    // (annotation); on an unannotated param the deferred Member constraint
    // would legitimately pin it to int.
    check_err(
        "type Id = int | str\nlet x : Id = 42\nmatch x { (n: int) => n }\n",
        "not exhaustive",
    );
    // Half of a bool.
    check_err("fn f b = match b { true => 1 }\n", "not exhaustive");
    // Missing empty list.
    check_err("fn f xs = match xs { [x, ...rest] => x }\n", "not exhaustive");
    // Missing non-empty lists.
    check_err("fn f xs = match xs { [] => 0 }\n", "not exhaustive");
    // Infinite type needs a catch-all.
    check_err("fn f n = match n { 0 => 0, 1 => 1 }\n", "not exhaustive");
    check_err("fn f s = match s { \"a\" => 0 }\n", "not exhaustive");
}

#[test]
fn guarded_arms_do_not_cover() {
    check_err(
        &format!("{OPTION_DECL}fn f o = match o {{ Some x if x > 0 => x, None => 0 }}\n"),
        "not exhaustive",
    );
}

#[test]
fn nested_payload_coverage_is_checked() {
    // Payload is an int: a literal does not cover it.
    check_err(
        &format!("{OPTION_DECL}fn f o = match o {{ Some 1 => 1, None => 0 }}\n"),
        "not exhaustive",
    );
    // Missing one cell of the product (record columns are known sums).
    check_err(
        &format!(
            "{OPTION_DECL}type Pair = {{ a: Option int, b: Option int }}\n\
             fn f (p: Pair) = match p {{\n\
             \x20   {{ a: Some x, b: Some y }} => x + y,\n\
             \x20   {{ a: Some x, b: None }} => x,\n\
             \x20   {{ a: None, b: Some y }} => y\n\
             }}\n"
        ),
        "not exhaustive",
    );
}

#[test]
fn known_tag_scrutinee_skips_exhaustiveness() {
    // A literal constructor application pins the tag; other arms cannot
    // occur and the matching arm is checked by tag instead.
    check_ok(&format!("{OPTION_DECL}assert (match Some 5 {{ Some x => x, None => 0 }} == 5)\n"));
}

#[test]
fn spread_only_list_arm_is_exhaustive() {
    check_ok("fn f (xs: [int]) = match xs { [...r] => 1 }\nassert (f [1, 2] == 1)\n");
}

#[test]
fn known_tag_scrutinee_requires_unguarded_matching_arm() {
    check_err(
        "type O = Some int | None\nlet x = match Some 5 { Some y if y > 10 => 1 }\n",
        "not exhaustive",
    );
    check_ok(
        "type O = Some int | None\nlet x = match Some 5 { Some y if y > 10 => 1, Some y => y }\n",
    );
}

#[test]
fn exhaustiveness_error_names_the_missing_case() {
    check_err(
        &format!("{OPTION_DECL}fn f o = match o {{ Some x => x }}\n"),
        "missing constructor 'None'",
    );
    check_err("fn f xs = match xs { [x, ...rest] => x }\n", "missing an empty list");
}
