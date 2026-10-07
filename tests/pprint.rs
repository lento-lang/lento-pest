// Round-trip tests for the pretty printer: parse a sample, format it, and
// parse the result. For well-formed programs the two trees must be equal.

use lento::parser::parse_program;
use lento::pprint::format_program;

fn roundtrip_ok(src: &str) -> bool {
    let ast1 = match parse_program(src) {
        Ok(a) => a,
        Err(_) => return false,
    };
    let printed = format_program(&ast1);
    match parse_program(&printed) {
        // Compare statements only: spans record source positions and differ
        // between the original and the normalized formatting.
        Ok(ast2) => ast1.statements == ast2.statements,
        Err(_) => false,
    }
}

const SAMPLES: &[&str] = &[
    "basics/blocks",
    "specs/borrow",
    "basics/fn_blocks",
    "basics/functions",
    "basics/intrinsics",
    "basics/lambdas",
    "basics/let_and_mutation",
    "matching/match",
    "matching/exhaustiveness",
    "matching/match_literals",
    "matching/match_nested",
    "matching/match_records",
    "matching/match_tuples",
    "specs/mutation_spec",
    "specs/polymorphism",
    "basics/partial_application",
    "types/records",
    "specs/spec_where",
    "matching/tuple_destructuring",
    "types/sum_types_constructors",
    "types/sum_types_bare",
    "types/record_types",
    "types/type_synonyms",
    "specs/spec_checked",
];

#[test]
fn formatted_samples_reparse_to_same_ast() {
    for name in SAMPLES {
        let src = std::fs::read_to_string(format!("tests/samples/{name}.lt")).unwrap();
        assert!(roundtrip_ok(&src), "round-trip failed for sample {name}.lt");
    }
}

#[test]
fn literals_and_operators_roundtrip() {
    // Same-precedence runs left-fold without needing parens; parenthesized
    // single expressions are not representable in Lento (they parse as
    // tuples), so mixed-precedence grouping is intentionally not part of
    // the identity guarantee.
    let src = "let a = 1 + 2 + 3
let b = x && y || z
let c = [1, 2, 3]
let d = (1, 2)
let e = a 3 + 4
let f = if_x != y
";
    assert!(roundtrip_ok(src));
}

#[test]
fn multiline_comma_where_and_all_parse() {
    // Conditions/list vars are comma-separated but a comma may trail at
    // end-of-line with the next item on the following line. These must parse
    // and round-trip (the printer normalizes them to one line).
    let src = "spec divide:
    (x: int) -> (y: int) -> (r: int)
    where
        y != 0,
        r * y <= x

spec map:
    all a,
        b.
    (a -> b) -> [a] -> [b]

fn divide x y = x / y
";
    assert!(roundtrip_ok(src));
}

#[test]
fn formatted_value_is_valid_lento() {
    let src = "spec map:
    all a, b.
    (a -> b) -> [a] -> [b]

let double = (x: int) => x * 2
fn len xs = xs.len
";
    let ast = parse_program(src).unwrap();
    let printed = format_program(&ast);
    // The formatted text must itself parse.
    assert!(parse_program(&printed).is_ok());
    // And should contain the reconstructed forms.
    assert!(printed.contains("double"));
    assert!(printed.contains("=>"));
    assert!(printed.contains("all a, b"));
}

#[test]
fn pretty_printed_type_applications_are_curried() {
    let ast = parse_program(
        "type Result a e = Ok a | Err e\n         spec check : all a, e. Result a e -> bool\n",
    )
    .expect("curried type application should parse");
    let printed = format_program(&ast);
    assert!(printed.contains("Result a e"), "{printed}");
    assert!(
        !printed.contains("<a") && !printed.contains("<a,"),
        "{printed}"
    );
}

#[test]
fn nested_type_arguments_round_trip_with_parentheses() {
    let source = "type Result a e = Ok a | Err e\n         type Pair a b = Mk a b\n         spec check : all a, e. Pair (Result a e) bool -> bool\n";
    let printed = format_program(&parse_program(source).expect("should parse"));
    assert!(printed.contains("Pair (Result a e) bool"), "{printed}");
    // The printed form must parse to the same shape, not flatten to four
    // arguments on `Pair`.
    let reparsed = parse_program(&printed).expect("printed form should reparse");
    let printed_again = format_program(&reparsed);
    assert_eq!(
        printed, printed_again,
        "type application printing must be stable"
    );
}

#[test]
fn multi_argument_ctor_payloads_round_trip() {
    let source = "type Foo = Ok a b | None\n         ";
    let printed = format_program(&parse_program(source).expect("should parse"));
    assert!(printed.contains("Ok a b"), "{printed}");
    let reparsed = parse_program(&printed).expect("multi-arg payload should reparse");
    let printed_again = format_program(&reparsed);
    assert!(printed_again.contains("Ok a b"), "{printed_again}");
}

#[test]
fn named_binder_arguments_round_trip_parenthesized() {
    let source = "type Pair a b = Mk a b\n         spec check : (value : Pair int bool) -> bool\n";
    let printed = format_program(&parse_program(source).expect("should parse"));
    let reparsed = parse_program(&printed).expect("printed named binder should reparse");
    assert_eq!(
        printed,
        format_program(&reparsed),
        "named binder printing must be stable"
    );
}
