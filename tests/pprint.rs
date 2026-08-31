// Round-trip tests for the pretty printer: parse a sample, format it, and
// parse the result. For well-formed programs the two trees must be equal.
//
// `spec_where.lt` is excluded: its trailing `fn` clause is absorbed into the
// `where` conditions by a pre-existing grammar ambiguity (no statement
// boundary after a where block), so it is not a printer-round-trippable
// program.

use lento::parser::parse_program;
use lento::pprint::format_program;

fn roundtrip_ok(src: &str) -> bool {
    let ast1 = match parse_program(src) {
        Ok(a) => a,
        Err(_) => return false,
    };
    let printed = format_program(&ast1);
    match parse_program(&printed) {
        Ok(ast2) => ast1 == ast2,
        Err(_) => false,
    }
}

const SAMPLES: &[&str] = &[
    "borrow",
    "functions",
    "lambdas",
    "let_and_mutation",
    "match",
    "match_literals",
    "match_nested",
    "match_records",
    "match_tuples",
    "mutation_spec",
    "polymorphism",
    "tuple_destructuring",
];

#[test]
fn formatted_samples_reparse_to_same_ast() {
    for name in SAMPLES {
        let src = std::fs::read_to_string(format!("tests/samples/{name}.lt")).unwrap();
        assert!(
            roundtrip_ok(&src),
            "round-trip failed for sample {name}.lt"
        );
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
fn formatted_value_is_valid_lento() {
    let src = "spec map:
    all a b.
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
    assert!(printed.contains("all a b"));
}
