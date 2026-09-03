# Lento (pest)

An experimental parser, formatter, type-analysis pipeline, and tree-walking interpreter for the Lento programming language, implemented in Rust with [pest](https://pest.rs/).

> [!IMPORTANT]
> This repository is an early language prototype. The syntax and semantics are evolving, and it is not yet intended for production use.

## Overview

Lento is an expression-oriented language exploring concise functional syntax, pattern-directed function definitions, type inference, explicit specifications, and specialization.

```lento
spec factorial:
    int -> int

fn factorial 0 = 1
fn factorial n = n * factorial (n - 1)

let values = range 1 6
let results = map factorial values

assert (results == [1, 2, 6, 24, 120])
println results
```

The current prototype includes:

- A pest grammar and AST lowering
- A source formatter with parse/format round-trip tests
- A tree-walking interpreter and REPL
- Curried functions, lambdas, recursion, and pattern matching
- Hindley–Milner-style inference infrastructure
- Function specs, overload partitioning, and specialization analysis
- Exhaustiveness, duplicate-clause, and unreachable-clause diagnostics
- Mutable bindings and an experimental `ref` model

See [spec.md](spec.md) for the implemented language reference.

## Getting started

### Requirements

- A recent stable Rust toolchain
- Cargo

Clone the repository and run the test suite:

```bash
git clone https://github.com/lento-lang/lento-pest.git
cd lento-pest
cargo test
```

Run a Lento source file:

```bash
cargo run -- path/to/program.lt
```

Start the parser REPL:

```bash
cargo run
```

## Command-line interface

```text
cargo run -- <file>               Parse and evaluate a file
cargo run -- --print-ast <file>   Print the lowered AST
cargo run -- --print-code <file>  Parse and pretty-print source
cargo run -- --fmt <file>         Format a file in place
cargo run -- --interactive        Start the REPL explicitly
```

The REPL currently prints parsed ASTs. File mode evaluates the program and prints the final non-unit expression.

## Language at a glance

```lento
type user_id = int

let users = [
    {name: "Ada", active: true},
    {name: "Grace", active: false},
]

fn status ({name: name, active: true}) = name + " is active"
fn status ({name: name, active: false}) = name + " is inactive"

let labels = map status users

match labels {
    [] => "no users"
    [first, ...rest] => first
}
```

Function application is curried and may be written with spaces or parentheses:

```lento
map (x => x * 2) [1, 2, 3]
map(x => x * 2, [1, 2, 3])
```

## Repository layout

| Path | Purpose |
| --- | --- |
| `src/grammar.pest` | Concrete grammar |
| `src/parser.rs` | Parse-tree to AST lowering |
| `src/ast.rs` | AST and function-clause desugaring |
| `src/infer.rs`, `src/types.rs` | Type inference and type representation |
| `src/semantics.rs`, `src/specialize.rs`, `src/specs.rs` | Function grouping, specialization, and spec association |
| `src/patterns.rs` | Pattern usefulness and exhaustiveness analysis |
| `src/eval.rs`, `src/intrinsics.rs` | Interpreter and built-in functions |
| `src/pprint.rs` | Source formatter |
| `tests/` | Parser, evaluator, inference, and semantic tests |

## Development

Before submitting a change, run:

```bash
cargo fmt --check
cargo test
cargo clippy --all-targets
```

When changing the language, update the grammar, implementation, tests, and [spec.md](spec.md) together. Small, focused changes with executable examples are easiest to review.

## Project status

The parser and interpreter support a useful experimental core, while the static semantics and memory model remain active design work. The reference describes the behavior implemented by this repository; future Lento design ideas may differ.
