# Lento (pest)

A pest-based parser and tree-walking interpreter for the Lento language.

## Build & Run

```bash
cargo run -- path/to/file.lt
cargo run -- --fmt path/to/file.lt   # format in place
cargo run                              # REPL
```

## Example

```lento
spec map:
    all a, b.
    (a -> b) -> [a] -> [b]

fn map f [] = []
fn map f [x, ...xs] = concat [f x] (map f xs)

let xs = [1, 2, 3]
let doubled = map (x => x * 2) xs
assert (doubled == [2, 4, 6])
println doubled
```

## Features

- **Let bindings** with optional `mut` for mutation
- **Functions** via curried `fn` clauses with pattern matching
- **Lambdas** with `=>` syntax and optional type annotations
- **Pattern matching** on literals, tuples, lists (`[x, ...rest]`), and records (`{x: a, ...rest}`)
- **Records** with field access and spread (`{...base, x: 1}`)
- **Higher-order intrinsics**: `map`, `filter`, `foldl`, `any`, `all`, `range`
- **Specs** for signatures with quantified type variables and `where` refinements
- **Blocks** as expressions with block scoping

## Tests

```bash
cargo test
```
