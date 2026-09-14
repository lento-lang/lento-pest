# Lento (pest)

A pest-based parser, Hindley–Milner type checker, and tree-walking interpreter
for the Lento language.

## Build & Run

```bash
cargo run -- path/to/file.lt         # parse, type-check, evaluate
cargo run -- --fmt path/to/file.lt   # format in place
cargo run -- --print-ast path/to/file.lt
cargo run                            # REPL
```

Every run of a file type-checks first: ill-typed programs fail with a `type
error:` message (line/column of the enclosing statement) before any evaluation.

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

- **Hindley–Milner type inference** with let-polymorphism (value restriction),
  unification, and builtin constraint classes (`Num`, `Ord`, `Eq`, `Add`,
  `Concat`, `Seq`, `Len`, `Haystack`) for the overloaded intrinsics and
  operators
- **User-defined types**:
  - constructor sums: `type Option a = Some a | None` — constructors are
    uppercase (`Some 5`, `None`) and matched by constructor patterns
  - bare sums: `type Id = int | str` — members inject implicitly against an
    annotated target and are matched with typed patterns (`(n : int) => ...`)
  - record types: `type Point = { x: int, y: int }` with row-polymorphic field
    access (`fn getx r = r.x`)
  - synonyms: `type Meters = int`
  - `[T]` remains the list-of-`T` type; sums with two or more alternatives use
    `|` (bracketed `[a | b]` works in any type position)
  - type application is juxtaposed: `Option int`, `Pair int str`
- **Checked specs**: `spec` signatures are verified against their definitions
  (skolemized conformance, including `::` constraint coverage)
- **Let bindings** with optional `mut` for mutation
- **Functions** via curried `fn` clauses with pattern matching
- **Lambdas** with `=>` syntax and optional type annotations
- **Pattern matching** on literals, constructors, typed patterns, tuples,
  lists (`[x, ...rest]`), and records (`{x: a, ...rest}`)
- **Records** with field access and spread (`{...base, x: 1}`)
- **Higher-order intrinsics**: `map`, `filter`, `foldl`, `any`, `all`, `range`
- **Blocks** as expressions with block scoping (types may be declared per
  block, shadowing outer ones)

### Conventions and limitations

- Constructor names must start with an uppercase letter; in unbracketed
  `type` alternatives an uppercase identifier is always a constructor.
- Numeric literals are monomorphic: `fn double x = x + x` is polymorphic, but
  `x * 2` fixes `x : int`.
- `ref`/`mut` are typed (`ref T`, `mut T`) but there is no borrow checking;
  runtime checks remain the authority.
- `where` refinements are parsed but not checked; match exhaustiveness is not
  analyzed (a non-matching scrutinee is a runtime error).
- Constructor names share one global namespace per scope; redeclaration at the
  top level is an error, nested blocks may shadow.

## Tests

```bash
cargo test
```

The suite runs every `tests/samples/*.lt` through the full pipeline
(parse → type-check → evaluate) plus targeted positive/negative type-checker
tests in `tests/typecheck.rs`. See `SUM_TYPES_PLAN.md` for the design notes.
