# Lento language reference

This document describes the language currently implemented by `lento-pest`. It is a living reference for an experimental prototype, not a stability promise. Where a design is incomplete, the limitation is stated explicitly.

## 1. Lexical structure

Lento source is UTF-8 text. Statements are separated by one or more newlines or by semicolons. Newlines inside parentheses, brackets, and comma-delimited record forms are insignificant.

Single-line and block comments are supported:

```lento
// A line comment

/*
A block comment
*/
```

Identifiers begin with an ASCII letter or underscore and continue with ASCII letters, digits, or underscores.

The reserved keywords are `spec`, `type`, `let`, `fn`, `mut`, `ref`, `match`, and `if`. The words `all` and `where` are contextual keywords in specifications and may otherwise be used as identifiers.

## 2. Programs and values

A program is an ordered sequence of declarations and expressions. Lento is expression-oriented: blocks, matches, assignments, and function applications produce values. The result of a program or block is its final expression; an empty block produces unit, `()`.

The interpreter currently supports:

- `bool`: `true` and `false`
- `int`: signed integer values
- `float`: decimal floating-point values
- `str`: double-quoted strings
- unit and tuples
- homogeneous lists
- records
- functions and references

Strings recognize `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, and `\'` escapes.

```lento
let answer = 42
let ratio = 1.5
let message = "hello\nworld"
let pair = (answer, message)
let singleton = (answer,)
let nothing = ()
```

Parentheses without a comma group an expression. A tuple requires a comma.

## 3. Bindings, blocks, and mutation

Bindings use `let` and may include a pattern and a type annotation:

```lento
let x = 1
let (left, right) = (1, 2)
let count : int = 3
```

Bindings are immutable by default. A mutable binding is introduced with `let mut` and updated using `=`:

```lento
let mut counter = 0
counter = counter + 1
counter
```

Assignment is valid only when its left-hand side denotes an assignable variable, member, or index. Assigning to an immutable binding is an error.

Blocks introduce lexical scope. Inner bindings do not escape, while updates through an outer mutable binding remain visible:

```lento
let mut x = 1
{
    let step = 2
    x = x + step
}
x // 3
```

## 4. Functions and application

A function clause begins with `fn`, followed by its name, zero or more parameter patterns, an optional return annotation, `=`, and its body:

```lento
fn identity x = x
fn add x y -> int = x + y
fn constant = 42
```

Multiple parameters are curried. Accordingly, `fn add x y = ...` has the shape `a -> b -> c`.

Function application can use whitespace or parentheses:

```lento
add 2 3
add(2, 3)
```

Whitespace application binds more tightly than infix operators. Compound whitespace arguments should be parenthesized. A bare record or block is not accepted as a whitespace argument; write `f ({x: 1})`.

Lambdas use the same parameter-pattern syntax and `=>`:

```lento
let double = x => x * 2
let add = x => y => x + y
map (x => x * 2) [1, 2, 3]
```

Function clauses with the same name are grouped. Clauses are tried in source order within a specialization:

```lento
fn factorial 0 = 1
fn factorial n = n * factorial (n - 1)
```

Arity and explicit parameter annotations may create distinct type specializations. Value patterns alone do not create overloads: `[]` and `[x, ...xs]` are clauses of the same list specialization.

## 5. Patterns

Patterns appear in `let` declarations, function parameters, lambdas, and match arms.

Supported patterns are:

- Variables: `x`
- Wildcards: `_`
- Boolean, numeric, and string literals
- Tuples: `(x, y)`
- Lists: `[]`, `[x]`, `[head, ...tail]`
- Records: `{name: n, active: a}`, `{name: n, ...rest}`
- Annotated patterns: `(x : int)`

Destructuring list and record parameters in a `fn` header are parenthesized to keep the body boundary unambiguous:

```lento
fn head_or_zero ([x, ...xs]) = x
fn display_name ({name: name, ...rest}) = name
```

The semantic analysis detects duplicate and unreachable clauses and reports non-exhaustive specializations. Exhaustiveness is computed over the product of all parameter patterns rather than independently per parameter.

## 6. Match expressions

A match evaluates its scrutinee and selects the first matching arm whose optional guard evaluates to `true`:

```lento
match value {
    0 => "zero"
    n if n < 0 => "negative"
    _ => "positive"
}
```

The opening brace is followed by a newline. Arms may be separated by newlines, semicolons, or commas. Match failure is a runtime error.

## 7. Lists and records

List literals use brackets:

```lento
let xs = [1, 2, 3]
let first = xs[0]
let size = xs.len
```

Records contain named fields. Spread entries copy fields from another record; later fields replace earlier fields with the same name:

```lento
let base = {name: "Ada", active: true}
let updated = {...base, active: false}
updated.name
```

A record literal must contain at least one entry. `{}` is the empty block, not an empty record.

## 8. Operators

From weakest to strongest, binary precedence is:

| Precedence | Operators |
| --- | --- |
| Logical OR | `||` |
| Logical AND | `&&` |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=` |
| Additive | `+`, `-` |
| Multiplicative | `*`, `/`, `%` |

Binary operators are left-associative. Prefix `-`, `!`, and `ref` bind more tightly, followed by calls, member access, and indexing.

Arithmetic supports integers and floating-point values. `+` also concatenates strings. Invalid operand combinations are runtime or inference errors, depending on the execution path.

## 9. Types and inference

Type annotations are optional. The inference implementation represents type variables, constructors, tuples, lists, references, and curried function types.

```lento
let n : int = 42
fn id x = x
fn parse (text : str) -> int = parse_int text
```

Type syntax includes:

```text
int
list_name<a, b>
[a]
()
a -> b
(a -> b) -> c
ref a
mut a
(name : a)
```

Function arrows associate to the right: `a -> b -> c` means `a -> (b -> c)`.

A type declaration introduces a named alias in the parsed language:

```lento
type user_id = int
```

The current prototype contains inference and semantic-analysis APIs, but the command-line interpreter does not yet run the complete static pipeline before evaluation.

## 10. Specifications

A `spec` declares a persistent signature or contract associated with a function group:

```lento
spec identity:
    all a.
    a -> a

fn identity x = x
```

Quantifiers may declare multiple variables and constraints:

```lento
spec compare:
    all a :: ord a.
    a -> a -> bool
```

A specification may include expression refinements introduced by `where`:

```lento
spec divide:
    (x : int) -> (y : int) -> int
    where y != 0
```

Constraint and `where` syntax is represented by the current front end; full constraint solving and refinement enforcement are not yet implemented.

Spec satisfaction is directional subsumption: an implementation must be at least as general as its spec. Informally,

```text
Instances(spec) ⊆ Instances(implementation)
```

Thus a polymorphic identity implementation can satisfy `int -> int`, while an implementation restricted to `int -> int` cannot satisfy `all a. a -> a`.

One specialization must cover an entire spec. Multiple value-pattern clauses may collectively provide that coverage, but distinct type specializations are not combined to satisfy one specification. Functions without specs remain valid and receive inferred signatures. Spec-only groups are permitted as abstract declarations.

## 11. References and mutable places

`mut T` denotes an explicitly mutable place type. `ref T` denotes a reference type, and `ref expression` constructs a reference:

```lento
let mut value = 1
let handle = ref value
```

In the current interpreter, references can be taken from cell-backed bindings; taking a reference to an inline immutable binding fails. The ownership, borrowing, and reference-erasure model is experimental and should not yet be treated as stable semantics.

## 12. Built-in functions

The initial environment includes common functions for I/O, assertions, collections, strings, and higher-order list processing. Implemented examples include:

```text
print, println, assert
len, concat, head, tail, is_empty
map, filter, foldl, any, all, range
take, drop, reverse, slice
contains, join, split
abs, min, max
to_string, parse_int
```

Built-ins generally use curried application:

```lento
let values = range 1 5
let total = foldl (acc => x => acc + x) 0 values
assert (total == 10)
```

`range start end` excludes `end` and descends when `start > end`.

## 13. Implementation notes and known limitations

- The language and this reference are evolving.
- Static analysis exists as library infrastructure and is not yet a mandatory CLI phase.
- Type-class constraints and `where` refinements are parsed but not fully enforced.
- The reference and memory model remain experimental.
- Formatting preserves the AST rather than comments or original whitespace.
- There is no module/package system in this prototype.
- Diagnostics and source spans are still under development.

For the exact accepted concrete syntax, `src/grammar.pest` is authoritative. Tests under `tests/` capture implemented parser, evaluator, inference, specialization, and pattern-analysis behavior.
