# Where-clause refinement checking

Status: implemented (v1). Checker-side, SMT-backed, no runtime fallback.

## What a `where` clause is

A `spec` may carry a comma-separated list of Lento boolean expressions that
refine the whole signature:

```lento
spec divide:
    (x: int) -> (y: int) -> (r: int)
    where
        y != 0,
        r * y <= x

fn divide x y = x / y
```

The clause parameters are the names bound by the spec's annotated binders —
`(x: int)`, `(y: int)`, `(r: int)`. A clause may only reference these names;
anything else is an unknown-identifier error. Bare (unnamed) binders cannot be
referenced by clauses.

## Classification: preconditions and postconditions

Let the spec's arrow type end in a final named binder `(r: T)`. That name is
the **result parameter**. Every clause is classified by a single rule:

- The clause references the result parameter name → **postcondition**.
- The clause does not reference the result parameter → **precondition**.

Because parameters are immutable, input parameters have the same values before
and after the call, so a postcondition may freely relate the result to the
inputs (as `r * y <= x` does with `y` and `x`), and a precondition still
describes the inputs at every point where it is meaningful.

## Checking obligations

### Preconditions: obligations on callers

A precondition must hold at **every fully applied call site** of the spec'd
function. The checker encodes the argument expressions into SMT and asks the
solver whether the clause can be violated. A definite counterexample is a
compile/type error reported at the call site.

```lento
divide 20 4        # ok: 4 != 0 provable
divide x y         # error: unprovable for symbolic x, y
```

Consequences (deliberate, for soundness):

- Partial application of a function with preconditions
  (`let g = divide 20`) is a compile error: the obligation for the remaining
  argument cannot be tracked through first-class function values in v1.
- Passing a spec'd function with preconditions as a value (to `map`, into a
  lambda, …) is a compile error for the same reason.
- Functions with postconditions only have no caller obligations and may be
  passed around freely.

### Postconditions: obligations on the definition

The checker encodes the function body with the inputs as universally
quantified solver variables and the result parameter bound to the encoded
body, assumes the spec's preconditions, and asks whether the postcondition
can be violated. A definite counterexample is a compile/type error at the
spec (with the witness in the message); the definition never runs.

```lento
spec divide:
    (x: int) -> (y: int) -> (r: int)
    where
        y != 0,
        r * y <= x
```

Note this postcondition is *false* for truncated division: `x = -1, y = 2`
gives `r = 0` and `0 * 2 = 0 > -1`. The sample in `tests/samples/spec_where.lt`
therefore also requires `x >= 0`. Weakening or strengthening clauses is the
author's responsibility; the checker only reports definite violations.

### Solver limits on division

Even the *true* form (`y != 0`, `x >= 0`, `r * y <= x`) exceeds what
bit-vector solvers prove in bounded time: relating `x sdiv y` back to `y`
over 64-bit inputs is a hard bit-blasting problem (both cvc5 and z3 run past
a two-minute budget on it). Under the strict contract this surfaces as a
`cannot verify` compile error. Sample `divide` therefore carries
preconditions only (`y != 0`, `x >= 0`); its calls are verified per call
site, which is fast and exact for the concrete arguments it uses.
Postconditions that restate the body (`spec square: (x: int) -> (r: int)
where r == x * x`) verify instantly.

## Solver model

- Solver: **cvc5** via its official Rust bindings (`cvc5` crate). The solver
  binary on the system is not used.
- Integers are 64-bit **bitvectors**, matching the runtime's `i64`:
  decidable quantifier-free reasoning, `sdiv`/`srem` truncated semantics
  match the evaluator. (One divergence: `INT_MIN / -1` is a runtime panic but
  defined `INT_MIN` in bitvector semantics.)
- Floats are IEEE 754 **double precision** (`FP64`).
- Booleans are solver booleans.
- Unsupported feature → compile error. The following cannot be encoded in v1
  and make any clause (or postcondition body) that needs them fail checking:
  strings, lists, tuples, records, sums/constructors, `ref`/`mut` operations,
  higher-order or intrinsic calls outside the arithmetic/comparison/logic
  subset below.

### Encodable expression subset

- literals: int, float, bool
- variables: clause parameters (and the result parameter inside bodies)
- arithmetic: `+ - * / %` (unary `-` included)
- comparisons: `== != < <= > >=`
- logic: `&& || !`
- `if`/`else` and blocks whose value is one of the above
- int/float are not mixed: a clause or body that would coerce (e.g. `x * 2.0`
  with `x : int`) is unsupported

### Strictness

The solver is expected to answer `sat` or `unsat`. `unknown` and timeouts are
**compile errors** (`cannot verify clause ...`), so checking is
deterministic: a program either passes with all clauses decided, or fails.
There is no runtime enforcement and no silent acceptance.
