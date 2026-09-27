# TODO — lento-pest

Working status doc. Completed work is at the top; remaining work below.
Deferred-feature decisions live in `SUM_TYPES_PLAN.md` (non-goals list);
where-clause design in `docs/where-refinements.md`.

## Done

### 2026-09 — canonical type-checker migration

All found by review; regression coverage lives in `tests/analysis.rs`,
`tests/infer.rs`, and the focused subsystem test files.

- Assignment never checked the assigned value against the binding's type
  (`x = "hello"` after `let mut x = 5` checked clean). Mutable lets are
  monomorphic, so the value is now unified with the binding's current type.
- Parameterized type synonyms silently dropped their type arguments
  (`Wrapper int` ≡ `Wrapper str`). Arguments now bind to the synonym's
  parameters, mirroring `ctor_instance` for sums.
- Let annotations now unify before pending class constraints are solved;
  concrete unsatisfied constraints are rejected.
- Spec conformance only fired when the named `let` was processed: specs
  declared after their definition were never checked, and specs without any
  definition passed silently. End-of-program sweep now verifies every
  recorded spec.
- `.len` on tuples/lists was rejected by member access while the `Len`
  class and the runtime both accept it. `.len` on concrete tuples/lists now
  type-checks; closed records intentionally stay plain field lookups
  (matches `eval_member`).

### 2026-09 — SMT-checked where-clause refinements

`spec ... where ...` clauses were parsed but ignored. Now verified
statically with cvc5 (official Rust bindings); see
`docs/where-refinements.md` for the full design.

- Clause classification: the spec's final named binder is the result
  parameter; clauses referencing it are postconditions, the rest are
  preconditions. Only named binders are referencable.
- Preconditions are proven at every fully applied call site (caller
  variables become solver constants of their inferred sorts); partial
  application and first-class use of precondition-carrying functions are
  compile errors.
- Postconditions are proven against the definition body (result bound to
  the encoded body, inputs universally quantified, preconditions assumed);
  counterexamples carry witnesses.
- Encoding: ints as 64-bit bitvectors (runtime `i64`), floats as IEEE-754
  doubles, bools. Anything outside the subset (strings, lists, records,
  match bodies, intrinsics) or a solver `unknown`/timeout is a strict
  compile error — no runtime fallback.
- Companion fix: parser applied no operator precedence (`1 + 2 * 3` was 9);
  now precedence-climbing, `|| < && < cmp < +- < */%`.

### 2026-09 — match exhaustiveness analysis

Non-matching scrutinees were runtime errors. Matches are now checked
statically; see `src/exhaustive.rs` module docs.

- Maranget-style usefulness over a binding-erased pattern IR. Finite
  signatures enumerate cases (sums, bool); lists split nil/cons with an
  irrefutable-row dominance shortcut; tuples/records expand into columns.
- Undetermined scrutinee columns are judged against the shapes the arms
  admit (sound because the checker's deferred `Member` constraints pin the
  column — verified empirically).
- A scrutinee that is literally a constructor application pins the tag:
  one unguarded arm must match it. Guarded arms cover nothing; typed
  patterns with refutable inners claim nothing.
- Missing-case errors name the case (`missing constructor 'None'`,
  `missing an empty list`).
- Typed pattern annotations contribute their declared domains to coverage;
  uppercase constructor patterns retain constructor identity.
- Grammar change: match arms must be separated by commas (may sit at
  end-of-line; no trailing comma; `;` and bare-newline separators removed).
  pprint emits commas; all samples and inline test programs updated.

### 2026-09 — user-defined type-class constraints

- Class names are resolved from declaration metadata, not a builtin allowlist.
- Class methods carry their owning class constraint in their schemes.
- Constrained implementations recursively require prerequisite instances.
- Regression coverage includes a user-defined `Show` class and constrained
  `Seq` implementation in `tests/analysis.rs`.

### 2026-09 — modules and direct imports

- Inline modules use `mod name { ... }`.
- Files are automatically modules; sibling `name.lt` and `name/mod.lt` files
  are discovered by file loading.
- `use name.subname` imports all exported declarations directly.
- Root declarations shadow imported names.
- All top-level module declarations are exported initially.

### 2026-09 — row-polymorphic records and variants

- `[T]` is reserved for lists; `[int | str]` is a list of union elements.
- Quantified record rows use `{ x: int, ...rest }`.
- Quantified variant rows use `Some int | None | ...rest`.
- Closed record parameters accept wider records with extra fields.
- Untyped record and list rest patterns infer open row information.

## Remaining

Ordered by current priority. All were explicit non-goals in
`SUM_TYPES_PLAN.md` unless noted.

1. **Borrow/exclusivity discipline** — `ref`/`mut` are typed but unchecked;
   runtime checks remain the authority.
2. **Expression-level error spans** — errors report the enclosing
   statement's line:col only.
3. **Uppercase lambda-param collision** — `A b =>` parses as a constructor
   pattern, not an annotated lambda param; documented convention
   (lowercase params are the norm), unfixed.

### Known limitations introduced with recent features

- **Exhaustiveness, closed-world columns**: for a scrutinee whose type is
  not yet determined, completeness is judged against the shapes the arms
  admit. An unknown column whose arms name only one constructor of a
  multi-alternative sum passes checking; other alternatives are not
  demanded. Latent only: current typing rejects such callsites.
- **Where-clauses, solver budget**: postconditions relating `sdiv` results
  to inputs (`r * y <= x` for `x / y`) are true but exceed bounded
  bit-blasting budgets (cvc5 and z3 both) → `cannot verify` compile error.
  Verification is all-or-nothing; there is no runtime check and no
  acceptance on `unknown`.
- **REPL** is parse-only by design (no type checking in the REPL or
  `--fmt` paths).
