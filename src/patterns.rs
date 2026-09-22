// Pattern usefulness and exhaustiveness over a specialization's parameter
// vector, analyzed as ONE product `(p1, ..., pn)` — not column-locally,
// because correlations between columns matter.
//
// Within ONE specialization, clauses dispatch by source order (ML/Haskell
// equation semantics). A catch-all placed first makes later value-pattern
// clauses in the SAME specialization unreachable; clauses in a DIFFERENT
// specialization are unaffected (type dispatch selects the specialization
// before value dispatch runs).
//
// Severity, per the clarified model:
//   - non-exhaustive specialization: warning (configurable as error);
//   - unreachable/redundant clause: warning;
//   - duplicate indistinguishable clause (semantically equivalent vector
//     earlier at the same specificity): error.
//
// Guards do NOT contribute to exhaustiveness (a guarded clause may fail at
// runtime). List witnesses for an uncovered `[y]` are the structural
// complement `[]` and `[_, _, ..._]` (non-singleton), reported as such.
//
// There is no cross-specialization value-pattern fallback: once a
// specialization is selected statically, a value-pattern failure is a match
// failure, never a retry of a less-specific specialization.

use std::fmt;

use crate::ast::{Lit, PatKind, Pattern};
use crate::specialize::Specialization;

/// A pattern diagnostic.
#[derive(Debug, Clone, PartialEq)]
pub struct PatternDiagnostic {
    pub severity: Severity,
    pub kind: DiagnosticKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DiagnosticKind {
    /// Clause `index` can never match: an earlier clause at the same
    /// specificity covers every value it would.
    UnreachableClause { index: usize },
    /// Clause `index` is indistinguishable from an earlier clause
    /// (`earlier`): semantically equivalent pattern vectors in one
    /// specialization. An error (duplicate definition).
    DuplicateClause { index: usize, earlier: usize },
    /// The specialization does not cover every value of its parameter
    /// product; `witnesses` describe the uncovered shapes.
    NonExhaustive { witnesses: Vec<String> },
}

impl fmt::Display for PatternDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sev = match self.severity {
            Severity::Warning => "warning",
            Severity::Error => "error",
        };
        match &self.kind {
            DiagnosticKind::UnreachableClause { index } => write!(
                f,
                "{sev}: unreachable function clause {index}: an earlier clause covers every value it would match"
            ),
            DiagnosticKind::DuplicateClause { index, earlier } => write!(
                f,
                "{sev}: clause {index} is indistinguishable from clause {earlier}"
            ),
            DiagnosticKind::NonExhaustive { witnesses } => write!(
                f,
                "{sev}: non-exhaustive function clauses: uncovered calls include {}",
                witnesses.join(", ")
            ),
        }
    }
}

// --------------------------------------------------------------------------
// Pattern vector model
// --------------------------------------------------------------------------
//
// A clause's parameter vector is a row of simplified patterns. We reduce each
// `Pattern` to a `Pat` constructor form for the usefulness algorithm.

/// A simplified pattern for usefulness analysis.
#[derive(Debug, Clone, PartialEq)]
enum Pat {
    /// Matches anything (variable or wildcard).
    Wild,
    /// A literal constructor.
    Lit(Lit),
    /// A tuple of sub-patterns.
    Tuple(Vec<Pat>),
    /// A list of EXACTLY n elements (a cons of length n). `List(n, pats)`.
    /// Lists of other lengths are different constructors.
    List(usize, Vec<Pat>),
    /// A list with a rest: `ListOrMore(n, pats)` matches lists of length >= n.
    ListOrMore(usize, Vec<Pat>),
    /// A nominal sum constructor and its optional payload.
    Constructor(String, Option<Box<Pat>>),
    /// A record: a set of named fields (open — extra fields allowed).
    Record(Vec<(String, Pat)>),
}

fn simplify(p: &Pattern) -> Pat {
    match &p.kind {
        PatKind::Var(_) | PatKind::Wildcard => Pat::Wild,
        PatKind::Lit(l) => Pat::Lit(l.clone()),
        PatKind::Tuple(ps) => Pat::Tuple(ps.iter().map(simplify).collect()),
        PatKind::List(ps) => {
            // A trailing `...rest` makes the list match length >= n; without
            // it the list is exact-length.
            let has_spread = matches!(ps.last().map(|p| &p.kind), Some(PatKind::Spread(_)));
            let prefix: Vec<Pat> = ps
                .iter()
                .take(if has_spread { ps.len() - 1 } else { ps.len() })
                .map(simplify)
                .collect();
            if has_spread {
                Pat::ListOrMore(prefix.len(), prefix)
            } else {
                Pat::List(ps.len(), prefix)
            }
        }
        PatKind::Spread(_) => Pat::Wild, // `...rest` matches any suffix list
        PatKind::Constructor { name, payload } => Pat::Constructor(
            name.clone(),
            payload.as_deref().map(simplify).map(Box::new),
        ),
        PatKind::Record { fields, .. } => Pat::Record(
            fields
                .iter()
                .map(|f| (f.name.clone(), simplify(&f.pattern)))
                .collect(),
        ),
    }
}

// --------------------------------------------------------------------------
// Usefulness / exhaustiveness (Maranget-style, specialized to Lento)
// --------------------------------------------------------------------------

/// Does pattern vector `p` cover vector `q` (every value matching `q` also
/// matches `p`)? `p` and `q` are rows of the same arity.
fn covers(p: &[Pat], q: &[Pat]) -> bool {
    p.iter().zip(q.iter()).all(|(a, b)| covers1(a, b))
}

/// Single-column coverage: every value matching `q` matches `p`.
fn covers1(p: &Pat, q: &Pat) -> bool {
    match (p, q) {
        (Pat::Wild, _) => true,
        (Pat::Lit(a), Pat::Lit(b)) => a == b,
        (Pat::Lit(_), _) => false,
        (Pat::Tuple(a), Pat::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| covers1(x, y))
        }
        (Pat::Tuple(_), Pat::Wild) => false,
        (Pat::Constructor(name_a, payload_a), Pat::Constructor(name_b, payload_b)) => {
            name_a == name_b
                && match (payload_a, payload_b) {
                    (None, None) => true,
                    (Some(a), Some(b)) => covers1(a, b),
                    _ => false,
                }
        }
        (Pat::Constructor(..), Pat::Wild) => false,
        // List coverage: exact-length vs exact-length, and or-more handling.
        (Pat::List(n, a), Pat::List(m, b)) => {
            n == m && a.iter().zip(b.iter()).all(|(x, y)| covers1(x, y))
        }
        (Pat::ListOrMore(n, a), Pat::List(m, b)) => {
            // `p` matches length >= n; `q` has exact length m. Covers iff
            // m >= n and the first n p-subpatterns cover q's.
            m >= n && a.iter().zip(b.iter()).take(*n).all(|(x, y)| covers1(x, y))
        }
        (Pat::ListOrMore(n, a), Pat::ListOrMore(m, b)) => {
            n <= m && a.iter().zip(b.iter()).take(*n).all(|(x, y)| covers1(x, y))
        }
        (Pat::List(..), Pat::ListOrMore(..)) => false,
        (Pat::List(..) | Pat::ListOrMore(..), Pat::Wild) => false,
        // Records are open: `p` covers `q` iff every field of `p` is present
        // (and covered) in `q`.
        (Pat::Record(pf), Pat::Record(qf)) => pf.iter().all(|(name, sub)| {
            qf.iter()
                .find(|(n, _)| n == name)
                .map(|(_, qsub)| covers1(sub, qsub))
                .unwrap_or(false)
        }),
        (Pat::Record(_), Pat::Wild) => false,
        _ => false,
    }
}

/// Are two pattern vectors semantically equivalent (each covers the other)?
fn equivalent(a: &[Pat], b: &[Pat]) -> bool {
    covers(a, b) && covers(b, a)
}

/// The constructors of a literal type, for computing uncovered witnesses.
/// `int`/`str`/`float` are infinite; `bool` is finite.
fn lit_constructors(l: &Lit) -> &'static str {
    match l {
        Lit::Bool(_) => "bool",
        Lit::Int(_) => "int",
        Lit::Float(_) => "float",
        Lit::Str(_) => "str",
    }
}

/// Analyze one specialization's clauses for usefulness and exhaustiveness.
///
/// Returns diagnostics in source order. The specialization's clauses are the
/// rows of one pattern matrix over the parameter product.
pub fn analyze_specialization(spec: &Specialization) -> Vec<PatternDiagnostic> {
    let mut diagnostics = Vec::new();
    let rows: Vec<Vec<Pat>> = spec
        .clauses
        .iter()
        .map(|c| c.patterns.iter().map(simplify).collect())
        .collect();

    // Duplicate (semantically equivalent) and unreachable detection.
    for (i, row) in rows.iter().enumerate() {
        // Duplicate: an earlier row equivalent to this one.
        for (j, earlier) in rows.iter().enumerate().take(i) {
            if equivalent(row, earlier) {
                diagnostics.push(PatternDiagnostic {
                    severity: Severity::Error,
                    kind: DiagnosticKind::DuplicateClause {
                        index: i,
                        earlier: j,
                    },
                });
                break;
            }
        }
        // Unreachable: some earlier row covers every value this row matches.
        // (Weaker than duplication: earlier is at least as general.)
        if !diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::DuplicateClause { index, .. } if index == i
        )) {
            let covered = rows
                .iter()
                .take(i)
                .any(|earlier| covers(earlier, row));
            if covered {
                diagnostics.push(PatternDiagnostic {
                    severity: Severity::Warning,
                    kind: DiagnosticKind::UnreachableClause { index: i },
                });
            }
        }
    }

    // Exhaustiveness: is there a value of the parameter product matching NO
    // unguarded row? Compute witnesses for the gaps.
    let witnesses = uncovered_witnesses(&rows);
    if !witnesses.is_empty() {
        diagnostics.push(PatternDiagnostic {
            severity: Severity::Warning,
            kind: DiagnosticKind::NonExhaustive { witnesses },
        });
    }

    diagnostics
}

/// Compute a small set of witness shapes not covered by any row.
///
/// This is a PRODUCT-level search: a candidate vector is uncovered only when
/// NO row covers it in EVERY column simultaneously, so correlations between
/// columns are respected (e.g. `(true, [])` / `(false, [x,...xs])` leaves
/// `(true, [_,..._])` and `(false, [])` uncovered). Guards are ignored —
/// guarded rows never count as covering.
fn uncovered_witnesses(rows: &[Vec<Pat>]) -> Vec<String> {
    if rows.is_empty() {
        return vec!["_".to_string()];
    }
    let arity = rows[0].len();
    // An unguarded all-wildcard row is a catch-all: exhaustive.
    if rows.iter().any(|r| r.iter().all(|p| matches!(p, Pat::Wild))) {
        return Vec::new();
    }
    // Search for one uncovered vector, then render it.
    match find_uncovered(rows, arity) {
        Some(witness) => vec![render_witness(&witness)],
        None => Vec::new(),
    }
}

/// Recursively search for a vector of `arity` columns that no row covers.
/// Returns the uncovered vector (as concrete `Pat`s / `Wild`) if one exists.
fn find_uncovered(rows: &[Vec<Pat>], arity: usize) -> Option<Vec<Pat>> {
    // Enumerate constructor candidates per column derived from the rows, plus
    // each column's complement. This bounded enumeration is sufficient for
    // Lento's constructor forms (literals, lists, tuples, records).
    let mut col_candidates: Vec<Vec<Pat>> = Vec::new();
    for col in 0..arity {
        let mut cands: Vec<Pat> = Vec::new();
        let mut has_wild_row = false;
        for r in rows {
            match &r[col] {
                Pat::Wild => has_wild_row = true,
                Pat::Lit(l) => cands.push(Pat::Lit(l.clone())),
                Pat::List(n, subs) => cands.push(Pat::List(*n, subs.clone())),
                Pat::ListOrMore(n, subs) => cands.push(Pat::ListOrMore(*n, subs.clone())),
                Pat::Tuple(subs) => cands.push(Pat::Tuple(subs.clone())),
                Pat::Constructor(name, payload) => {
                    cands.push(Pat::Constructor(name.clone(), payload.clone()));
                    if payload.is_some() {
                        cands.push(Pat::Constructor(
                            name.clone(),
                            Some(Box::new(Pat::Wild)),
                        ));
                    }
                }
                Pat::Record(fields) => cands.push(Pat::Record(fields.clone())),
            }
        }
        // Add the column's complement constructor when the domain is not
        // fully covered by the enumerated constructors.
        // Bool: add the missing bool literal.
        let bools: Vec<bool> = cands
            .iter()
            .filter_map(|p| match p {
                Pat::Lit(Lit::Bool(b)) => Some(*b),
                _ => None,
            })
            .collect();
        if !bools.is_empty() {
            for b in [true, false] {
                if !bools.contains(&b) {
                    cands.push(Pat::Lit(Lit::Bool(b)));
                }
            }
        } else if !has_wild_row {
            // Non-bool literal columns (int/str/float) are infinite: a
            // wildcard complement is always available.
            let has_lit = cands.iter().any(|p| matches!(p, Pat::Lit(_)));
            if has_lit {
                cands.push(Pat::Wild);
            }
        }
        // Lists: if there is a ListOrMore, lengths below its bound need exact
        // lists; if only exact lists, add `[]` and a longer open list.
        let list_lens: Vec<usize> = cands
            .iter()
            .filter_map(|p| match p {
                Pat::List(n, _) => Some(*n),
                _ => None,
            })
            .collect();
        let min_or_more = cands
            .iter()
            .filter_map(|p| match p {
                Pat::ListOrMore(n, _) => Some(*n),
                _ => None,
            })
            .min();
        if !list_lens.is_empty() || min_or_more.is_some() {
            match min_or_more {
                Some(bound) => {
                    for len in 0..bound {
                        if !list_lens.contains(&len) {
                            cands.push(Pat::List(len, vec![Pat::Wild; len]));
                        }
                    }
                }
                None => {
                    if !list_lens.contains(&0) {
                        cands.push(Pat::List(0, vec![]));
                    }
                    let max = list_lens.iter().max().copied().unwrap_or(0);
                    cands.push(Pat::ListOrMore(max + 1, vec![Pat::Wild; max + 1]));
                }
            }
        }
        // The column always admits the complement as a wildcard.
        if cands.is_empty() {
            cands.push(Pat::Wild);
        }
        col_candidates.push(cands);
    }

    // Cartesian product over the column candidates; the first vector no row
    // covers is a witness.
    let mut witness: Option<Vec<Pat>> = None;
    let mut current: Vec<Pat> = Vec::with_capacity(arity);
    product_search(rows, &col_candidates, 0, &mut current, &mut witness);
    witness
}

fn product_search(
    rows: &[Vec<Pat>],
    col_candidates: &[Vec<Pat>],
    col: usize,
    current: &mut Vec<Pat>,
    witness: &mut Option<Vec<Pat>>,
) {
    if witness.is_some() {
        return;
    }
    if col == col_candidates.len() {
        if !rows.iter().any(|r| covers(r, current)) {
            *witness = Some(current.clone());
        }
        return;
    }
    for cand in &col_candidates[col] {
        current.push(cand.clone());
        product_search(rows, col_candidates, col + 1, current, witness);
        current.pop();
        if witness.is_some() {
            return;
        }
    }
}

/// Render an uncovered witness vector as a source-like shape.
fn render_witness(v: &[Pat]) -> String {
    let parts: Vec<String> = v.iter().map(render_pat).collect();
    if v.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        format!("({})", parts.join(", "))
    }
}

fn render_pat(p: &Pat) -> String {
    match p {
        Pat::Wild => "_".to_string(),
        Pat::Lit(l) => match l {
            Lit::Bool(b) => b.to_string(),
            Lit::Int(i) => i.to_string(),
            Lit::Float(f) => f.to_string(),
            Lit::Str(s) => format!("\"{s}\""),
        },
        Pat::Tuple(subs) => format!(
            "({})",
            subs.iter().map(render_pat).collect::<Vec<_>>().join(", ")
        ),
        Pat::List(_, subs) => format!(
            "[{}]",
            subs.iter().map(render_pat).collect::<Vec<_>>().join(", ")
        ),
        Pat::ListOrMore(_, subs) => {
            let mut inner: Vec<String> = subs.iter().map(render_pat).collect();
            inner.push("..._".to_string());
            format!("[{}]", inner.join(", "))
        }
        Pat::Constructor(name, payload) => match payload {
            Some(payload) => format!("{name} {}", render_pat(payload)),
            None => name.clone(),
        },
        Pat::Record(fields) => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(n, sub)| format!("{n}: {}", render_pat(sub)))
                .collect();
            format!("{{{}}}", inner.join(", "))
        }
    }
}
