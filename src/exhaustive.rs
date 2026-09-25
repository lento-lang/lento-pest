//! Match-exhaustiveness analysis (Maranget-style usefulness).
//!
//! The question asked is always: is a wildcard row still useful against the
//! matrix of (unguarded) arm patterns? If yes, the match is not exhaustive
//! and [`analyze`] reports the first missing case it finds.
//!
//! The module is pure: it sees pruned types and binding-erased patterns
//! ([`CoverPat`], translated by `Checker::translate_pattern`) and never
//! touches the substitution or the environment. One analyzer input is a
//! *fresh unknown type* allocated by the checker for columns whose type is
//! not determined (scrutinee type variables); using a real fresh id keeps
//! them distinct from every pattern-annotation type.
//!
//! Runtime matching semantics mirrored here (src/eval.rs):
//! - record patterns match any record that HAS the named fields (at-least),
//! - list patterns fix the length unless they end in `...rest`,
//! - typed patterns `(n: T)` are runtime type tests covering all of `T`,
//! - a bare uppercase var is a nullary constructor match,
//! - guarded arms match conditionally and are excluded from coverage.
//!
//! Closed-world note: when a scrutinee column's type is still undetermined,
//! completeness is judged against the *shapes the arms themselves admit*
//! (constructors seen, tuple arities, list nil/cons, bool literals, record
//! field sets, typed alternatives). This mirrors the checker's deferred
//! `Member` constraints, which pin the scrutinee to the union of arm types.
//! Limitation: for an undetermined column whose arms name only one
//! constructor of a multi-alternative sum, other alternatives are not
//! demanded; the deferred constraint model treats the arms as jointly
//! describing the type.

use crate::ast::Lit;
use crate::ty::{Con, Type, TypeAlt};

/// Binding-erased pattern for coverage analysis.
#[derive(Clone, Debug)]
pub(crate) enum CoverPat {
    /// Binds or ignores: matches every value of the column type.
    CatchAll,
    /// Literal pattern; covers only that value (bool handled per-case).
    Lit(Lit),
    Tuple(Vec<CoverPat>),
    Ctor {
        name: String,
        payload: Option<Box<CoverPat>>,
    },
    /// `(n: T)` with an irrefutable inner pattern: a type test covering all
    /// of `T`. Refutable inners become `Refutable` (they are sub-cases).
    Typed(Type),
    List {
        prefix: Vec<CoverPat>,
        rest: bool,
    },
    Record {
        fields: Vec<(String, CoverPat)>,
    },
    /// Matches nothing for coverage purposes (refutable sub-shape).
    Refutable,
}

#[derive(Clone)]
pub(crate) struct CoverRow(pub Vec<CoverPat>);

/// Is a wildcard row useful against `rows` over `cols`? `Some(desc)` names
/// the first missing case found; `None` means exhaustive.
pub(crate) fn analyze(cols: &[Type], rows: Vec<CoverRow>, unknown: Type) -> Option<String> {
    uncovered(cols, &rows, &unknown)
}

/// Structural type equality for coverage decisions: constructors by value,
/// sums by declaration id (parameter instantiation is irrelevant to which
/// alternatives exist), compounds recursively.
fn cover_ty_same(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Con(x), Type::Con(y)) => x == y,
        (Type::Sum(x), Type::Sum(y)) => x.id == y.id,
        (Type::Tuple(x), Type::Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| cover_ty_same(a, b))
        }
        (Type::List(x), Type::List(y)) => cover_ty_same(x, y),
        (Type::Record(x), Type::Record(y)) => {
            x.fields.len() == y.fields.len()
                && x.fields
                    .iter()
                    .zip(y.fields.iter())
                    .all(|((an, at), (bn, bt))| an == bn && cover_ty_same(at, bt))
        }
        (Type::Var(x), Type::Var(y)) => x == y,
        _ => false,
    }
}

fn cover_catchalls(n: usize) -> Vec<CoverPat> {
    vec![CoverPat::CatchAll; n]
}

/// Does `pat` match every value of `ty`?
fn cover_irrefutable(pat: &CoverPat, ty: &Type) -> bool {
    match pat {
        CoverPat::CatchAll => true,
        CoverPat::Typed(t) => cover_ty_same(t, ty),
        CoverPat::Record { fields } => fields.iter().all(|(_, p)| cover_irrefutable(p, ty)),
        CoverPat::List { prefix, rest } => prefix.is_empty() && *rest,
        _ => false,
    }
}

/// A shape observed among row heads of an undetermined column.
enum Shape {
    Ctor { name: String, payload: bool },
    Tuple(usize),
    Record(Vec<String>),
    /// Splits into nil and cons cases.
    List,
    Bool(bool),
    /// `(n: T)` arm: a possible alternative of type `T`.
    Typed(Type),
}

fn collect_shapes(m: &[CoverRow]) -> Vec<Shape> {
    let mut shapes: Vec<Shape> = Vec::new();
    let mut push = |s: Shape| {
        let dup = shapes.iter().any(|existing| match (existing, &s) {
            (Shape::Ctor { name: a, payload: pa }, Shape::Ctor { name: b, payload: pb }) => {
                a == b && pa == pb
            }
            (Shape::Tuple(a), Shape::Tuple(b)) => a == b,
            (Shape::Record(a), Shape::Record(b)) => a == b,
            (Shape::List, Shape::List) => true,
            (Shape::Bool(a), Shape::Bool(b)) => a == b,
            (Shape::Typed(a), Shape::Typed(b)) => cover_ty_same(a, b),
            _ => false,
        });
        if !dup {
            shapes.push(s);
        }
    };
    for row in m {
        let Some((head, _)) = row.0.split_first() else {
            continue;
        };
        match head {
            CoverPat::Ctor { name, payload } => push(Shape::Ctor {
                name: name.clone(),
                payload: payload.is_some(),
            }),
            CoverPat::Tuple(ps) => push(Shape::Tuple(ps.len())),
            CoverPat::List { .. } => push(Shape::List),
            CoverPat::Record { fields } => {
                let mut names: Vec<String> = fields.iter().map(|(n, _)| n.clone()).collect();
                names.sort();
                push(Shape::Record(names));
            }
            CoverPat::Lit(Lit::Bool(_)) => {
                // A bool literal head makes the column's bool-ness known:
                // enumerate both literals regardless of which was seen.
                push(Shape::Bool(true));
                push(Shape::Bool(false));
            }
            CoverPat::Typed(t) => push(Shape::Typed(t.clone())),
            _ => {}
        }
    }
    shapes
}

fn cover_describe_ty(ty: &Type) -> String {
    match ty {
        Type::Con(Con::Int) => "an int".into(),
        Type::Con(Con::Float) => "a float".into(),
        Type::Con(Con::Str) => "a string".into(),
        Type::Con(Con::Bool) => "a bool".into(),
        Type::Con(Con::Unit) => "unit".into(),
        Type::Var(_) => "any value".into(),
        other => format!("a value of type {other}"),
    }
}

/// Specialize the matrix for one constructor case: keep rows whose head
/// matches (or irrefutably covers) the case, and expose the case's value
/// column(s) in front of the row tail.
fn specialize_ctor(
    name: &str,
    payload: Option<&Type>,
    sum_ty: &Type,
    m: &[CoverRow],
) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            let head_cols: Vec<CoverPat> = match head {
                CoverPat::CatchAll => match payload {
                    Some(_) => vec![CoverPat::CatchAll],
                    None => vec![],
                },
                CoverPat::Ctor {
                    name: n,
                    payload: p,
                } if n == name => match (payload, p) {
                    (Some(_), Some(p)) => vec![(**p).clone()],
                    // Payload-bearing case against a nullary pattern cannot
                    // occur (arity is checked during inference).
                    (Some(_), None) => return None,
                    (None, _) => vec![],
                },
                CoverPat::Typed(t) if cover_ty_same(t, sum_ty) => match payload {
                    Some(_) => vec![CoverPat::CatchAll],
                    None => vec![],
                },
                _ => return None,
            };
            let mut new_row = head_cols;
            new_row.extend(tail.iter().cloned());
            Some(CoverRow(new_row))
        })
        .collect()
}

/// Specialize for a bare-alternative (typed) case of value type `alt_ty`.
fn specialize_typed(alt_ty: &Type, sum_ty: &Type, m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            let covers = match head {
                CoverPat::CatchAll => true,
                CoverPat::Typed(t) => cover_ty_same(t, alt_ty) || cover_ty_same(t, sum_ty),
                CoverPat::Record { .. } | CoverPat::Tuple(_) | CoverPat::List { .. } => {
                    cover_irrefutable(head, alt_ty)
                }
                _ => false,
            };
            if !covers {
                return None;
            }
            let mut new_row = vec![CoverPat::CatchAll];
            new_row.extend(tail.iter().cloned());
            Some(CoverRow(new_row))
        })
        .collect()
}

/// Specialize for `true`/`false`.
fn specialize_bool(b: bool, m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            match head {
                CoverPat::CatchAll => Some(tail.to_vec()),
                CoverPat::Lit(Lit::Bool(v)) if *v == b => Some(tail.to_vec()),
                _ => None,
            }
        })
        .map(CoverRow)
        .collect()
}

/// Specialize for the empty list.
fn specialize_nil(m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            match head {
                CoverPat::CatchAll => Some(tail.to_vec()),
                // `[]` and the irrefutable `[...r]` both match nil.
                CoverPat::List { prefix, .. } if prefix.is_empty() => Some(tail.to_vec()),
                _ => None,
            }
        })
        .map(CoverRow)
        .collect()
}

/// Specialize for a cons cell: expose head element and tail list columns.
/// A spread-only `[...r]` head matches cons cells too (two catch-alls).
fn specialize_cons(m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            let head_cols: Vec<CoverPat> = match head {
                CoverPat::CatchAll => vec![CoverPat::CatchAll, CoverPat::CatchAll],
                CoverPat::List { prefix, rest } => match prefix.split_first() {
                    Some((first, rest_prefix)) => {
                        let mut cols = vec![first.clone()];
                        cols.push(CoverPat::List {
                            prefix: rest_prefix.to_vec(),
                            rest: *rest,
                        });
                        cols
                    }
                    // `[]` never matches a cons cell; `[...r]` matches all.
                    None if *rest => vec![CoverPat::CatchAll, CoverPat::CatchAll],
                    None => return None,
                },
                _ => return None,
            };
            let mut new_row = head_cols;
            new_row.extend(tail.iter().cloned());
            Some(CoverRow(new_row))
        })
        .collect()
}

/// Expand a tuple-typed column into its component columns.
fn expand_tuple(tys: &[Type], m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            let head_cols: Vec<CoverPat> = match head {
                CoverPat::CatchAll => cover_catchalls(tys.len()),
                CoverPat::Tuple(ps) if ps.len() == tys.len() => ps.clone(),
                CoverPat::Typed(_) => cover_catchalls(tys.len()),
                _ => return None,
            };
            let mut new_row = head_cols;
            new_row.extend(tail.iter().cloned());
            Some(CoverRow(new_row))
        })
        .collect()
}

/// Expand a record-typed column into one column per known field.
fn expand_record(fields: &[(String, Type)], m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            let head_cols: Vec<CoverPat> = match head {
                CoverPat::CatchAll => cover_catchalls(fields.len()),
                CoverPat::Typed(_) => cover_catchalls(fields.len()),
                CoverPat::Record { fields: pf } => fields
                    .iter()
                    .map(|(name, _)| {
                        pf.iter()
                            .find(|(n, _)| n == name)
                            .map(|(_, p)| p.clone())
                            .unwrap_or(CoverPat::CatchAll)
                    })
                    .collect(),
                _ => return None,
            };
            let mut new_row = head_cols;
            new_row.extend(tail.iter().cloned());
            Some(CoverRow(new_row))
        })
        .collect()
}

/// Drop rows whose head cannot cover any value of a column with no finite
/// signature, and expose the tails of the rows that cover everything.
fn specialize_irrefutable(ty: &Type, m: &[CoverRow]) -> Vec<CoverRow> {
    m.iter()
        .filter_map(|row| {
            let (head, tail) = row.0.split_first()?;
            match head {
                h if cover_irrefutable(h, ty) => Some(tail.to_vec()),
                _ => None,
            }
        })
        .map(CoverRow)
        .collect()
}

/// No irrefutable row exists for a column of undetermined type. Enumerate
/// the shapes present among the rows' heads; the column could be of any of
/// them, so every shape must be covered on its own. With no enumerable
/// shape present (bare non-bool literals only) some value remains
/// uncovered.
fn missing_unknown(m: &[CoverRow], rest_cols: &[Type], unknown: &Type) -> Option<String> {
    let shapes = collect_shapes(m);
    let saw_shape = !shapes.is_empty();
    for shape in &shapes {
        match shape {
            Shape::Ctor { name, payload } => {
                let mut sub_cols: Vec<Type> = Vec::new();
                if *payload {
                    sub_cols.push(unknown.clone());
                }
                sub_cols.extend(rest_cols.iter().cloned());
                let sub: Vec<CoverRow> = m
                    .iter()
                    .filter_map(|row| {
                        let (head, tail) = row.0.split_first()?;
                        match head {
                            CoverPat::Ctor {
                                name: n,
                                payload: p,
                            } if n == name => {
                                let mut cols: Vec<CoverPat> = match (payload, p) {
                                    (true, Some(p)) => vec![(**p).clone()],
                                    (true, None) => vec![CoverPat::CatchAll],
                                    (false, _) => vec![],
                                };
                                cols.extend(tail.iter().cloned());
                                Some(CoverRow(cols))
                            }
                            _ => None,
                        }
                    })
                    .collect();
                if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                    return Some(format!("constructor '{name}' ({d})"));
                }
            }
            Shape::Tuple(k) => {
                let mut sub_cols: Vec<Type> = vec![unknown.clone(); *k];
                sub_cols.extend(rest_cols.iter().cloned());
                let sub: Vec<CoverRow> = m
                    .iter()
                    .filter_map(|row| {
                        let (head, tail) = row.0.split_first()?;
                        match head {
                            CoverPat::Tuple(ps) if ps.len() == *k => {
                                let mut cols = ps.clone();
                                cols.extend(tail.iter().cloned());
                                Some(CoverRow(cols))
                            }
                            _ => None,
                        }
                    })
                    .collect();
                if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                    return Some(format!("a {k}-component tuple ({d})"));
                }
            }
            Shape::Record(field_names) => {
                let mut sub_cols: Vec<Type> = vec![unknown.clone(); field_names.len()];
                sub_cols.extend(rest_cols.iter().cloned());
                let sub: Vec<CoverRow> = m
                    .iter()
                    .filter_map(|row| {
                        let (head, tail) = row.0.split_first()?;
                        match head {
                            CoverPat::Record { fields } => {
                                let mut names: Vec<&String> =
                                    fields.iter().map(|(n, _)| n).collect();
                                names.sort();
                                if names.len() == field_names.len()
                                    && names
                                        .iter()
                                        .zip(field_names.iter())
                                        .all(|(a, b)| a.as_str() == b.as_str())
                                {
                                    let mut cols: Vec<CoverPat> =
                                        fields.iter().map(|(_, p)| p.clone()).collect();
                                    cols.extend(tail.iter().cloned());
                                    return Some(CoverRow(cols));
                                }
                                None
                            }
                            _ => None,
                        }
                    })
                    .collect();
                if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                    let list = field_names.join(", ");
                    return Some(format!("a record with fields {{{list}}} ({d})"));
                }
            }
            Shape::List => {
                if let Some(d) = uncovered(rest_cols, &specialize_nil(m), unknown) {
                    return Some(format!("an empty list ({d})"));
                }
                let mut cons_cols = vec![unknown.clone(), unknown.clone()];
                cons_cols.extend(rest_cols.iter().cloned());
                if let Some(d) = uncovered(&cons_cols, &specialize_cons(m), unknown) {
                    return Some(format!("a non-empty list ({d})"));
                }
            }
            Shape::Bool(b) => {
                let sub: Vec<CoverRow> = m
                    .iter()
                    .filter_map(|row| {
                        let (head, tail) = row.0.split_first()?;
                        match head {
                            CoverPat::Lit(Lit::Bool(v)) if *v == *b => Some(tail.to_vec()),
                            _ => None,
                        }
                    })
                    .map(CoverRow)
                    .collect();
                let label = if *b { "true" } else { "false" };
                if let Some(d) = uncovered(rest_cols, &sub, unknown) {
                    return Some(format!("{label} ({d})"));
                }
            }
            Shape::Typed(t) => {
                let mut sub_cols = vec![unknown.clone()];
                sub_cols.extend(rest_cols.iter().cloned());
                let sub: Vec<CoverRow> = m
                    .iter()
                    .filter_map(|row| {
                        let (head, tail) = row.0.split_first()?;
                        match head {
                            CoverPat::Typed(u) if cover_ty_same(u, t) => {
                                let mut cols = vec![CoverPat::CatchAll];
                                cols.extend(tail.iter().cloned());
                                Some(CoverRow(cols))
                            }
                            _ => None,
                        }
                    })
                    .collect();
                if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                    return Some(format!("case (v : {t}) ({d})"));
                }
            }
        }
    }
    // Closed world over observed shapes: the scrutinee type is undetermined
    // at check time, so completeness is judged against the shapes the arms
    // themselves admit. With no enumerable shape present at all (bare
    // non-bool literals only), some other value remains uncovered.
    if saw_shape {
        None
    } else {
        Some(format!(
            "any other value (of {})",
            cover_describe_ty(unknown)
        ))
    }
}

fn uncovered(cols: &[Type], m: &[CoverRow], unknown: &Type) -> Option<String> {
    if m.is_empty() {
        return Some(match cols.first() {
            Some(ty) => cover_describe_ty(ty),
            None => "case".into(),
        });
    }
    let (head_ty, rest_cols) = cols.split_first()?;
    match head_ty {
        // Finite signatures: enumerate the cases.
        Type::Sum(sum) => {
            for alt in &sum.alts {
                match alt {
                    TypeAlt::Ctor { name, payload } => {
                        // Unit payloads are nullary constructors: no value
                        // column.
                        let payload_col = match payload {
                            Type::Con(Con::Unit) => None,
                            other => Some(other),
                        };
                        let sub = specialize_ctor(name, payload_col, head_ty, m);
                        let mut sub_cols: Vec<Type> =
                            payload_col.map(|t| vec![t.clone()]).unwrap_or_default();
                        sub_cols.extend(rest_cols.iter().cloned());
                        if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                            return Some(format!("constructor '{name}' ({d})"));
                        }
                    }
                    TypeAlt::Bare(t) => {
                        let sub = specialize_typed(t, head_ty, m);
                        let mut sub_cols = vec![t.clone()];
                        sub_cols.extend(rest_cols.iter().cloned());
                        if let Some(d) = uncovered(&sub_cols, &sub, unknown) {
                            return Some(format!("case (v : {t}) ({d})"));
                        }
                    }
                }
            }
            None
        }
        Type::Con(Con::Bool) => {
            for (b, label) in [(true, "true"), (false, "false")] {
                let sub = specialize_bool(b, m);
                if let Some(d) = uncovered(rest_cols, &sub, unknown) {
                    return Some(format!("{label} ({d})"));
                }
            }
            None
        }
        Type::List(elem) => {
            // A row whose head irrefutably covers the list (catch-all or
            // `[...r]`) dominates the column: only its tail matters.
            // Without this shortcut the cons case re-expands a catch-all
            // tail list forever.
            let dominant = specialize_irrefutable(head_ty, m);
            if !dominant.is_empty() {
                return uncovered(rest_cols, &dominant, unknown);
            }
            if let Some(d) = uncovered(rest_cols, &specialize_nil(m), unknown) {
                return Some(format!("an empty list ({d})"));
            }
            let mut cons_cols = vec![(**elem).clone(), head_ty.clone()];
            cons_cols.extend(rest_cols.iter().cloned());
            if let Some(d) = uncovered(&cons_cols, &specialize_cons(m), unknown) {
                return Some(format!("a non-empty list ({d})"));
            }
            None
        }
        // Products: expand into columns and recurse.
        Type::Tuple(tys) => {
            let mut expanded = tys.to_vec();
            expanded.extend(rest_cols.iter().cloned());
            uncovered(&expanded, &expand_tuple(tys, m), unknown)
        }
        Type::Record(rec) => {
            let mut expanded: Vec<Type> = rec.fields.iter().map(|(_, t)| t.clone()).collect();
            expanded.extend(rest_cols.iter().cloned());
            uncovered(&expanded, &expand_record(&rec.fields, m), unknown)
        }
        // Undetermined or infinite columns: irrefutable rows cover
        // everything; otherwise analyze the shapes the arms observe.
        _ => {
            let sub = specialize_irrefutable(head_ty, m);
            if sub.is_empty() {
                return missing_unknown(m, rest_cols, unknown);
            }
            uncovered(rest_cols, &sub, unknown)
        }
    }
}
