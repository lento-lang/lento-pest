// Partitioning a function group's clauses into specializations.
//
// For each `FunctionGroup`:
//
//   1. Every clause's principal type scheme is inferred (see `infer`).
//   2. Schemes are canonicalized by alpha-renaming quantified variables.
//   3. Clauses land in the same specialization when their schemes are
//      *compatible*: they admit one shared principal scheme (a common
//      generalization that both refine). Clauses whose annotations impose
//      genuinely different nominal domains form different specializations.
//   4. Different arity normally forms different specializations.
//   5. `a -> Ast` and `bytes -> Ast` are NEVER merged merely because they
//      unify: one is a deliberate strict specialization of the other.
//   6. Value-shape variants that refine the SAME type stay together: `[]`
//      and `[x, ...xs]` both refine `[a]`, so they share one specialization.
//
// The result is an `OverloadSet` of `Specialization`s, each with one
// principal scheme and the clauses (in source order) that implement it.

use std::collections::BTreeMap;
use std::fmt;

use crate::infer::{infer_function_group, InferCtx};
use crate::semantics::FunctionGroup;
use crate::types::{
    alpha_equiv, canonicalize, MonoType, TypeEnv, TypeScheme, TypeVarSupply,
};

/// One clause assigned to a specialization, with its inferred type.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecializedClause {
    /// The clause's own inferred type (ungeneralized, resolved).
    pub ty: MonoType,
    /// The clause's parameter patterns (value dispatch), in source order.
    pub patterns: Vec<crate::ast::Pattern>,
    /// Statement index of the source clause, for diagnostics.
    pub source_index: usize,
    /// The declared type restriction induced by annotations, if any: the
    /// sequence of per-parameter annotated domains. `None` when the clause is
    /// unannotated. Partitioning compares these SEMANTICALLY — two clauses
    /// with the same annotated domains (`(x : int) 0` and `(x : int) n`) share
    /// a specialization, while a redundant generic annotation (`(x : a)`)
    /// induces no restriction and merges with the unannotated generic.
    pub declared_domain: Vec<Option<MonoType>>,
}

/// One specialization: clauses sharing a single principal callable scheme.
#[derive(Debug, Clone, PartialEq)]
pub struct Specialization {
    /// Stable identity within the overload set (its index).
    pub id: usize,
    /// The principal scheme every clause in this specialization refines.
    pub scheme: TypeScheme,
    /// The declared type restriction shared by every clause in this
    /// specialization (one annotated domain per parameter), if any. This is
    /// the semantic specialization boundary: clauses with DIFFERENT declared
    /// restrictions form different specializations, and a clause with a
    /// concrete declared restriction never merges with the unannotated
    /// generic.
    pub declared_domain: Vec<Option<MonoType>>,
    /// Clauses in source (pattern-dispatch) order.
    pub clauses: Vec<SpecializedClause>,
}

/// All specializations of one function name.
#[derive(Debug, Clone, PartialEq)]
pub struct OverloadSet {
    pub name: String,
    pub specializations: Vec<Specialization>,
}

/// A clause whose scheme is incompatible with every other clause in the
/// group is fine (it is its own specialization). Partitioning only fails when
/// two clauses in the SAME tentative specialization cannot share a principal
/// scheme — but that cannot happen by construction here, so partitioning is
/// total. Diagnostics about unreachable patterns / non-exhaustiveness live in
/// the pattern phase, not here.
#[derive(Debug, Clone, PartialEq)]
pub struct PartitionError {
    pub message: String,
}

impl fmt::Display for PartitionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for PartitionError {}

/// The arity of a curried function type: the number of leading `->`s.
fn arity(ty: &MonoType) -> usize {
    match ty {
        MonoType::Function(_, to) => 1 + arity(to),
        _ => 0,
    }
}

/// The least generalization (anti-unification) of two monotypes: the most
/// specific type that has BOTH as instances. Correlation is tracked so that
/// the SAME pair of variables collapses to one generalization variable
/// (preserving `a -> a` structure) while DISTINCT pairs stay distinct.
/// Returns `None` for genuinely incompatible nominal/structural domains.
fn least_generalization(
    a: &MonoType,
    b: &MonoType,
    map: &mut BTreeMap<(u32, u32), u32>,
    next: &mut u32,
) -> Option<MonoType> {
    match (a, b) {
        // Two variables: correlated by the ordered pair of their ids.
        (MonoType::Var(x), MonoType::Var(y)) => {
            let id = *map.entry((*x, *y)).or_insert_with(|| {
                let id = *next;
                *next += 1;
                id
            });
            Some(MonoType::Var(id))
        }
        // A variable vs a concrete type: the concrete side is a refinement of
        // the variable, so the generalization is a fresh variable. Correlated
        // on the variable's id so the same var stays one variable.
        (MonoType::Var(x), other) | (other, MonoType::Var(x)) => {
            let other_key = match other {
                MonoType::Var(v) => *v,
                _ => u32::MAX, // any non-var refines to a fresh var keyed by `x`
            };
            let id = *map.entry((*x, other_key)).or_insert_with(|| {
                let id = *next;
                *next += 1;
                id
            });
            Some(MonoType::Var(id))
        }
        (MonoType::Constructor(n1, a1), MonoType::Constructor(n2, a2)) => {
            if n1 != n2 || a1.len() != a2.len() {
                return None;
            }
            let mut args = Vec::with_capacity(a1.len());
            for (x, y) in a1.iter().zip(a2.iter()) {
                args.push(least_generalization(x, y, map, next)?);
            }
            Some(MonoType::Constructor(n1.clone(), args))
        }
        (MonoType::Function(f1, t1), MonoType::Function(f2, t2)) => Some(MonoType::Function(
            Box::new(least_generalization(f1, f2, map, next)?),
            Box::new(least_generalization(t1, t2, map, next)?),
        )),
        (MonoType::Tuple(x), MonoType::Tuple(y)) => {
            if x.len() != y.len() {
                return None;
            }
            let mut items = Vec::with_capacity(x.len());
            for (a, b) in x.iter().zip(y.iter()) {
                items.push(least_generalization(a, b, map, next)?);
            }
            Some(MonoType::Tuple(items))
        }
        (MonoType::List(x), MonoType::List(y)) => {
            Some(MonoType::List(Box::new(least_generalization(x, y, map, next)?)))
        }
        (MonoType::Ref(x), MonoType::Ref(y)) => {
            Some(MonoType::Ref(Box::new(least_generalization(x, y, map, next)?)))
        }
        (MonoType::Mut(x), MonoType::Mut(y)) => {
            Some(MonoType::Mut(Box::new(least_generalization(x, y, map, next)?)))
        }
        _ => None,
    }
}

/// Extract the declared type restriction induced by a clause's parameter
/// annotations: one `Option<MonoType>` per parameter. An annotation that
/// lowers to a bare variable (`(x : a)`) induces NO restriction (`None`) — it
/// is a redundant generic annotation, not a boundary.
fn declared_domain(clause: &crate::ast::FnDecl) -> Vec<Option<MonoType>> {
    clause
        .params
        .iter()
        .map(|p| {
            p.annotation.as_ref().and_then(|ann| {
                // A bare lowercase unknown name (e.g. `a`) is a type variable,
                // not a nominal restriction.
                if let crate::ast::Ty::Named { name, args } = ann {
                    if args.is_empty()
                        && name.chars().next().map(|c| c.is_lowercase()).unwrap_or(false)
                        && !is_known_type_constructor(name)
                    {
                        return None;
                    }
                }
                let lowered = crate::types::lower_ty(ann, &BTreeMap::new());
                // A bare type variable is not a restriction.
                match lowered {
                    MonoType::Var(_) => None,
                    other => Some(other),
                }
            })
        })
        .collect()
}

/// Is `name` a known type constructor (as opposed to a type variable)?
/// Lowercase unknown names are conventionally variables; the primitives are
/// constructors.
fn is_known_type_constructor(name: &str) -> bool {
    matches!(
        name,
        "int" | "float" | "str" | "bool" | "bytes" | "unit" | "char"
    )
}

/// Do two declared domains impose the same restriction? `None` (unrestricted)
/// and a domain equal up to alpha-renaming are compatible; a concrete
/// restriction is compatible only with the SAME concrete restriction.
fn domains_compatible(a: &[Option<MonoType>], b: &[Option<MonoType>]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b.iter()).all(|(x, y)| match (x, y) {
        (None, None) => true,
        // A restricted parameter is compatible only with the identical
        // restriction; restricted-vs-unrestricted is a specialization
        // boundary.
        (Some(d1), Some(d2)) => {
            let mut map = BTreeMap::new();
            let mut next = 10_000;
            // Same declared restriction: equal up to alpha-renaming of any
            // variables inside. Use least-generalization reflexively: d1 and
            // d2 must generalize to a type equal to both.
            match least_generalization(d1, d2, &mut map, &mut next) {
                Some(lg) => lg == *d1 && lg == *d2,
                None => false,
            }
        }
        _ => false,
    })
}

/// Do two clause schemes belong to the same specialization, given their
/// declared type restrictions?
///
///   - the declared domains must be compatible (same semantic restriction per
///     parameter) — a distinct declared restriction is a specialization
///     boundary, and a concrete restriction never merges with the unannotated
///     generic;
///   - alpha-equivalent schemes merge;
///   - value-shape variants (`[]` vs `[x, ...xs]`, or literal `0` vs var `n`)
///     with the same declared domain refine one type and merge;
///   - genuinely different nominal domains have no common generalization.
fn same_specialization(
    supply: &mut TypeVarSupply,
    a: &TypeScheme,
    a_domain: &[Option<MonoType>],
    b: &TypeScheme,
    b_domain: &[Option<MonoType>],
) -> bool {
    let _ = supply;
    // The semantic boundary: declared type restrictions must agree.
    if !domains_compatible(a_domain, b_domain) {
        return false;
    }
    if alpha_equiv(a, b) {
        return true;
    }
    // Same declared domain: merge iff the schemes admit one common principal
    // scheme (a least generalization exists — no incompatible nominal
    // domains). Value-shape variants unify structurally even when neither is
    // an HM-instance of the other.
    let mut map = BTreeMap::new();
    let mut next = 10_000;
    least_generalization(&a.body, &b.body, &mut map, &mut next).is_some()
}

/// Partition a function group's clauses into specializations.
///
/// Clauses are processed in source order; each joins the first
/// specialization whose scheme it is compatible with, else opens a new one.
/// Arity is part of family identity: clauses of different arity never share
/// a specialization.
pub fn partition(
    ctx: &mut InferCtx,
    group: &FunctionGroup,
    env: &TypeEnv,
) -> Result<OverloadSet, PartitionError> {
    let inferred = infer_function_group(ctx, group, env).map_err(|e| PartitionError {
        message: format!("type error in `{}`: {e}", group.name),
    })?;

    let mut specializations: Vec<Specialization> = Vec::new();

    for (i, clause_ty) in inferred.clause_types.iter().enumerate() {
        let clause_arity = arity(clause_ty);
        let domain = group
            .raw_clauses
            .get(i)
            .map(declared_domain)
            .unwrap_or_default();
        let scheme = canonicalize(&crate::types::generalize(env, clause_ty, vec![]));

        let mut placed = false;
        for spec in specializations.iter_mut() {
            if arity(&spec.scheme.body) != clause_arity {
                continue; // arity is part of family identity
            }
            let mut supply = TypeVarSupply::new();
            if same_specialization(&mut supply, &spec.scheme, &spec.declared_domain, &scheme, &domain) {
                spec.clauses.push(SpecializedClause {
                    ty: clause_ty.clone(),
                    patterns: inferred.clause_patterns[i].clone(),
                    source_index: group.source_indices.get(i).copied().unwrap_or(i),
                    declared_domain: domain.clone(),
                });
                placed = true;
                break;
            }
        }
        if !placed {
            let id = specializations.len();
            specializations.push(Specialization {
                id,
                scheme,
                declared_domain: domain.clone(),
                clauses: vec![SpecializedClause {
                    ty: clause_ty.clone(),
                    patterns: inferred.clause_patterns[i].clone(),
                    source_index: group.source_indices.get(i).copied().unwrap_or(i),
                    declared_domain: domain,
                }],
            });
        }
    }

    Ok(OverloadSet {
        name: group.name.clone(),
        specializations,
    })
}
