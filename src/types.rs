// Internal type representation for Hindley–Milner inference.
//
// The parser's `ast::Ty` is a *surface* syntax tree: it records what the
// programmer wrote, including the ambiguous `Ty::Named` (used both for real
// nominal types like `int` and for quantified variables like `a`). It is not
// suitable as an inference representation. This module defines the internal
// representation:
//
//   MonoType                     -- monomorphic types with explicit variables
//     Var(TypeVarId)             -- a unification/quantification variable
//     Constructor(TypeConstructorId, Vec<MonoType>)
//     Function(Box, Box)
//     Tuple(Vec<MonoType>)
//     List(Box<MonoType>)
//     Ref(Box<MonoType>) / Mut(Box<MonoType>)
//
//   TypeScheme { quantified, constraints, body }
//
// plus the required operations: fresh type variables, capture-avoiding
// substitution, the occurs check, unification, instantiation, generalization
// relative to an environment, and alpha-equivalence/canonicalization of
// schemes.
//
// An inferred type variable is always `MonoType::Var`, never `Ty::Named`.
// The old `ast::param_type` behavior (turning a parameter named `x` into the
// nominal type `x`) is gone from the semantic path: parameters get fresh
// `MonoType::Var`s from `TypeVarSupply`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ast::{Constraint, Ty};

/// Identity of a type variable. Fresh variables come from `TypeVarSupply`;
/// skolem constants are allocated from the same supply but marked rigid by
/// the context that creates them.
pub type TypeVarId = u32;

/// Identity of a named type constructor (`int`, `str`, a user `type` alias).
///
/// This is a name for now; it becomes a resolved interned id when the
//  type-declaration environment lands.
pub type TypeConstructorId = String;

/// Monomorphic types: the unification and inference representation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MonoType {
    /// A type variable (unification variable when mutable, quantified
    /// variable inside a scheme).
    Var(TypeVarId),
    /// An applied named type constructor: `int`, `bytes`, `Ast`, `Map k v`.
    Constructor(TypeConstructorId, Vec<MonoType>),
    /// A function type `from -> to` (right-associative at the surface).
    Function(Box<MonoType>, Box<MonoType>),
    /// `(a, b, ...)`. `Tuple(vec![])` is the unit type `()`.
    Tuple(Vec<MonoType>),
    /// `[a]`.
    List(Box<MonoType>),
    /// `ref T` — a shared borrow.
    Ref(Box<MonoType>),
    /// `mut T` — an exclusive mutable place.
    Mut(Box<MonoType>),
    /// Structural record type with an optional open row variable.
    Record {
        fields: Vec<(String, MonoType)>,
        rest: Option<TypeVarId>,
    },
    /// Nominal or inferred sum type with constructor and bare alternatives.
    Sum {
        name: String,
        args: Vec<MonoType>,
        alts: Vec<MonoSumAlt>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MonoSumAlt {
    Constructor { name: String, payload: Option<MonoType> },
    Bare(MonoType),
}

/// A type scheme: quantified variables with their constraints over a
/// monomorphic body.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    /// Quantified variables. Order is significant for canonicalization only.
    pub quantified: Vec<TypeVarId>,
    /// Constraints over the quantified variables (`Ord a`, `Show a`).
    pub constraints: Vec<SchemeConstraint>,
    pub body: MonoType,
}

/// A constraint in a scheme, with its type arguments in the internal
/// representation.
#[derive(Debug, Clone, PartialEq)]
pub struct SchemeConstraint {
    pub name: String,
    pub args: Vec<MonoType>,
}

impl TypeScheme {
    /// The trivial scheme: no quantification, no constraints.
    pub fn mono(body: MonoType) -> Self {
        TypeScheme {
            quantified: Vec::new(),
            constraints: Vec::new(),
            body,
        }
    }
}

// --------------------------------------------------------------------------
// Fresh type variables
// --------------------------------------------------------------------------

/// Allocates fresh type variables. One supply per inference run keeps ids
/// deterministic for tests.
#[derive(Debug, Default, Clone)]
pub struct TypeVarSupply {
    next: TypeVarId,
}

impl TypeVarSupply {
    pub fn new() -> Self {
        TypeVarSupply { next: 0 }
    }

    /// A fresh unification variable.
    pub fn fresh(&mut self) -> MonoType {
        let id = self.next;
        self.next += 1;
        MonoType::Var(id)
    }

    /// A fresh variable id (for skolems or quantified variables).
    pub fn fresh_id(&mut self) -> TypeVarId {
        let id = self.next;
        self.next += 1;
        id
    }
}

// --------------------------------------------------------------------------
// Free variables
// --------------------------------------------------------------------------

impl MonoType {
    /// Every variable occurring in the type, in first-occurrence order.
    pub fn free_vars(&self) -> Vec<TypeVarId> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        self.collect_free_vars(&mut seen, &mut out);
        out
    }

    fn collect_free_vars(&self, seen: &mut BTreeSet<TypeVarId>, out: &mut Vec<TypeVarId>) {
        match self {
            MonoType::Var(id) => {
                if seen.insert(*id) {
                    out.push(*id);
                }
            }
            MonoType::Constructor(_, args) | MonoType::Tuple(args) => {
                for a in args {
                    a.collect_free_vars(seen, out);
                }
            }
            MonoType::Function(from, to) => {
                from.collect_free_vars(seen, out);
                to.collect_free_vars(seen, out);
            }
            MonoType::List(inner) | MonoType::Ref(inner) | MonoType::Mut(inner) => {
                inner.collect_free_vars(seen, out);
            }
            MonoType::Record { fields, rest } => {
                for (_, field) in fields {
                    field.collect_free_vars(seen, out);
                }
                if let Some(rest) = rest {
                    if seen.insert(*rest) {
                        out.push(*rest);
                    }
                }
            }
            MonoType::Sum { args, alts, .. } => {
                for arg in args {
                    arg.collect_free_vars(seen, out);
                }
                for alt in alts {
                    match alt {
                        MonoSumAlt::Constructor { payload, .. } => {
                            if let Some(payload) = payload {
                                payload.collect_free_vars(seen, out);
                            }
                        }
                        MonoSumAlt::Bare(ty) => ty.collect_free_vars(seen, out),
                    }
                }
            }
        }
    }
}

impl TypeScheme {
    /// Variables free in the body or constraints but not quantified.
    pub fn free_vars(&self) -> Vec<TypeVarId> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        self.body.collect_free_vars(&mut seen, &mut out);
        for c in &self.constraints {
            for a in &c.args {
                a.collect_free_vars(&mut seen, &mut out);
            }
        }
        out.retain(|v| !self.quantified.contains(v));
        out
    }
}

/// A typing environment: term names mapped to their schemes. Used as the
/// reference for generalization (`generalize(env, ty)` quantifies the
/// variables free in `ty` but not free in `env`).
pub type TypeEnv = BTreeMap<String, TypeScheme>;

fn env_free_vars(env: &TypeEnv) -> BTreeSet<TypeVarId> {
    let mut out = BTreeSet::new();
    for scheme in env.values() {
        out.extend(scheme.free_vars());
        out.extend(scheme.quantified.iter().copied());
    }
    out
}

// --------------------------------------------------------------------------
// Capture-avoiding substitution
// --------------------------------------------------------------------------

/// A substitution from type variables to monotypes.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct Substitution {
    map: BTreeMap<TypeVarId, MonoType>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution::default()
    }

    /// The singleton substitution `id |-> ty`.
    pub fn singleton(id: TypeVarId, ty: MonoType) -> Self {
        let mut map = BTreeMap::new();
        map.insert(id, ty);
        Substitution { map }
    }

    pub fn get(&self, id: TypeVarId) -> Option<&MonoType> {
        self.map.get(&id)
    }

    pub fn insert(&mut self, id: TypeVarId, ty: MonoType) {
        self.map.insert(id, ty);
    }

    /// Apply the substitution to a type. Application is capture-avoiding:
    /// a mapping `v |-> Var(w)` is applied only when `w` is not itself mapped
    /// (i.e. it is final), so variable-to-variable renamings can never form a
    /// cycle through a third variable. This keeps alpha-renaming idempotent
    /// while still chasing solved unification bindings.
    pub fn apply(&self, ty: &MonoType) -> MonoType {
        match ty {
            MonoType::Var(id) => match self.map.get(id) {
                Some(MonoType::Var(w)) if self.map.contains_key(w) => {
                    self.apply(&MonoType::Var(*w))
                }
                Some(t) => t.clone(),
                None => ty.clone(),
            },
            MonoType::Constructor(name, args) => MonoType::Constructor(
                name.clone(),
                args.iter().map(|a| self.apply(a)).collect(),
            ),
            MonoType::Function(from, to) => MonoType::Function(
                Box::new(self.apply(from)),
                Box::new(self.apply(to)),
            ),
            MonoType::Tuple(items) => {
                MonoType::Tuple(items.iter().map(|t| self.apply(t)).collect())
            }
            MonoType::List(inner) => MonoType::List(Box::new(self.apply(inner))),
            MonoType::Ref(inner) => MonoType::Ref(Box::new(self.apply(inner))),
            MonoType::Mut(inner) => MonoType::Mut(Box::new(self.apply(inner))),
            MonoType::Record { fields, rest } => MonoType::Record {
                fields: fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.apply(ty)))
                    .collect(),
                rest: *rest,
            },
            MonoType::Sum { name, args, alts } => MonoType::Sum {
                name: name.clone(),
                args: args.iter().map(|ty| self.apply(ty)).collect(),
                alts: alts
                    .iter()
                    .map(|alt| match alt {
                        MonoSumAlt::Constructor { name, payload } => MonoSumAlt::Constructor {
                            name: name.clone(),
                            payload: payload.as_ref().map(|ty| self.apply(ty)),
                        },
                        MonoSumAlt::Bare(ty) => MonoSumAlt::Bare(self.apply(ty)),
                    })
                    .collect(),
            },
        }
    }

    /// Apply the substitution under a scheme's binder. Bound variables are
    /// removed from the substitution first, so application is
    /// capture-avoiding: quantified variables are never instantiated by
    /// substitution.
    pub fn apply_scheme(&self, scheme: &TypeScheme) -> TypeScheme {
        let mut restricted = self.clone();
        for q in &scheme.quantified {
            restricted.map.remove(q);
        }
        TypeScheme {
            quantified: scheme.quantified.clone(),
            constraints: scheme
                .constraints
                .iter()
                .map(|c| SchemeConstraint {
                    name: c.name.clone(),
                    args: c.args.iter().map(|a| restricted.apply(a)).collect(),
                })
                .collect(),
            body: restricted.apply(&scheme.body),
        }
    }

    /// Compose `self` after `other`: `self.compose(other)(t) =
    /// self(other(t))`.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut map: BTreeMap<TypeVarId, MonoType> = other
            .map
            .iter()
            .map(|(k, v)| (*k, self.apply(v)))
            .collect();
        for (k, v) in &self.map {
            map.insert(*k, v.clone());
        }
        Substitution { map }
    }
}

// --------------------------------------------------------------------------
// Occurs check and unification
// --------------------------------------------------------------------------

/// A unification failure.
#[derive(Debug, Clone, PartialEq)]
pub enum UnifyError {
    /// `v` occurs in `ty`: unifying them would build an infinite type.
    Occurs { var: TypeVarId, ty: MonoType },
    /// Rigid constructors disagree (`int` vs `str`, arity mismatch, ...).
    Mismatch { left: MonoType, right: MonoType },
}

impl fmt::Display for UnifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnifyError::Occurs { var, ty } => {
                write!(f, "occurs check failed: ?{var} occurs in {ty:?}")
            }
            UnifyError::Mismatch { left, right } => {
                write!(f, "type mismatch: {left:?} vs {right:?}")
            }
        }
    }
}

impl std::error::Error for UnifyError {}

/// The occurs check: does `var` occur in `ty` (after applying `subst`)?
fn occurs(subst: &Substitution, var: TypeVarId, ty: &MonoType) -> bool {
    subst.apply(ty).free_vars().contains(&var)
}

fn bind_var(subst: &mut Substitution, var: TypeVarId, ty: &MonoType) -> Result<(), UnifyError> {
    let ty = subst.apply(ty);
    if ty == MonoType::Var(var) {
        return Ok(());
    }
    if occurs(subst, var, &ty) {
        return Err(UnifyError::Occurs { var, ty });
    }
    subst.insert(var, ty);
    Ok(())
}

/// Unify two monotypes, extending `subst` on success.
pub fn unify(
    subst: &mut Substitution,
    left: &MonoType,
    right: &MonoType,
) -> Result<(), UnifyError> {
    let left = subst.apply(left);
    let right = subst.apply(right);
    match (&left, &right) {
        (MonoType::Var(a), MonoType::Var(b)) if a == b => Ok(()),
        (MonoType::Var(v), _) => bind_var(subst, *v, &right),
        (_, MonoType::Var(v)) => bind_var(subst, *v, &left),
        (MonoType::Constructor(n1, a1), MonoType::Constructor(n2, a2)) => {
            if n1 != n2 || a1.len() != a2.len() {
                return Err(UnifyError::Mismatch { left, right });
            }
            for (x, y) in a1.clone().iter().zip(a2.clone().iter()) {
                unify(subst, x, y)?;
            }
            Ok(())
        }
        (MonoType::Function(f1, t1), MonoType::Function(f2, t2)) => {
            unify(subst, &f1.clone(), &f2.clone())?;
            unify(subst, &t1.clone(), &t2.clone())
        }
        (MonoType::Tuple(a), MonoType::Tuple(b)) => {
            if a.len() != b.len() {
                return Err(UnifyError::Mismatch { left, right });
            }
            for (x, y) in a.clone().iter().zip(b.clone().iter()) {
                unify(subst, x, y)?;
            }
            Ok(())
        }
        (MonoType::List(a), MonoType::List(b))
        | (MonoType::Ref(a), MonoType::Ref(b))
        | (MonoType::Mut(a), MonoType::Mut(b)) => unify(subst, &a.clone(), &b.clone()),
        (MonoType::Mut(inner), other) => unify(subst, inner, &other),
        (other, MonoType::Mut(inner)) => unify(subst, &other, inner),
        (
            MonoType::Record {
                fields: left_fields,
                rest: left_rest,
            },
            MonoType::Record {
                fields: right_fields,
                rest: right_rest,
            },
        ) => unify_records(subst, left_fields, *left_rest, right_fields, *right_rest),
        (
            MonoType::Sum {
                name: left_name,
                args: left_args,
                alts: left_alts,
            },
            MonoType::Sum {
                name: right_name,
                args: right_args,
                alts: right_alts,
            },
        ) => {
            if left_name != right_name && left_alts != right_alts {
                return Err(UnifyError::Mismatch { left, right });
            }
            for (left, right) in left_args.iter().zip(right_args) {
                unify(subst, left, right)?;
            }
            Ok(())
        }
        (MonoType::Sum { alts, .. }, other) => unify_sum_member(subst, alts, &other),
        (other, MonoType::Sum { alts, .. }) => unify_sum_member(subst, alts, &other),
        _ => Err(UnifyError::Mismatch { left, right }),
    }
}

fn unify_sum_member(
    subst: &mut Substitution,
    alts: &[MonoSumAlt],
    other: &MonoType,
) -> Result<(), UnifyError> {
    for alt in alts {
        let MonoSumAlt::Bare(candidate) = alt else {
            continue;
        };
        let snapshot = subst.clone();
        if unify(subst, other, candidate).is_ok() {
            return Ok(());
        }
        *subst = snapshot;
    }
    Err(UnifyError::Mismatch {
        left: other.clone(),
        right: MonoType::Sum {
            name: "<sum>".to_string(),
            args: Vec::new(),
            alts: alts.to_vec(),
        },
    })
}

fn unify_records(
    subst: &mut Substitution,
    left_fields: &[(String, MonoType)],
    left_rest: Option<TypeVarId>,
    right_fields: &[(String, MonoType)],
    right_rest: Option<TypeVarId>,
) -> Result<(), UnifyError> {
    let left_names = left_fields
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<BTreeSet<_>>();
    let right_names = right_fields
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<BTreeSet<_>>();
    for (name, left) in left_fields {
        if let Some((_, right)) = right_fields.iter().find(|(other, _)| other == name) {
            unify(subst, left, right)?;
        }
    }
    let only_left = left_fields
        .iter()
        .filter(|(name, _)| !right_names.contains(name.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let only_right = right_fields
        .iter()
        .filter(|(name, _)| !left_names.contains(name.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    match (only_left.is_empty(), only_right.is_empty()) {
        (true, true) => unify_rows(subst, left_rest, right_rest),
        (true, false) => match left_rest {
            Some(rest) => bind_var(
                subst,
                rest,
                &MonoType::Record {
                    fields: only_right,
                    rest: right_rest,
                },
            ),
            None => Err(record_mismatch(left_fields, left_rest, right_fields, right_rest)),
        },
        (false, true) => match right_rest {
            Some(rest) => bind_var(
                subst,
                rest,
                &MonoType::Record {
                    fields: only_left,
                    rest: left_rest,
                },
            ),
            None => Err(record_mismatch(left_fields, left_rest, right_fields, right_rest)),
        },
        (false, false) => {
            let left_rest = left_rest
                .ok_or_else(|| record_mismatch(left_fields, left_rest, right_fields, right_rest))?;
            let right_rest = right_rest
                .ok_or_else(|| record_mismatch(left_fields, Some(left_rest), right_fields, right_rest))?;
            let fresh = subst.map.keys().copied().max().unwrap_or(10_000_000) + 1;
            bind_var(
                subst,
                left_rest,
                &MonoType::Record {
                    fields: only_right,
                    rest: Some(fresh),
                },
            )?;
            bind_var(
                subst,
                right_rest,
                &MonoType::Record {
                    fields: only_left,
                    rest: Some(fresh),
                },
            )
        }
    }
}

fn unify_rows(
    subst: &mut Substitution,
    left: Option<TypeVarId>,
    right: Option<TypeVarId>,
) -> Result<(), UnifyError> {
    match (left, right) {
        (None, None) => Ok(()),
        (Some(left), Some(right)) if left == right => Ok(()),
        (Some(left), Some(right)) => bind_var(
            subst,
            right,
            &MonoType::Record {
                fields: Vec::new(),
                rest: Some(left),
            },
        ),
        (Some(row), None) | (None, Some(row)) => bind_var(
            subst,
            row,
            &MonoType::Record {
                fields: Vec::new(),
                rest: None,
            },
        ),
    }
}

fn record_mismatch(
    left_fields: &[(String, MonoType)],
    left_rest: Option<TypeVarId>,
    right_fields: &[(String, MonoType)],
    right_rest: Option<TypeVarId>,
) -> UnifyError {
    UnifyError::Mismatch {
        left: MonoType::Record {
            fields: left_fields.to_vec(),
            rest: left_rest,
        },
        right: MonoType::Record {
            fields: right_fields.to_vec(),
            rest: right_rest,
        },
    }
}

// --------------------------------------------------------------------------
// Instantiation and generalization
// --------------------------------------------------------------------------

/// Instantiate a scheme: replace each quantified variable with a fresh
/// variable from `supply`. Constraints are instantiated alongside the body.
/// Uses a direct (non-chasing) renaming so a fresh id that happens to collide
/// with a quantifier id can never be re-mapped.
pub fn instantiate(
    supply: &mut TypeVarSupply,
    scheme: &TypeScheme,
) -> (MonoType, Vec<SchemeConstraint>) {
    let mut renaming = BTreeMap::new();
    for q in &scheme.quantified {
        renaming.insert(*q, supply.fresh_id());
    }
    let body = rename_vars(&scheme.body, &renaming);
    let constraints = scheme
        .constraints
        .iter()
        .map(|c| SchemeConstraint {
            name: c.name.clone(),
            args: c.args.iter().map(|a| rename_vars(a, &renaming)).collect(),
        })
        .collect();
    (body, constraints)
}

/// Generalize a monotype relative to an environment: quantify every variable
/// free in `ty` but not free in `env`. Constraints attached to the
/// generalized variables travel with the scheme.
pub fn generalize(
    env: &TypeEnv,
    ty: &MonoType,
    constraints: Vec<SchemeConstraint>,
) -> TypeScheme {
    let env_vars = env_free_vars(env);
    let quantified: Vec<TypeVarId> = {
        let mut q: Vec<TypeVarId> = ty
            .free_vars()
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();
        // Also quantify variables that occur only in the constraints.
        let mut seen: BTreeSet<TypeVarId> = q.iter().copied().collect();
        for c in &constraints {
            for a in &c.args {
                for v in a.free_vars() {
                    if !env_vars.contains(&v) && seen.insert(v) {
                        q.push(v);
                    }
                }
            }
        }
        q
    };
    TypeScheme {
        quantified,
        constraints,
        body: ty.clone(),
    }
}

// --------------------------------------------------------------------------
// Alpha-equivalence and canonicalization
// --------------------------------------------------------------------------

/// Rename a scheme's quantified variables to the canonical sequence
/// `0, 1, 2, ...` ordered by first occurrence in the body. Two schemes are
/// alpha-equivalent iff their canonicalizations are equal.
pub fn canonicalize(scheme: &TypeScheme) -> TypeScheme {
    // Map each quantified variable to its canonical index, ordered by first
    // occurrence in the body (then constraint-only variables, in the order
    // they appear).
    let mut order: Vec<TypeVarId> = Vec::new();
    for v in scheme.body.free_vars() {
        if scheme.quantified.contains(&v) && !order.contains(&v) {
            order.push(v);
        }
    }
    for c in &scheme.constraints {
        for a in &c.args {
            for v in a.free_vars() {
                if scheme.quantified.contains(&v) && !order.contains(&v) {
                    order.push(v);
                }
            }
        }
    }
    // Quantified variables that never occur anywhere keep their relative
    // order at the end.
    for q in &scheme.quantified {
        if !order.contains(q) {
            order.push(*q);
        }
    }

    // Build the renaming directly: original variable id -> canonical index.
    // Canonical indices may collide with original ids, so apply it with a
    // dedicated non-chasing renaming (not `Substitution::apply`, which would
    // follow chains and could cycle through a shared id).
    let renaming: BTreeMap<TypeVarId, TypeVarId> = order
        .iter()
        .enumerate()
        .map(|(canonical, original)| (*original, canonical as TypeVarId))
        .collect();
    let rename = |ty: &MonoType| rename_vars(ty, &renaming);
    TypeScheme {
        quantified: (0..order.len() as TypeVarId).collect(),
        constraints: scheme
            .constraints
            .iter()
            .map(|c| SchemeConstraint {
                name: c.name.clone(),
                args: c.args.iter().map(|a| rename(a)).collect(),
            })
            .collect(),
        body: rename(&scheme.body),
    }
}

/// Rename variables per a direct id->id map, without chasing: each variable
/// is replaced at most once, so the map may freely reuse ids.
fn rename_vars(ty: &MonoType, renaming: &BTreeMap<TypeVarId, TypeVarId>) -> MonoType {
    match ty {
        MonoType::Var(id) => MonoType::Var(renaming.get(id).copied().unwrap_or(*id)),
        MonoType::Constructor(name, args) => MonoType::Constructor(
            name.clone(),
            args.iter().map(|a| rename_vars(a, renaming)).collect(),
        ),
        MonoType::Function(from, to) => MonoType::Function(
            Box::new(rename_vars(from, renaming)),
            Box::new(rename_vars(to, renaming)),
        ),
        MonoType::Tuple(items) => {
            MonoType::Tuple(items.iter().map(|t| rename_vars(t, renaming)).collect())
        }
        MonoType::List(inner) => MonoType::List(Box::new(rename_vars(inner, renaming))),
        MonoType::Ref(inner) => MonoType::Ref(Box::new(rename_vars(inner, renaming))),
        MonoType::Mut(inner) => MonoType::Mut(Box::new(rename_vars(inner, renaming))),
        MonoType::Record { fields, rest } => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| (name.clone(), rename_vars(ty, renaming)))
                .collect(),
            rest: rest.map(|id| renaming.get(&id).copied().unwrap_or(id)),
        },
        MonoType::Sum { name, args, alts } => MonoType::Sum {
            name: name.clone(),
            args: args.iter().map(|ty| rename_vars(ty, renaming)).collect(),
            alts: alts
                .iter()
                .map(|alt| match alt {
                    MonoSumAlt::Constructor { name, payload } => MonoSumAlt::Constructor {
                        name: name.clone(),
                        payload: payload.as_ref().map(|ty| rename_vars(ty, renaming)),
                    },
                    MonoSumAlt::Bare(ty) => MonoSumAlt::Bare(rename_vars(ty, renaming)),
                })
                .collect(),
        },
    }
}

/// Alpha-equivalence: same canonical form.
pub fn alpha_equiv(a: &TypeScheme, b: &TypeScheme) -> bool {
    canonicalize(a) == canonicalize(b)
}

// --------------------------------------------------------------------------
// Surface-type lowering
// --------------------------------------------------------------------------

/// Lower a surface `ast::Ty` into a `MonoType` under a binder environment.
///
/// `binders` maps quantified variable names (from `all a b. ...`) to their
/// `MonoType::Var`s. A `Ty::Named` whose name is a binder becomes that
/// variable; any other `Ty::Named` is a real nominal type constructor. This
/// is the *only* place a name becomes a variable: nothing in the semantic
/// path ever turns a bare parameter name into a nominal type.
pub fn lower_ty(ty: &Ty, binders: &BTreeMap<String, MonoType>) -> MonoType {
    match ty {
        Ty::Named { name, args } => {
            if args.is_empty() {
                if let Some(var) = binders.get(name) {
                    return var.clone();
                }
                if name == "unit" {
                    return MonoType::Tuple(Vec::new());
                }
                if let Some(primitive) = match name.as_str() {
                    "Int" => Some("int"),
                    "Float" => Some("float"),
                    "String" => Some("str"),
                    "Bool" => Some("bool"),
                    "Unit" => Some("unit"),
                    "usize" => Some("int"),
                    _ => None,
                } {
                    return if primitive == "unit" {
                        MonoType::Tuple(Vec::new())
                    } else {
                        MonoType::Constructor(primitive.to_string(), Vec::new())
                    };
                }
            }
            MonoType::Constructor(
                name.clone(),
                args.iter().map(|a| lower_ty(a, binders)).collect(),
            )
        }
        Ty::Tuple(items) => MonoType::Tuple(items.iter().map(|t| lower_ty(t, binders)).collect()),
        Ty::List(inner) => MonoType::List(Box::new(lower_ty(inner, binders))),
        Ty::Arrow { from, to } => MonoType::Function(
            Box::new(lower_ty(from, binders)),
            Box::new(lower_ty(to, binders)),
        ),
        Ty::Ref(inner) => MonoType::Ref(Box::new(lower_ty(inner, binders))),
        Ty::Mut(inner) => MonoType::Mut(Box::new(lower_ty(inner, binders))),
        // `name: T` named binders are transparent at the type level.
        Ty::NamedBinder { ty, .. } => lower_ty(ty, binders),
        Ty::Sum(alts) => MonoType::Constructor(
            "sum".to_string(),
            alts.iter()
                .map(|alt| match alt {
                    crate::ast::SumAlt::Ctor { name, payload } => MonoType::Constructor(
                        name.clone(),
                        payload
                            .as_ref()
                            .map(|ty| vec![lower_ty(ty, binders)])
                            .unwrap_or_default(),
                    ),
                    crate::ast::SumAlt::Bare(ty) => lower_ty(ty, binders),
                })
                .collect(),
        ),
        Ty::RecordType(fields) => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| (name.clone(), lower_ty(ty, binders)))
                .collect(),
            rest: None,
        },
    }
}

/// Lower a surface constraint's type arguments.
pub fn lower_constraint(c: &Constraint, binders: &BTreeMap<String, MonoType>) -> SchemeConstraint {
    SchemeConstraint {
        name: c.name.clone(),
        args: c.args.iter().map(|a| lower_ty(a, binders)).collect(),
    }
}

// --------------------------------------------------------------------------
// Skolemization and subsumption (used by spec checking / overload
// resolution's specificity comparison)
// --------------------------------------------------------------------------

/// Instantiate a scheme using explicit fresh-variable ids, returning the body
/// and the quantifier->fresh-id mapping (no `Substitution`, so no id can
/// collide with an existing key and trigger chasing).
fn instantiate_fresh(
    supply: &mut TypeVarSupply,
    scheme: &TypeScheme,
) -> (MonoType, BTreeMap<TypeVarId, TypeVarId>) {
    let mut renaming = BTreeMap::new();
    for q in &scheme.quantified {
        renaming.insert(*q, supply.fresh_id());
    }
    (rename_vars(&scheme.body, &renaming), renaming)
}

/// Skolemize a scheme: replace quantified variables with fresh *rigid* ids.
pub fn skolemize(supply: &mut TypeVarSupply, scheme: &TypeScheme) -> (MonoType, Vec<TypeVarId>) {
    let (body, renaming) = instantiate_fresh(supply, scheme);
    let skolems = scheme
        .quantified
        .iter()
        .map(|q| renaming[q])
        .collect();
    (body, skolems)
}

/// Is `instance` an instance of `general`? i.e. is there a substitution for
/// `general`'s quantified variables that yields exactly `instance`'s shape.
///
/// This is one-way matching, not full unification: `general`'s quantified
/// variables may be bound, but `instance`'s variables (skolemized to rigid
/// constants) may only match themselves. Matching propagates a substitution
/// for `general`'s variables left-to-right.
pub fn is_instance(supply: &mut TypeVarSupply, general: &TypeScheme, instance: &TypeScheme) -> bool {
    // Skolemize `instance`: its variables become rigid constants.
    let (instance_body, _) = skolemize(supply, instance);
    // Instantiate `general`: its quantified variables become matchable.
    let (general_body, renaming) = instantiate_fresh(supply, general);
    // The matchable variables are exactly the fresh ids general mapped to.
    let matchable: BTreeSet<TypeVarId> = renaming.values().copied().collect();
    let mut subst = Substitution::new();
    matches(&general_body, &instance_body, &matchable, &mut subst)
}

/// Is `instance` a *permissive* instance of `general`: every use allowed by
/// `general` is allowed by `instance`? Unlike `is_instance`, `instance`'s own
/// quantified variables are flexible (a MORE-general implementation may
/// satisfy a more-specific contract: the polymorphic identity satisfies
/// `int -> int`).
///
/// Prefer `implementation_covers_spec` for spec satisfaction: it is skolem-
/// based and constraint-aware. This unification-based check is retained for
/// comparability probes where both sides are flexible.
pub fn is_permissive_instance(
    supply: &mut TypeVarSupply,
    general: &TypeScheme,
    instance: &TypeScheme,
) -> bool {
    // Both sides instantiated with fresh flexible variables; unify.
    let (instance_body, _) = instantiate(supply, instance);
    let (general_body, _) = instantiate(supply, general);
    let mut subst = Substitution::new();
    unify(&mut subst, &general_body, &instance_body).is_ok()
}

/// One-way matching: bind `left`'s matchable variables (via `subst`) so that
/// `left` becomes structurally equal to the rigid `right`. Only variables in
/// `matchable` may be bound; all other variables are rigid constants and are
/// never bound. Lookup is non-chasing: a bound variable maps directly to its
/// (rigid) image, which never contains a matchable variable.
fn matches(
    left: &MonoType,
    right: &MonoType,
    matchable: &BTreeSet<TypeVarId>,
    subst: &mut Substitution,
) -> bool {
    match (left, right) {
        (MonoType::Var(a), _) if matchable.contains(a) => match subst.get(*a) {
            Some(bound) => bound.clone() == *right,
            None => {
                subst.insert(*a, right.clone());
                true
            }
        },
        (MonoType::Var(a), MonoType::Var(b)) => a == b,
        (MonoType::Constructor(n1, a1), MonoType::Constructor(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .clone()
                    .iter()
                    .zip(a2.clone().iter())
                    .all(|(x, y)| matches(x, y, matchable, subst))
        }
        (MonoType::Function(f1, t1), MonoType::Function(f2, t2)) => {
            let (f1, t1, f2, t2) = (f1.clone(), t1.clone(), f2.clone(), t2.clone());
            matches(&f1, &f2, matchable, subst) && matches(&t1, &t2, matchable, subst)
        }
        (MonoType::Tuple(a), MonoType::Tuple(b)) => {
            a.len() == b.len()
                && a.clone()
                    .iter()
                    .zip(b.clone().iter())
                    .all(|(x, y)| matches(x, y, matchable, subst))
        }
        (MonoType::List(a), MonoType::List(b))
        | (MonoType::Ref(a), MonoType::Ref(b))
        | (MonoType::Mut(a), MonoType::Mut(b)) => {
            let (a, b) = (a.clone(), b.clone());
            matches(&a, &b, matchable, subst)
        }
        (MonoType::Mut(inner), other) | (other, MonoType::Mut(inner)) => {
            matches(inner, other, matchable, subst)
        }
        _ => false,
    }
}

/// Strict specificity: `a` dominates `b` iff `a` is an instance of `b` and
/// `b` is not an instance of `a`.
pub fn dominates(supply: &mut TypeVarSupply, a: &TypeScheme, b: &TypeScheme) -> bool {
    is_instance(supply, b, a) && !is_instance(supply, a, b)
}

/// Strict specificity INCLUDING constraints: `a` dominates `b` iff
/// `dominates(a, b)` holds on the bodies AND `a`'s constraint set is a subset
/// of `b`'s (a more-constrained candidate is more specific only when it is
/// also more specific on the underlying type). Constraints participate in the
/// comparison: `∀a. Ord a => a -> a` and `∀a. a -> a` are incomparable unless
/// one genuinely refines the other including its constraint context.
pub fn dominates_constrained(
    supply: &mut TypeVarSupply,
    a: &TypeScheme,
    b: &TypeScheme,
) -> bool {
    if !dominates(supply, a, b) {
        return false;
    }
    // a's constraints must be a subset of b's (a is no MORE constrained than
    // b in a way that would make it reject inputs b accepts). Compare by
    // constraint name (a coarse but sound approximation for now).
    a.constraints
        .iter()
        .all(|ca| b.constraints.iter().any(|cb| cb.name == ca.name))
}

/// Directional spec satisfaction: does the implementation scheme `imp` cover
/// the required spec `spec`?
///
/// ```text
/// imp ⊧ spec   ⟺   Instances(spec) ⊆ Instances(imp)
/// ```
///
/// The implementation must be AT LEAST AS GENERAL as the spec: every type the
/// spec allows must be a valid use of the implementation. Equality is valid
/// (reflexive). So:
///
///   - `fn f x = x` (∀a. a -> a) covers `spec f : int -> int` — the
///     polymorphic implementation covers the required concrete use.
///   - `fn f (x : int) = x` (int -> int) does NOT cover
///     `spec f : all a. a -> a` — an int implementation does not implement
///     the universally quantified contract.
///
/// Operationally:
///   1. Skolemize the SPEC (its quantified variables are rigid requirements).
///   2. Instantiate the IMPLEMENTATION with flexible metavariables.
///   3. One-way match the instantiated implementation against the rigid spec,
///      binding only the implementation's variables; a rigid spec skolem may
///      only match itself (rejecting escaping skolems falls out of `matches`).
///   4. Constraint check: every constraint the IMPLEMENTATION requires must be
///      provided by the spec — the implementation's constraints may not be
///      stronger than the spec's. (`∀a. Ord a => a -> a` does not cover the
///      unconstrained `∀a. a -> a`.)
pub fn implementation_covers_spec(
    supply: &mut TypeVarSupply,
    imp: &TypeScheme,
    spec: &TypeScheme,
) -> bool {
    // (4) Constraint check first: each constraint the implementation needs
    // must be among those the spec provides (by name, over the implementation's
    // own variables). A spec that provides fewer constraints cannot cover an
    // implementation that needs more.
    if !imp
        .constraints
        .iter()
        .all(|need| spec.constraints.iter().any(|have| have.name == need.name))
    {
        return false;
    }
    // (1)-(3): skolemize spec, instantiate impl, one-way match impl against
    // the rigid spec.
    let (spec_body, _) = skolemize(supply, spec);
    let (imp_body, renaming) = instantiate_fresh(supply, imp);
    let matchable: BTreeSet<TypeVarId> = renaming.values().copied().collect();
    let mut subst = Substitution::new();
    matches(&imp_body, &spec_body, &matchable, &mut subst)
}
