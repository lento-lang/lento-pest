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

pub use crate::ast::Kind;

/// Known arities for builtin type constructors. Declared types are checked
/// against their declaration parameter counts by the analysis pass.
pub fn builtin_constructor_arity(name: &str) -> Option<usize> {
    match name {
        "int" | "float" | "str" | "bool" | "bytes" | "char" => Some(0),
        "list" => Some(1),
        _ => None,
    }
}

// Identity of a named type constructor (`int`, `str`, a user `type` alias).
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
    /// Type application `f a` where the head is not (yet) a known
    /// constructor: a higher-kinded type variable (`f : * -> *`) applied to
    /// arguments. When the head resolves to a constructor-like type
    /// (`Constructor`, `Sum`, or the `list` constructor), substitution
    /// *reduces* the application (see `Substitution::apply`). A `Var` head
    /// may be bound to a partially applied constructor during unification,
    /// which is how `Functor f` constraints dispatch.
    TypeApp {
        head: Box<MonoType>,
        args: Vec<MonoType>,
    },
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
    Constructor {
        name: String,
        payload: Option<MonoType>,
    },
    Bare(MonoType),
    Row(MonoType),
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
        assert!(self.next < 1 << 31, "type variable space exhausted");
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
            MonoType::TypeApp { head, args } => {
                head.collect_free_vars(seen, out);
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
                        MonoSumAlt::Row(ty) => ty.collect_free_vars(seen, out),
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
// Type application (higher-kinded types)
// --------------------------------------------------------------------------

/// Reduce a type application when the head is a known constructor-like type:
///
///   - `Constructor("list", []) a`      -> `List a`   (the list constructor)
///   - `Constructor(n, hargs) args`     -> `Constructor(n, hargs ++ args)`
///   - `Sum { name, args: hargs, alts } args` -> the sum with `args` appended
///
/// Anything else (an unresolved `Var` head, a function type, ...) stays as an
/// unreduced [`MonoType::TypeApp`]. This is the beta-step of type-level
/// application: binding a higher-kinded variable to a constructor makes
/// every `TypeApp` over it collapse to that constructor applied.
fn reduce_type_app(head: MonoType, args: Vec<MonoType>) -> MonoType {
    match head {
        MonoType::Constructor(name, head_args)
            if name == "list" && head_args.is_empty() && args.len() == 1 =>
        {
            MonoType::List(Box::new(args.into_iter().next().unwrap()))
        }
        MonoType::Constructor(name, mut head_args) => {
            head_args.extend(args);
            MonoType::Constructor(name, head_args)
        }
        MonoType::Sum {
            name,
            args: mut sum_args,
            alts,
        } => {
            sum_args.extend(args);
            MonoType::Sum { name, args: sum_args, alts }
        }
        head => MonoType::TypeApp {
            head: Box::new(head),
            args,
        },
    }
}

// --------------------------------------------------------------------------
// Capture-avoiding substitution
// --------------------------------------------------------------------------

/// A substitution from type variables to monotypes.
#[derive(Debug, Clone, PartialEq)]
pub struct Substitution {
    map: BTreeMap<TypeVarId, MonoType>,
    // Row unification allocates in a disjoint range from TypeVarSupply.
    next_row_var: TypeVarId,
}

impl Default for Substitution {
    fn default() -> Self {
        Self {
            map: BTreeMap::new(),
            next_row_var: 1 << 31,
        }
    }
}

impl Substitution {
    pub fn new() -> Self {
        Substitution::default()
    }

    /// The singleton substitution `id |-> ty`.
    pub fn singleton(id: TypeVarId, ty: MonoType) -> Self {
        let mut subst = Self::new();
        subst.insert(id, ty);
        subst
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
            MonoType::TypeApp { head, args } => {
                let head = self.apply(head);
                let args: Vec<MonoType> = args.iter().map(|a| self.apply(a)).collect();
                reduce_type_app(head, args)
            }
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
            MonoType::Record { fields, rest } => {
                let mut fields = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.apply(ty)))
                    .collect::<Vec<_>>();
                let rest = match rest.map(|id| self.apply(&MonoType::Var(id))) {
                    Some(MonoType::Record {
                        fields: solved,
                        rest,
                    }) => {
                        fields.extend(solved);
                        rest
                    }
                    Some(MonoType::Var(id)) => Some(id),
                    None => None,
                    _ => unreachable!("row tail must resolve to a record row"),
                };
                MonoType::Record { fields, rest }
            }
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
                        MonoSumAlt::Row(ty) => MonoSumAlt::Row(self.apply(ty)),
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
        let mut map: BTreeMap<TypeVarId, MonoType> =
            other.map.iter().map(|(k, v)| (*k, self.apply(v))).collect();
        for (k, v) in &self.map {
            map.insert(*k, v.clone());
        }
        Substitution {
            map,
            next_row_var: self.next_row_var.max(other.next_row_var),
        }
    }

    fn fresh_row(&mut self) -> TypeVarId {
        let id = self.next_row_var;
        self.next_row_var = self
            .next_row_var
            .checked_add(1)
            .expect("row variable space exhausted");
        id
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

/// Bind a higher-kinded variable (the head of a `TypeApp`) to the constructor
/// prefix of `other` and report that prefix for re-application. The prefix
/// keeps any leading arguments that the type application does not itself
/// supply: `f a ~ Result int e` is a kind error, but a partially applied
/// head like `map : ... -> (Result int) a -> ...` binds `f := Result int`.
/// Returns `None` when `other` is not constructor-like (kind mismatch: a
/// `* -> *` variable cannot unify with a plain `*` type).
fn bind_type_app_head(
    subst: &mut Substitution,
    var: TypeVarId,
    other: &MonoType,
    app_arg_count: usize,
) -> Result<Option<MonoType>, UnifyError> {
    let prefix = |name: &str, constructor_args: &[MonoType]| {
        let keep = constructor_args.len().saturating_sub(app_arg_count);
        MonoType::Constructor(name.to_string(), constructor_args[..keep].to_vec())
    };
    let head = match other {
        MonoType::Constructor(name, args) => prefix(name, args),
        MonoType::Sum { name, args, .. } => prefix(name, args),
        MonoType::List(_) => MonoType::Constructor("list".to_string(), Vec::new()),
        _ => return Ok(None),
    };
    bind_var(subst, var, &head)?;
    Ok(Some(head))
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
        // `f a` vs `f' a'`: same arity -> unify heads, then arguments.
        (
            MonoType::TypeApp { head: h1, args: a1 },
            MonoType::TypeApp { head: h2, args: a2 },
        ) => {
            if a1.len() != a2.len() {
                return Err(UnifyError::Mismatch { left, right });
            }
            unify(subst, h1, h2)?;
            for (x, y) in a1.clone().iter().zip(a2.clone().iter()) {
                unify(subst, x, y)?;
            }
            Ok(())
        }
        // `f a` (variable head) vs a constructor-like type: bind the head to
        // the bare constructor (kind `* -> *`), then unify the reduced
        // application against the other side. A plain `List` head binds to
        // the `list` constructor.
        (MonoType::TypeApp { head, args }, other) if matches!(&**head, MonoType::Var(_)) => {
            let MonoType::Var(var) = &**head else { unreachable!() };
            match bind_type_app_head(subst, *var, other, args.len()) {
                Ok(Some(bound_head)) => {
                    let applied = subst.apply(&MonoType::TypeApp {
                        head: Box::new(bound_head),
                        args: args.clone(),
                    });
                    unify(subst, &applied, other)
                }
                Ok(None) => Err(UnifyError::Mismatch { left, right }),
                Err(error) => Err(error),
            }
        }
        (other, MonoType::TypeApp { head, args }) if matches!(&**head, MonoType::Var(_)) => {
            let MonoType::Var(var) = &**head else { unreachable!() };
            match bind_type_app_head(subst, *var, other, args.len()) {
                Ok(Some(bound_head)) => {
                    let applied = subst.apply(&MonoType::TypeApp {
                        head: Box::new(bound_head),
                        args: args.clone(),
                    });
                    unify(subst, other, &applied)
                }
                Ok(None) => Err(UnifyError::Mismatch { left, right }),
                Err(error) => Err(error),
            }
        }
        (MonoType::Constructor(n1, a1), MonoType::Constructor(n2, a2)) => {
            if n1 != n2 || a1.len() != a2.len() {
                return Err(UnifyError::Mismatch { left, right });
            }
            for (x, y) in a1.clone().iter().zip(a2.clone().iter()) {
                unify(subst, x, y)?;
            }
            Ok(())
        }
        // Specs lower named ADTs as constructors, while inferred values carry
        // their resolved sum alternatives. Both denote the same nominal type.
        (
            MonoType::Sum {
                name: sum_name,
                args: sum_args,
                ..
            },
            MonoType::Constructor(name, args),
        )
        | (
            MonoType::Constructor(name, args),
            MonoType::Sum {
                name: sum_name,
                args: sum_args,
                ..
            },
        ) if sum_name == name && sum_args.len() == args.len() => {
            for (sum_arg, arg) in sum_args.iter().zip(args) {
                unify(subst, sum_arg, arg)?;
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
        // The `list` type constructor applied to one argument denotes the
        // same type as the structural List node (impl targets like
        // `impl Functor list`). The bare constructor (kind `* -> *`) is
        // compatible with any List instance shape.
        (MonoType::Constructor(name, args), MonoType::List(inner))
        | (MonoType::List(inner), MonoType::Constructor(name, args))
            if name == "list" && args.len() <= 1 =>
        {
            match (args.first(), args.len()) {
                (Some(arg), _) => unify(subst, arg, inner),
                _ => Ok(()),
            }
        }
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
        ) => unify_sums(
            subst, left_name, left_args, left_alts, right_name, right_args, right_alts,
        ),
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
        let candidate = match alt {
            MonoSumAlt::Bare(candidate) => candidate,
            MonoSumAlt::Row(row) => {
                let snapshot = subst.clone();
                if unify(subst, row, other).is_ok() {
                    return Ok(());
                }
                *subst = snapshot;
                continue;
            }
            MonoSumAlt::Constructor { .. } => continue,
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

fn unify_sums(
    subst: &mut Substitution,
    left_name: &str,
    left_args: &[MonoType],
    left_alts: &[MonoSumAlt],
    right_name: &str,
    right_args: &[MonoType],
    right_alts: &[MonoSumAlt],
) -> Result<(), UnifyError> {
    let mismatch = || UnifyError::Mismatch {
        left: MonoType::Sum {
            name: left_name.to_string(),
            args: left_args.to_vec(),
            alts: left_alts.to_vec(),
        },
        right: MonoType::Sum {
            name: right_name.to_string(),
            args: right_args.to_vec(),
            alts: right_alts.to_vec(),
        },
    };
    let left_nominal = !left_name.starts_with('<');
    let right_nominal = !right_name.starts_with('<');
    if left_args.len() != right_args.len()
        || (left_nominal && right_nominal && left_name != right_name)
    {
        return Err(mismatch());
    }
    for (left, right) in left_args.iter().zip(right_args) {
        unify(subst, left, right)?;
    }
    if left_nominal && right_nominal {
        return Ok(());
    }
    let left_rows = left_alts
        .iter()
        .filter_map(|alt| match alt {
            MonoSumAlt::Row(row) => Some(row),
            _ => None,
        })
        .collect::<Vec<_>>();
    let right_rows = right_alts
        .iter()
        .filter_map(|alt| match alt {
            MonoSumAlt::Row(row) => Some(row),
            _ => None,
        })
        .collect::<Vec<_>>();
    let left_known = left_alts
        .iter()
        .filter(|alt| !matches!(alt, MonoSumAlt::Row(_)))
        .collect::<Vec<_>>();
    let right_known = right_alts
        .iter()
        .filter(|alt| !matches!(alt, MonoSumAlt::Row(_)))
        .collect::<Vec<_>>();
    // Match each known alternative at most once. A display name such as
    // `<sum:2>` cannot stand in for comparing its payloads and members.
    let mut matched_right = BTreeSet::new();
    let mut unmatched_left = Vec::new();
    for left in &left_known {
        let found = right_known.iter().enumerate().find_map(|(index, right)| {
            if matched_right.contains(&index) || sum_alt_shape(left) != sum_alt_shape(right) {
                return None;
            }
            let snapshot = subst.clone();
            if unify_sum_alternatives(subst, left, right).is_ok() {
                Some(index)
            } else {
                *subst = snapshot;
                None
            }
        });
        if let Some(index) = found {
            matched_right.insert(index);
        } else {
            unmatched_left.push((**left).clone());
        }
    }
    let unmatched_right = right_known
        .iter()
        .enumerate()
        .filter(|(index, _)| !matched_right.contains(index))
        .map(|(_, alt)| (**alt).clone())
        .collect::<Vec<_>>();
    if !unmatched_left.is_empty() {
        let Some(row) = right_rows.first() else {
            return Err(mismatch());
        };
        unify(subst, row, &sum_row(unmatched_left))?;
    }
    if !unmatched_right.is_empty() {
        let Some(row) = left_rows.first() else {
            return Err(mismatch());
        };
        unify(subst, row, &sum_row(unmatched_right))?;
    }
    Ok(())
}

fn unify_sum_alternatives(
    subst: &mut Substitution,
    left: &MonoSumAlt,
    right: &MonoSumAlt,
) -> Result<(), UnifyError> {
    match (left, right) {
        (
            MonoSumAlt::Constructor {
                payload: Some(a), ..
            },
            MonoSumAlt::Constructor {
                payload: Some(b), ..
            },
        ) => unify(subst, a, b),
        (
            MonoSumAlt::Constructor { payload: None, .. },
            MonoSumAlt::Constructor { payload: None, .. },
        ) => Ok(()),
        (MonoSumAlt::Bare(a), MonoSumAlt::Bare(b)) => unify(subst, a, b),
        _ => Err(UnifyError::Mismatch {
            left: sum_row(vec![left.clone()]),
            right: sum_row(vec![right.clone()]),
        }),
    }
}

fn sum_alt_shape(alt: &MonoSumAlt) -> (u8, &str) {
    match alt {
        MonoSumAlt::Constructor { name, .. } => (0, name),
        MonoSumAlt::Bare(_) => (1, ""),
        MonoSumAlt::Row(_) => (2, ""),
    }
}

fn sum_row(alts: Vec<MonoSumAlt>) -> MonoType {
    MonoType::Sum {
        name: "<row>".to_string(),
        args: Vec::new(),
        alts,
    }
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
            None => Err(record_mismatch(
                left_fields,
                left_rest,
                right_fields,
                right_rest,
            )),
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
            None => Err(record_mismatch(
                left_fields,
                left_rest,
                right_fields,
                right_rest,
            )),
        },
        (false, false) => {
            let left_rest = left_rest
                .ok_or_else(|| record_mismatch(left_fields, left_rest, right_fields, right_rest))?;
            let right_rest = right_rest.ok_or_else(|| {
                record_mismatch(left_fields, Some(left_rest), right_fields, right_rest)
            })?;
            let fresh = subst.fresh_row();
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
pub fn generalize(env: &TypeEnv, ty: &MonoType, constraints: Vec<SchemeConstraint>) -> TypeScheme {
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
        MonoType::TypeApp { head, args } => MonoType::TypeApp {
            head: Box::new(rename_vars(head, renaming)),
            args: args.iter().map(|a| rename_vars(a, renaming)).collect(),
        },
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
                    MonoSumAlt::Row(ty) => MonoSumAlt::Row(rename_vars(ty, renaming)),
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
            if let Some(var) = binders.get(name) {
                // A quantified binder used bare is a variable; applied to
                // arguments it is a higher-kinded type application (`f a`).
                if args.is_empty() {
                    return var.clone();
                }
                return MonoType::TypeApp {
                    head: Box::new(var.clone()),
                    args: args.iter().map(|a| lower_ty(a, binders)).collect(),
                };
            }
                if args.is_empty() {
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
        Ty::Sum(alts) => MonoType::Sum {
            name: "<surface-sum>".to_string(),
            args: Vec::new(),
            alts: alts
                .iter()
                .map(|alt| match alt {
                    crate::ast::SumAlt::Ctor { name, payload } => MonoSumAlt::Constructor {
                        name: name.clone(),
                        payload: payload.as_ref().map(|ty| lower_ty(ty, binders)),
                    },
                    crate::ast::SumAlt::Bare(ty) => MonoSumAlt::Bare(lower_ty(ty, binders)),
                    crate::ast::SumAlt::Row(name) => MonoSumAlt::Row(
                        binders
                            .get(name)
                            .cloned()
                            .unwrap_or_else(|| MonoType::Constructor(name.clone(), Vec::new())),
                    ),
                })
                .collect(),
        },
        Ty::RecordType(fields) => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| (name.clone(), lower_ty(ty, binders)))
                .collect(),
            rest: None,
        },
        Ty::OpenRecordType { fields, row } => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| (name.clone(), lower_ty(ty, binders)))
                .collect(),
            rest: match binders.get(row) {
                Some(MonoType::Var(id)) => Some(*id),
                _ => None,
            },
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
    let skolems = scheme.quantified.iter().map(|q| renaming[q]).collect();
    (body, skolems)
}

/// Is `instance` an instance of `general`? i.e. is there a substitution for
/// `general`'s quantified variables that yields exactly `instance`'s shape.
///
/// This is one-way matching, not full unification: `general`'s quantified
/// variables may be bound, but `instance`'s variables (skolemized to rigid
/// constants) may only match themselves. Matching propagates a substitution
/// for `general`'s variables left-to-right.
pub fn is_instance(
    supply: &mut TypeVarSupply,
    general: &TypeScheme,
    instance: &TypeScheme,
) -> bool {
    // Skolemize `instance`: its variables become rigid constants.
    let (instance_body, _) = skolemize(supply, instance);
    // Instantiate `general`: its quantified variables become matchable.
    let (general_body, renaming) = instantiate_fresh(supply, general);
    // The matchable variables are exactly the fresh ids general mapped to.
    let matchable: BTreeSet<TypeVarId> = renaming.values().copied().collect();
    let mut subst = Substitution::new();
    matches(&general_body, &instance_body, &matchable, &mut subst, false)
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

/// Check a call against a callable type, allowing an actual record argument
/// to contain fields omitted by a closed record parameter.
pub fn call_type_compatible(expected: &MonoType, actual: &MonoType) -> bool {
    match (expected, actual) {
        (
            MonoType::Function(expected_arg, expected_ret),
            MonoType::Function(actual_arg, actual_ret),
        ) => {
            call_type_compatible(expected_ret, actual_ret)
                && matches(
                    actual_arg,
                    expected_arg,
                    &BTreeSet::new(),
                    &mut Substitution::new(),
                    false,
                )
        }
        _ => expected == actual,
    }
}

/// The bare, unapplied constructor of a constructor-like type, for binding a
/// higher-kinded variable's head: `Option a`/`Option` -> `Option`,
/// `[a]`/`List` -> `list`. `None` for non-constructor kinds.
fn bare_constructor_prefix(ty: &MonoType, app_arg_count: usize) -> Option<MonoType> {
    let prefix = |name: &str, constructor_args: &[MonoType]| {
        let keep = constructor_args.len().saturating_sub(app_arg_count);
        MonoType::Constructor(name.to_string(), constructor_args[..keep].to_vec())
    };
    match ty {
        MonoType::Constructor(name, args) => Some(prefix(name, args)),
        MonoType::Sum { name, args, .. } => Some(prefix(name, args)),
        MonoType::List(_) => Some(MonoType::Constructor("list".to_string(), Vec::new())),
        _ => None,
    }
}

/// One-way matching: bind `left`'s matchable variables (via `subst`) so that
/// `left` becomes structurally equal to the rigid `right`. Only variables in
/// `matchable` may be bound; all other variables are rigid constants and are
/// never bound. Lookup is non-chasing: a bound variable maps directly to its
/// (rigid) image, which never contains a matchable variable.
/// Bind the implementation's open row variable so it carries exactly the
/// spec fields the implementation does not declare. Returns `false` when the
/// row cannot absorb them: it is not a matchable variable, or it is already
/// bound (through a shared row elsewhere in the implementation type) to a
/// record missing one of the required fields. Binding once keeps coverage
/// sound: two positions sharing a row cannot demand contradictory shapes.
fn absorb_missing_fields(
    rest: Option<TypeVarId>,
    missing: &[(String, MonoType)],
    matchable: &BTreeSet<TypeVarId>,
    subst: &mut Substitution,
) -> bool {
    let Some(mut var) = rest else { return false };
    loop {
        match subst.get(var) {
            Some(MonoType::Var(next)) => var = *next,
            Some(MonoType::Record { fields, rest: None }) => {
                return missing.iter().all(|(name, required)| {
                    fields
                        .iter()
                        .find(|(bound_name, _)| bound_name == name)
                        .is_some_and(|(_, bound)| {
                            // The pinned row image must satisfy the new
                            // demand: image ⊇ required (sum width, record
                            // fields). Direction matters — the inverse would
                            // accept contradictions like `y : [int|str]`
                            // pinned while `y : [int|str|bool]` is demanded.
                            matches(
                                bound,
                                required,
                                &BTreeSet::new(),
                                &mut Substitution::new(),
                                false,
                            )
                        })
                });
            }
            Some(_) => return false,
            None => break,
        }
    }
    if !matchable.contains(&var) {
        return false;
    }
    subst.insert(
        var,
        MonoType::Record {
            fields: missing.to_vec(),
            rest: None,
        },
    );
    true
}

fn matches(
    left: &MonoType,
    right: &MonoType,
    matchable: &BTreeSet<TypeVarId>,
    subst: &mut Substitution,
    open_absorption: bool,
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
                    .all(|(x, y)| matches(x, y, matchable, subst, open_absorption))
        }
        (MonoType::TypeApp { head: h1, args: a1 }, MonoType::TypeApp { head: h2, args: a2 }) => {
            a1.len() == a2.len()
                && matches(h1, h2, matchable, subst, open_absorption)
                && a1
                    .clone()
                    .iter()
                    .zip(a2.clone().iter())
                    .all(|(x, y)| matches(x, y, matchable, subst, open_absorption))
        }
        // A matchable `TypeApp` head binds to the bare constructor of the
        // other side, then the reduced application is matched. This is how a
        // generic spec (`Functor f => ... -> f a -> f b`) covers a concrete
        // implementation (`... -> Option a -> Option b`).
        (MonoType::TypeApp { head, args }, right)
            if matches!(&**head, MonoType::Var(v) if matchable.contains(v)) =>
        {
            let MonoType::Var(var) = &**head else { unreachable!() };
            let Some(bound_head) = bare_constructor_prefix(right, args.len()) else {
                return false;
            };
            subst.insert(*var, bound_head.clone());
            let applied = subst.apply(&MonoType::TypeApp {
                head: Box::new(bound_head),
                args: args.clone(),
            });
            matches(&applied, right, matchable, subst, open_absorption)
        }
        (left, MonoType::TypeApp { head, args })
            if matches!(&**head, MonoType::Var(v) if matchable.contains(v)) =>
        {
            let MonoType::Var(var) = &**head else { unreachable!() };
            let Some(bound_head) = bare_constructor_prefix(left, args.len()) else {
                return false;
            };
            subst.insert(*var, bound_head.clone());
            let applied = subst.apply(&MonoType::TypeApp {
                head: Box::new(bound_head),
                args: args.clone(),
            });
            matches(left, &applied, matchable, subst, open_absorption)
        }
        (MonoType::Sum { name: sum_name, args: sum_args, .. }, MonoType::Constructor(name, args)) => {
            sum_name == name
                && sum_args.len() == args.len()
                && sum_args
                    .iter()
                    .zip(args)
                    .all(|(sum_arg, arg)| matches(sum_arg, arg, matchable, subst, open_absorption))
        }
        (
            MonoType::Constructor(name, args),
            MonoType::Sum {
                name: sum_name,
                args: sum_args,
                ..
            },
        ) => {
            sum_name == name
                && args.len() == sum_args.len()
                && args
                    .iter()
                    .zip(sum_args)
                    .all(|(arg, sum_arg)| matches(arg, sum_arg, matchable, subst, open_absorption))
        }
        (MonoType::Function(f1, t1), MonoType::Function(f2, t2)) => {
            let (f1, t1, f2, t2) = (f1.clone(), t1.clone(), f2.clone(), t2.clone());
            matches(&f1, &f2, matchable, subst, open_absorption)
                && matches(&t1, &t2, matchable, subst, open_absorption)
        }
        (MonoType::Tuple(a), MonoType::Tuple(b)) => {
            a.len() == b.len()
                && a.clone()
                    .iter()
                    .zip(b.clone().iter())
                    .all(|(x, y)| matches(x, y, matchable, subst, open_absorption))
        }
        (MonoType::List(a), MonoType::List(b))
        | (MonoType::Ref(a), MonoType::Ref(b))
        | (MonoType::Mut(a), MonoType::Mut(b)) => {
            let (a, b) = (a.clone(), b.clone());
            matches(&a, &b, matchable, subst, open_absorption)
        }
        // The `list` type constructor vs the structural List node. The bare
        // constructor is compatible with any List shape.
        (MonoType::Constructor(name, args), MonoType::List(inner))
        | (MonoType::List(inner), MonoType::Constructor(name, args))
            if name == "list" && args.len() <= 1 =>
        {
            match (args.first(), args.len()) {
                (Some(arg), _) => {
                    let (arg, inner) = (arg.clone(), inner.clone());
                    matches(&arg, &inner, matchable, subst, open_absorption)
                }
                _ => true,
            }
        }
        (MonoType::Mut(inner), other) | (other, MonoType::Mut(inner)) => {
            matches(inner, other, matchable, subst, open_absorption)
        }
        (
            MonoType::Record {
                fields: left_fields,
                rest: left_rest,
            },
            MonoType::Record {
                fields: right_fields,
                rest: right_rest,
            },
        ) => {
            // Spec coverage (`open_absorption`) reads the record
            // specification as "the implementation may only read the fields
            // the spec provides": every implementation field must appear in
            // the spec, while the spec's additional fields ride the
            // implementation's open row variable — bound once, so every
            // position sharing the row must accept the same shape. Plain
            // call compatibility keeps the inverse reading: an actual
            // record may carry fields the closed parameter omits.
            let mut fields_match = true;
            let mut missing = Vec::new();
            for (name, right) in right_fields.iter() {
                match left_fields.iter().find(|(left_name, _)| left_name == name) {
                    Some((_, left)) => {
                        if !matches(left, right, matchable, subst, open_absorption) {
                            fields_match = false;
                        }
                    }
                    None => missing.push((name.clone(), right.clone())),
                }
            }
            let left_fields_provided = !open_absorption
                || left_fields.iter().all(|(name, left)| {
                    right_fields
                        .iter()
                        .find(|(right_name, _)| right_name == name)
                        .is_some_and(|(_, right)| {
                            matches(left, right, matchable, subst, open_absorption)
                        })
                });
            let missing_absorbed = missing.is_empty()
                || open_absorption && absorb_missing_fields(*left_rest, &missing, matchable, subst);
            fields_match
                && left_fields_provided
                && missing_absorbed
                && (right_rest.is_none() || left_rest.is_some())
        }
        (MonoType::Sum { alts: left, .. }, MonoType::Sum { alts: right, .. }) => {
            let left_rows = left.iter().any(|alt| matches!(alt, MonoSumAlt::Row(_)));
            right.iter().all(|required| match required {
                MonoSumAlt::Row(_) => left_rows,
                MonoSumAlt::Constructor { name, payload } => left.iter().any(|candidate| {
                    matches!(candidate, MonoSumAlt::Constructor { name: candidate_name, payload: candidate_payload }
                        if candidate_name == name
                            && match (candidate_payload, payload) {
                                (Some(candidate), Some(required)) => matches(candidate, required, matchable, subst, open_absorption),
                                (None, None) => true,
                                _ => false,
                            })
                }),
                MonoSumAlt::Bare(required) => left.iter().any(|candidate| {
                    matches!(candidate, MonoSumAlt::Bare(candidate) if matches(candidate, required, matchable, subst, open_absorption))
                }),
            })
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
pub fn dominates_constrained(supply: &mut TypeVarSupply, a: &TypeScheme, b: &TypeScheme) -> bool {
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
    matches(&imp_body, &spec_body, &matchable, &mut subst, true)
}

/// Lower a surface type to its semantic form, resolving named type
/// applications through `type_declarations`: a sum declaration becomes
/// `MonoType::Sum` (its variants), a record synonym becomes its record
/// structure, and other synonyms are substituted transparently. Quantifier
/// binders map names to fresh variables. This is the declaration-aware
/// counterpart of [`lower_ty`], which never consults declarations.
pub fn lower_surface_ty(
    ty: &Ty,
    binders: &BTreeMap<String, MonoType>,
    type_declarations: &BTreeMap<String, (Vec<String>, crate::ast::Ty)>,
) -> MonoType {
        match ty {
            crate::ast::Ty::Named { name, args } => {
                if let Some(bound) = binders.get(name) {
                    // Bare binder -> variable; applied binder -> type app.
                    if args.is_empty() {
                        return bound.clone();
                    }
                    return MonoType::TypeApp {
                        head: Box::new(bound.clone()),
                        args: args
                            .iter()
                            .map(|argument| lower_surface_ty(argument, binders, type_declarations))
                            .collect(),
                    };
                }
                if args.is_empty() {
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
            if let Some((parameters, source)) = type_declarations.get(name) {
                if parameters.len() == args.len() {
                    let mapping = parameters
                        .iter()
                        .zip(args)
                        .map(|(parameter, argument)| {
                            (
                                parameter.clone(),
                                lower_surface_ty(argument, binders, type_declarations),
                            )
                        })
                        .collect::<BTreeMap<_, _>>();
                    if let crate::ast::Ty::Sum(_) = source {
                        if let MonoType::Sum { alts, .. } =
                            lower_surface_ty(source, &mapping, type_declarations)
                        {
                            return MonoType::Sum {
                                name: name.clone(),
                                args: args
                                    .iter()
                                    .map(|argument| {
                                        lower_surface_ty(argument, binders, type_declarations)
                                    })
                                    .collect(),
                                alts,
                            };
                        }
                    }
                    return lower_surface_ty(source, &mapping, type_declarations);
                }
            }
            MonoType::Constructor(
                name.clone(),
                args.iter()
                    .map(|argument| lower_surface_ty(argument, binders, type_declarations))
                    .collect(),
            )
        }
        crate::ast::Ty::Tuple(items) => MonoType::Tuple(
            items
                .iter()
                .map(|item| lower_surface_ty(item, binders, type_declarations))
                .collect(),
        ),
        crate::ast::Ty::List(inner) => MonoType::List(Box::new(lower_surface_ty(
            inner,
            binders,
            type_declarations,
        ))),
        crate::ast::Ty::Arrow { from, to } => MonoType::Function(
            Box::new(lower_surface_ty(from, binders, type_declarations)),
            Box::new(lower_surface_ty(to, binders, type_declarations)),
        ),
        crate::ast::Ty::Ref(inner) => MonoType::Ref(Box::new(lower_surface_ty(
            inner,
            binders,
            type_declarations,
        ))),
        crate::ast::Ty::Mut(inner) => MonoType::Mut(Box::new(lower_surface_ty(
            inner,
            binders,
            type_declarations,
        ))),
        crate::ast::Ty::NamedBinder { ty, .. } => lower_surface_ty(ty, binders, type_declarations),
        crate::ast::Ty::Sum(alts) => MonoType::Sum {
            name: format!("<sum:{}>", alts.len()),
            args: Vec::new(),
            alts: alts
                .iter()
                .map(|alt| match alt {
                    crate::ast::SumAlt::Ctor { name, payload } => MonoSumAlt::Constructor {
                        name: name.clone(),
                        payload: payload
                            .as_ref()
                            .map(|payload| lower_surface_ty(payload, binders, type_declarations)),
                    },
                    crate::ast::SumAlt::Bare(ty) => {
                        MonoSumAlt::Bare(lower_surface_ty(ty, binders, type_declarations))
                    }
                    crate::ast::SumAlt::Row(name) => MonoSumAlt::Row(
                        binders
                            .get(name)
                            .cloned()
                            .unwrap_or_else(|| MonoType::Constructor(name.clone(), Vec::new())),
                    ),
                })
                .collect(),
        },
        crate::ast::Ty::RecordType(fields) => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        lower_surface_ty(ty, binders, type_declarations),
                    )
                })
                .collect(),
            rest: None,
        },
        crate::ast::Ty::OpenRecordType { fields, row } => MonoType::Record {
            fields: fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        lower_surface_ty(ty, binders, type_declarations),
                    )
                })
                .collect(),
            rest: match binders.get(row) {
                Some(MonoType::Var(id)) => Some(*id),
                _ => None,
            },
        },
    }
}
