// Type representation, substitution, unification, and builtin constraint
// classes for the Lento type checker.
//
// Types are standard Hindley–Milner types with a few extensions:
// - `Sum` datatypes are generative: each `type` declaration gets a unique id
//   and sums unify by id plus arguments.
// - `Record` types carry an optional row variable (`rest`) so field access on
//   unknown record types can be inferred (`fn getx r = r.x`).
// - Builtin classes (`Num`, `Ord`, ...) model the overloads of the standard
//   intrinsics and operators. Unsolved constraints generalize into schemes.

use std::collections::{HashMap, HashSet};
use std::fmt;

pub type VarId = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Con {
    Unit,
    Bool,
    Int,
    Float,
    Str,
}

impl fmt::Display for Con {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Con::Unit => write!(f, "unit"),
            Con::Bool => write!(f, "bool"),
            Con::Int => write!(f, "int"),
            Con::Float => write!(f, "float"),
            Con::Str => write!(f, "str"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Var(VarId),
    Con(Con),
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Ref(Box<Type>),
    Mut(Box<Type>),
    Sum(SumType),
    Record(RecordType),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SumType {
    pub id: u32,
    pub name: String,
    pub args: Vec<Type>,
    pub alts: Vec<TypeAlt>,
}

/// One alternative of a resolved sum type: an uppercase constructor with a
/// payload type, or a bare member type injected implicitly.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeAlt {
    Ctor { name: String, payload: Type },
    Bare(Type),
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecordType {
    pub fields: Vec<(String, Type)>,
    pub rest: Option<VarId>,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(v) => write!(f, "t{v}"),
            Type::Con(c) => write!(f, "{c}"),
            Type::Arrow(from, to) => match from.as_ref() {
                Type::Arrow(_, _) => write!(f, "({from}) -> {to}"),
                _ => write!(f, "{from} -> {to}"),
            },
            Type::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::List(inner) => write!(f, "[{inner}]"),
            Type::Ref(inner) => write!(f, "ref {inner}"),
            Type::Mut(inner) => write!(f, "mut {inner}"),
            Type::Sum(sum) => {
                if sum.args.is_empty() {
                    write!(f, "{}", sum.name)
                } else {
                    let args: Vec<String> = sum.args.iter().map(|a| a.to_string()).collect();
                    write!(f, "{}<{}>", sum.name, args.join(", "))
                }
            }
            Type::Record(rec) => {
                let mut parts: Vec<String> = rec
                    .fields
                    .iter()
                    .map(|(name, t)| format!("{name}: {t}"))
                    .collect();
                if let Some(rest) = rec.rest {
                    parts.push(format!("...t{rest}"));
                }
                write!(f, "{{{}}}", parts.join(", "))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Substitution and unification
// ---------------------------------------------------------------------------

#[derive(Default)]
pub struct Subst {
    map: HashMap<VarId, Type>,
    next_var: VarId,
    /// Rigid (skolem) variables: only unifiable with ordinary unbound
    /// variables, never with concrete types. Used for spec conformance.
    rigid: HashSet<VarId>,
}

impl Subst {
    pub fn new() -> Self {
        // Fresh variable ids start above the ids hardcoded in the builtin
        // intrinsic schemes (which use small ids as placeholders).
        Subst { map: HashMap::new(), next_var: 1000, rigid: HashSet::new() }
    }

    pub fn fresh(&mut self) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        id
    }

    /// Follow variable links to the most specific type.
    pub fn prune(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match self.map.get(v) {
                Some(solution) => self.prune(solution),
                None => t.clone(),
            },
            other => other.clone(),
        }
    }

    pub fn bind(&mut self, v: VarId, t: Type) {
        self.map.insert(v, t);
    }

    /// Snapshot the substitution table (for speculative unification, e.g.
    /// spec conformance checks) and roll back later.
    pub fn snapshot(&self) -> HashMap<VarId, Type> {
        self.map.clone()
    }

    pub fn restore(&mut self, snapshot: HashMap<VarId, Type>) {
        self.map = snapshot;
    }

    pub fn mark_rigid(&mut self, v: VarId) {
        self.rigid.insert(v);
    }

    pub fn is_rigid(&self, v: VarId) -> bool {
        self.rigid.contains(&v)
    }

    pub fn lookup(&self, v: VarId) -> Option<&Type> {
        self.map.get(&v)
    }

    pub fn occurs(&self, v: VarId, t: &Type) -> bool {
        match t {
            Type::Var(other) => *other == v,
            Type::Con(_) => false,
            Type::Arrow(a, b) => self.occurs(v, a) || self.occurs(v, b),
            Type::Ref(a) | Type::Mut(a) => self.occurs(v, a),
            Type::Tuple(items) => items.iter().any(|t| self.occurs(v, t)),
            Type::List(inner) => self.occurs(v, inner),
            Type::Sum(sum) => {
                sum.args.iter().any(|t| self.occurs(v, t))
                    || sum.alts.iter().any(|alt| match alt {
                        TypeAlt::Ctor { payload, .. } => self.occurs(v, payload),
                        TypeAlt::Bare(t) => self.occurs(v, t),
                    })
            }
            Type::Record(rec) => {
                rec.fields.iter().any(|(_, t)| self.occurs(v, t))
                    || rec.rest.map(|r| r == v).unwrap_or(false)
            }
        }
    }

    /// Splice a record's `rest` variables that were solved to records, giving
    /// a flat view of all known fields plus the outermost rest var.
    pub fn flatten_record(&self, rec: &RecordType) -> RecordType {
        let mut fields = rec.fields.clone();
        let mut rest = rec.rest;
        let mut guard = 0;
        while let Some(r) = rest {
            guard += 1;
            if guard > 1000 {
                break; // defensive: avoid infinite row cycles
            }
            match self.map.get(&r) {
                Some(Type::Record(inner)) => {
                    let flat = self.flatten_record(inner);
                    fields.extend(flat.fields);
                    rest = flat.rest;
                }
                Some(Type::Var(v)) => {
                    // Follow one more link via prune-style loop.
                    rest = Some(*v);
                    // If the var is unbound this would loop; break out by
                    // checking whether it is actually bound.
                    if self.map.get(v).is_none() {
                        break;
                    }
                }
                _ => break,
            }
        }
        RecordType { fields, rest }
    }

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        let pa = self.prune(a);
        let pb = self.prune(b);
        match (&pa, &pb) {
            (Type::Var(x), Type::Var(y)) if x == y => Ok(()),
            (Type::Var(x), _) => self.bind_var(*x, pb),
            (_, Type::Var(y)) => self.bind_var(*y, pa),
            (Type::Con(x), Type::Con(y)) => {
                if x == y {
                    Ok(())
                } else {
                    Err(format!("cannot unify {x} with {y}"))
                }
            }
            (Type::Arrow(f1, t1), Type::Arrow(f2, t2)) => {
                self.unify(f1, f2)?;
                self.unify(t1, t2)
            }
            (Type::Tuple(xs), Type::Tuple(ys)) => {
                if xs.len() != ys.len() {
                    return Err(format!("cannot unify {} with {}", pa, pb));
                }
                for (x, y) in xs.iter().zip(ys.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Type::List(x), Type::List(y)) => self.unify(x, y),
            (Type::Ref(x), Type::Ref(y)) => self.unify(x, y),
            (Type::Mut(x), Type::Mut(y)) => self.unify(x, y),
            // `mut` is a memory marker, not a distinct type: unify through it.
            (Type::Mut(x), _) => self.unify(x, &pb),
            (_, Type::Mut(y)) => self.unify(&pa, y),
            (Type::Sum(x), Type::Sum(y)) => {
                if x.id != y.id {
                    return Err(format!("cannot unify {} with {}", pa, pb));
                }
                for (x, y) in x.args.iter().zip(y.args.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            // Bare sum alternative: the target type is a sum and the actual
            // type is one of its bare members (implicit injection).
            (Type::Sum(sum), other) => self.sum_member(sum, other, &pb),
            (other, Type::Sum(sum)) => self.sum_member(sum, other, &pa),
            // (Sum, Var) is handled by the Var arms above.
            (Type::Record(r1), Type::Record(r2)) => self.unify_records(r1, r2),
            _ => Err(format!("cannot unify {} with {}", pa, pb)),
        }
    }

    /// One-way membership check: does `other` match a bare alternative of
    /// `sum`? Unification against the alternative may bind variables; failed
    /// attempts roll back the bindings they introduced.
    fn sum_member(&mut self, sum: &SumType, other: &Type, pa: &Type) -> Result<(), String> {
        for alt in &sum.alts {
            if let TypeAlt::Bare(bare) = alt {
                let before: HashSet<VarId> = self.map.keys().copied().collect();
                let attempt = self.unify(other, bare);
                match attempt {
                    Ok(()) => return Ok(()),
                    Err(_) => {
                        // Roll back bindings introduced by the failed try.
                        let created: Vec<VarId> = self
                            .map
                            .keys()
                            .copied()
                            .filter(|k| !before.contains(k))
                            .collect();
                        for k in created {
                            self.map.remove(&k);
                        }
                    }
                }
            }
        }
        Err(format!("{pa} is not an alternative of {}", sum.name))
    }

    fn bind_var(&mut self, v: VarId, t: Type) -> Result<(), String> {
        if self.rigid.contains(&v) {
            // Rigid variables may only alias an ordinary unbound variable
            // (the definition quantifies over it); any concrete assignment
            // means the definition is narrower than the spec.
            match &t {
                Type::Var(w) if *w == v => return Ok(()),
                Type::Var(w) if !self.rigid.contains(w) => {
                    self.bind(*w, Type::Var(v));
                    return Ok(());
                }
                _ => {
                    return Err(format!(
                        "rigid type variable t{v} cannot be unified with {t}"
                    ));
                }
            }
        }
        if self.occurs(v, &t) {
            return Err(format!("infinite type: cannot construct t{v} = {t}"));
        }
        self.bind(v, t);
        Ok(())
    }

    /// Row-aware record unification.
    fn unify_records(&mut self, r1: &RecordType, r2: &RecordType) -> Result<(), String> {
        let f1 = self.flatten_record(r1);
        let f2 = self.flatten_record(r2);
        let names1: HashSet<&String> = f1.fields.iter().map(|(n, _)| n).collect();
        let names2: HashSet<&String> = f2.fields.iter().map(|(n, _)| n).collect();

        for (name, t1) in &f1.fields {
            if names2.contains(name) {
                let t2 = &f2.fields.iter().find(|(n, _)| n == name).unwrap().1;
                self.unify(t1, t2)?;
            }
        }
        let only1: Vec<(String, Type)> = f1
            .fields
            .iter()
            .filter(|(n, _)| !names2.contains(n))
            .cloned()
            .collect();
        let only2: Vec<(String, Type)> = f2
            .fields
            .iter()
            .filter(|(n, _)| !names1.contains(n))
            .cloned()
            .collect();

        match (only1.is_empty(), only2.is_empty()) {
            (true, true) => self.unify_rows(f1.rest, f2.rest),
            // r1 is closed; r2 demands fields r1 cannot provide.
            (true, false) => {
                if f1.rest.is_none() {
                    Err(format!(
                        "record {} lacks fields required by {}",
                        Type::Record(f1.clone()),
                        Type::Record(f2.clone())
                    ))
                } else {
                    // r1 open: its rest absorbs r2's extra fields.
                    let rest1 = f1.rest.unwrap();
                    self.bind_var(rest1, Type::Record(RecordType { fields: only2, rest: f2.rest }))
                }
            }
            (false, true) => {
                if f2.rest.is_none() {
                    Err(format!(
                        "record {} lacks fields required by {}",
                        Type::Record(f2.clone()),
                        Type::Record(f1.clone())
                    ))
                } else {
                    let rest2 = f2.rest.unwrap();
                    self.bind_var(rest2, Type::Record(RecordType { fields: only1, rest: f1.rest }))
                }
            }
            (false, false) => {
                let fresh = self.fresh();
                let rest1 = f1.rest.ok_or_else(|| {
                    format!(
                        "records {} and {} have different fields",
                        Type::Record(f1.clone()),
                        Type::Record(f2.clone())
                    )
                })?;
                let rest2 = f2.rest.ok_or_else(|| {
                    format!(
                        "records {} and {} have different fields",
                        Type::Record(f1.clone()),
                        Type::Record(f2.clone())
                    )
                })?;
                self.bind_var(rest1, Type::Record(RecordType { fields: only2, rest: Some(fresh) }))?;
                self.bind_var(rest2, Type::Record(RecordType { fields: only1, rest: Some(fresh) }))
            }
        }
    }

    /// Unify two row positions (each `None` = closed empty row).
    fn unify_rows(&mut self, a: Option<VarId>, b: Option<VarId>) -> Result<(), String> {
        match (a, b) {
            (None, None) => Ok(()),
            (Some(x), Some(y)) => {
                if x == y {
                    Ok(())
                } else {
                    self.bind_var(y, Type::Record(RecordType { fields: Vec::new(), rest: Some(x) }))
                }
            }
            (Some(x), None) => {
                self.bind_var(x, Type::Record(RecordType { fields: Vec::new(), rest: None }))
            }
            (None, Some(y)) => {
                self.bind_var(y, Type::Record(RecordType { fields: Vec::new(), rest: None }))
            }
        }
    }

    /// Free unification variables reachable from `t` (after pruning).
    pub fn free_vars(&self, t: &Type, out: &mut HashSet<VarId>) {
        match self.prune(t) {
            Type::Var(v) => {
                out.insert(v);
            }
            Type::Con(_) => {}
            Type::Arrow(a, b) => {
                self.free_vars(&a, out);
                self.free_vars(&b, out);
            }
            Type::Ref(a) | Type::Mut(a) => self.free_vars(&a, out),
            Type::Tuple(items) => {
                for t in items {
                    self.free_vars(&t, out);
                }
            }
            Type::List(inner) => self.free_vars(&inner, out),
            Type::Sum(sum) => {
                for t in &sum.args {
                    self.free_vars(t, out);
                }
                for alt in &sum.alts {
                    match alt {
                        TypeAlt::Ctor { payload, .. } => self.free_vars(payload, out),
                        TypeAlt::Bare(t) => self.free_vars(t, out),
                    }
                }
            }
            Type::Record(rec) => {
                for (_, t) in &rec.fields {
                    self.free_vars(t, out);
                }
                if let Some(r) = rec.rest {
                    out.insert(r);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Builtin constraint classes
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Num,
    Ord,
    Eq,
    Add,
    Concat,
    Seq,
    Len,
    Haystack,
    /// `Member target member` — target is a sum with `member` as a bare
    /// alternative (or already equals it). Deferred while target is unknown.
    Member,
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Class::Num => "Num",
            Class::Ord => "Ord",
            Class::Eq => "Eq",
            Class::Add => "Add",
            Class::Concat => "Concat",
            Class::Seq => "Seq",
            Class::Len => "Len",
            Class::Haystack => "Haystack",
            Class::Member => "Member",
        };
        write!(f, "{name}")
    }
}

/// `class args...` — e.g. `Haystack c e` for `contains`.
#[derive(Clone, Debug)]
pub struct Constraint {
    pub class: Class,
    pub args: Vec<Type>,
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args: Vec<String> = self.args.iter().map(|t| t.to_string()).collect();
        if args.is_empty() {
            write!(f, "{}", self.class)
        } else {
            write!(f, "{} {}", self.class, args.join(" "))
        }
    }
}

/// Outcome of attempting to solve one constraint.
pub enum SolveResult {
    /// The constraint holds; drop it.
    Solved,
    /// The constraint depends on unsolved variables; keep it.
    Deferred,
    /// The constraint cannot hold.
    Failed(String),
}

pub fn solve_constraint(subst: &mut Subst, con: &Constraint) -> SolveResult {
    let pruned: Vec<Type> = con.args.iter().map(|a| subst.prune(a)).collect();
    let has_var = pruned.iter().any(|t| matches!(t, Type::Var(_)));
    match con.class {
        Class::Num => one_arg(&pruned, Class::Num, |t| {
            matches!(t, Type::Con(Con::Int) | Type::Con(Con::Float))
        }),
        Class::Ord => one_arg(&pruned, Class::Ord, |t| {
            matches!(t, Type::Con(Con::Int) | Type::Con(Con::Float) | Type::Con(Con::Str))
        }),
        Class::Eq => eq_instance(subst, &pruned[0]),
        Class::Add => add_instance(subst, &pruned[0]),
        Class::Concat => match &pruned[0] {
            Type::Con(Con::Str) => SolveResult::Solved,
            Type::List(_) => SolveResult::Solved,
            t if matches!(t, Type::Var(_)) => SolveResult::Deferred,
            t => SolveResult::Failed(format!("no Concat instance for {t}")),
        },
        Class::Seq => match &pruned[0] {
            Type::Con(Con::Str) | Type::List(_) => SolveResult::Solved,
            t if matches!(t, Type::Var(_)) => SolveResult::Deferred,
            t => SolveResult::Failed(format!("no Seq instance for {t}")),
        },
        Class::Len => match &pruned[0] {
            Type::Con(Con::Str)
            | Type::List(_)
            | Type::Tuple(_)
            | Type::Record(_) => SolveResult::Solved,
            t if matches!(t, Type::Var(_)) => SolveResult::Deferred,
            t => SolveResult::Failed(format!("no Len instance for {t}")),
        },
        Class::Member => {
            if pruned.len() != 2 {
                return SolveResult::Failed("Member expects two arguments".into());
            }
            match (&pruned[0], &pruned[1]) {
                (Type::Var(_), _) => SolveResult::Deferred,
                (Type::Sum(sum), member) => {
                    for alt in &sum.alts {
                        if let TypeAlt::Bare(bare) = alt {
                            if &subst.prune(bare) == member {
                                return SolveResult::Solved;
                            }
                        }
                    }
                    SolveResult::Failed(format!("{member} is not an alternative of {}", sum.name))
                }
                (target, member) => match subst.unify(member, target) {
                    Ok(()) => SolveResult::Solved,
                    Err(e) => SolveResult::Failed(e),
                },
            }
        }
        Class::Haystack => {
            if pruned.len() != 2 {
                return SolveResult::Failed("Haystack expects two arguments".into());
            }
            match (&pruned[0], &pruned[1]) {
                (Type::Con(Con::Str), Type::Con(Con::Str)) => SolveResult::Solved,
                (Type::List(elem), element) => match subst.unify(elem, element) {
                    Ok(()) => SolveResult::Solved,
                    Err(e) => SolveResult::Failed(e),
                },
                (Type::Var(_), _) | (_, Type::Var(_)) if has_var => SolveResult::Deferred,
                (c, e) => SolveResult::Failed(format!("no Haystack instance for ({c}, {e})")),
            }
        }
    }
}

fn one_arg(pruned: &[Type], class: Class, ok: impl Fn(&Type) -> bool) -> SolveResult {
    match &pruned[0] {
        t if matches!(t, Type::Var(_)) => SolveResult::Deferred,
        t if ok(t) => SolveResult::Solved,
        t => SolveResult::Failed(format!("no {class} instance for {t}")),
    }
}

fn eq_instance(subst: &mut Subst, t: &Type) -> SolveResult {
    match t {
        Type::Var(_) => SolveResult::Deferred,
        Type::Con(_) => SolveResult::Solved,
        Type::List(inner) => eq_instance(subst, &subst.prune(inner)),
        Type::Tuple(items) => {
            for item in items {
                match eq_instance(subst, &subst.prune(item)) {
                    SolveResult::Solved => continue,
                    other => return other,
                }
            }
            SolveResult::Solved
        }
        Type::Record(rec) => {
            for (_, field) in &rec.fields {
                match eq_instance(subst, &subst.prune(field)) {
                    SolveResult::Solved => continue,
                    other => return other,
                }
            }
            SolveResult::Solved
        }
        Type::Sum(_) | Type::Ref(_) => SolveResult::Solved,
        other => SolveResult::Failed(format!("no Eq instance for {other}")),
    }
}

fn add_instance(_subst: &mut Subst, t: &Type) -> SolveResult {
    match t {
        Type::Var(_) => SolveResult::Deferred,
        Type::Con(Con::Int) | Type::Con(Con::Float) | Type::Con(Con::Str) => SolveResult::Solved,
        Type::List(_) => SolveResult::Solved,
        other => SolveResult::Failed(format!("no Add instance for {other}")),
    }
}

// ---------------------------------------------------------------------------
// Schemes
// ---------------------------------------------------------------------------

/// A quantified type: `forall vars. constraints => ty`.
#[derive(Clone, Debug)]
pub struct Scheme {
    pub vars: Vec<VarId>,
    pub constraints: Vec<Constraint>,
    pub ty: Type,
}

impl Scheme {
    pub fn monomorphic(ty: Type) -> Self {
        Scheme { vars: Vec::new(), constraints: Vec::new(), ty }
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.vars.is_empty() {
            let names: Vec<String> = self.vars.iter().map(|v| format!("t{v}")).collect();
            write!(f, "forall {}. ", names.join(" "))?;
        }
        if !self.constraints.is_empty() {
            let cons: Vec<String> = self.constraints.iter().map(|c| c.to_string()).collect();
            write!(f, "{} => ", cons.join(", "))?;
        }
        write!(f, "{}", self.ty)
    }
}
