// Bidirectional type inference over function clauses.
//
// For a clause `fn f p1 ... pn [-> R] = body`:
//
//   1. Every parameter pattern gets a fresh expected type `Pi`.
//   2. Each pattern is *checked* against its `Pi`, extending a clause-local
//      environment with the variables the pattern binds.
//   3. An annotation on a parameter unifies `Pi` with that annotation.
//   4. The body is inferred (or checked against a declared return type).
//   5. The clause's curried type is `P1 -> ... -> Pn -> R`.
//
// Inference is standard Damas–Milner over the internal `MonoType`
// representation. Patterns and expressions are checked/inferred
// bidirectionally; generalization happens only after a whole function group
// is processed (see `infer_function_group`), never per clause, so mutually
// recursive clauses and multi-clause functions share one scope.

use std::collections::BTreeMap;
use std::fmt;

use crate::ast::{BinaryOp, Expr, FnDecl, Lit, PatKind, Pattern, UnaryOp};
use crate::semantics::FunctionGroup;
use crate::types::{
    generalize, instantiate, unify, MonoType, SchemeConstraint, Substitution, TypeEnv, TypeScheme,
    TypeVarSupply, UnifyError,
};

/// A typing error with the clause it arose in.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    /// Two types could not be unified.
    Unify(UnifyError),
    /// A name is not bound in the environment.
    UnboundVariable(String),
    /// A pattern and its expected type have incompatible shapes.
    PatternMismatch { expected: MonoType, got: String },
    /// An operator was applied to a type it does not support.
    BadOperator { op: String, ty: MonoType },
    /// A record field access on a non-record (or unknown-field) type.
    BadMember { ty: MonoType, field: String },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TypeErrorKind::Unify(e) => write!(f, "{e}"),
            TypeErrorKind::UnboundVariable(n) => write!(f, "unbound variable `{n}`"),
            TypeErrorKind::PatternMismatch { expected, got } => {
                write!(f, "pattern `{got}` does not match expected type {expected:?}")
            }
            TypeErrorKind::BadOperator { op, ty } => {
                write!(f, "operator `{op}` does not apply to {ty:?}")
            }
            TypeErrorKind::BadMember { ty, field } => {
                write!(f, "type {ty:?} has no field `{field}`")
            }
        }
    }
}

impl std::error::Error for TypeError {}

impl From<UnifyError> for TypeError {
    fn from(e: UnifyError) -> Self {
        TypeError {
            kind: TypeErrorKind::Unify(e),
        }
    }
}

fn unbound(name: &str) -> TypeError {
    TypeError {
        kind: TypeErrorKind::UnboundVariable(name.to_string()),
    }
}

/// Convenience constructors for the primitive constructors.
pub mod ctor {
    use super::MonoType;
    fn con(name: &str) -> MonoType {
        MonoType::Constructor(name.to_string(), Vec::new())
    }
    pub fn unit() -> MonoType {
        MonoType::Tuple(Vec::new())
    }
    pub fn bool() -> MonoType {
        con("bool")
    }
    pub fn int() -> MonoType {
        con("int")
    }
    pub fn float() -> MonoType {
        con("float")
    }
    pub fn str() -> MonoType {
        con("str")
    }
}

/// The inference context: a substitution, a fresh-variable supply, and the
/// collected constraints.
pub struct InferCtx {
    pub supply: TypeVarSupply,
    pub subst: Substitution,
    pub constraints: Vec<SchemeConstraint>,
}

impl InferCtx {
    pub fn new() -> Self {
        InferCtx {
            supply: TypeVarSupply::new(),
            subst: Substitution::new(),
            constraints: Vec::new(),
        }
    }

    fn fresh(&mut self) -> MonoType {
        self.supply.fresh()
    }

    fn unify(&mut self, a: &MonoType, b: &MonoType) -> Result<(), TypeError> {
        Ok(unify(&mut self.subst, a, b)?)
    }

    /// Resolve a type through the current substitution.
    pub fn resolve(&self, ty: &MonoType) -> MonoType {
        self.subst.apply(ty)
    }
}

impl Default for InferCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// The result of inferring one clause: its curried type and the patterns as
/// written (for pattern dispatch, which is a separate stage from typing).
#[derive(Debug, Clone, PartialEq)]
pub struct InferredClause {
    /// The curried clause type `P1 -> ... -> Pn -> R`.
    pub ty: MonoType,
    /// The parameter patterns, in order (value dispatch).
    pub patterns: Vec<Pattern>,
    /// Constraints arising from the clause body (e.g. from operators).
    pub constraints: Vec<SchemeConstraint>,
}

/// A base environment with the primitive types of the intrinsics and
/// operators, so inference has something to start from. Names match
/// `intrinsics.rs`. Built from its own throwaway supply so the caller's
/// clause variables still start at 0 (keeps inferred ids deterministic).
pub fn base_env(_supply: &mut TypeVarSupply) -> TypeEnv {
    let mut supply = TypeVarSupply::new();
    let supply = &mut supply;
    let mut env = TypeEnv::new();
    let mono = |t: MonoType| TypeScheme::mono(t);
    // A couple of representative polymorphic intrinsics; the full table grows
    // as the evaluator's intrinsics are typed.
    let a = supply.fresh_id();
    let b = supply.fresh_id();
    env.insert(
        "concat".to_string(),
        TypeScheme {
            quantified: vec![a],
            constraints: vec![],
            body: MonoType::Function(
                Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
                Box::new(MonoType::Function(
                    Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
                    Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
                )),
            ),
        },
    );
    env.insert(
        "head".to_string(),
        TypeScheme {
            quantified: vec![a],
            constraints: vec![],
            body: MonoType::Function(
                Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
                Box::new(MonoType::Var(a)),
            ),
        },
    );
    env.insert(
        "map".to_string(),
        TypeScheme {
            quantified: vec![a, b],
            constraints: vec![],
            body: MonoType::Function(
                Box::new(MonoType::Function(
                    Box::new(MonoType::Var(a)),
                    Box::new(MonoType::Var(b)),
                )),
                Box::new(MonoType::Function(
                    Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
                    Box::new(MonoType::List(Box::new(MonoType::Var(b)))),
                )),
            ),
        },
    );
    env.insert(
        "len".to_string(),
        mono(MonoType::Function(
            Box::new(MonoType::List(Box::new(MonoType::Var(a)))),
            Box::new(ctor::int()),
        )),
    );
    env.insert(
        "to_string".to_string(),
        mono(MonoType::Function(
            Box::new(MonoType::Var(a)),
            Box::new(ctor::str()),
        )),
    );
    let _ = b;
    env
}

// --------------------------------------------------------------------------
// Pattern checking
// --------------------------------------------------------------------------

/// Check a pattern against an expected type, extending `env` with the
/// pattern's bound variables (each mapped to a monomorphic type for the
/// duration of the clause).
pub fn check_pattern(
    ctx: &mut InferCtx,
    pat: &Pattern,
    expected: &MonoType,
    env: &mut TypeEnv,
) -> Result<(), TypeError> {
    // An explicit annotation unifies with the expected type first.
    if let Some(annotation) = &pat.annotation {
        let ann = crate::types::lower_ty(annotation, &BTreeMap::new());
        ctx.unify(expected, &ann)?;
    }
    match &pat.kind {
        PatKind::Var(name) => {
            env.insert(name.clone(), TypeScheme::mono(expected.clone()));
            Ok(())
        }
        PatKind::Wildcard => Ok(()),
        PatKind::Lit(lit) => {
            let lit_ty = match lit {
                Lit::Bool(_) => ctor::bool(),
                Lit::Int(_) => ctor::int(),
                Lit::Float(_) => ctor::float(),
                Lit::Str(_) => ctor::str(),
            };
            ctx.unify(expected, &lit_ty)
        }
        PatKind::Tuple(parts) => {
            let part_tys: Vec<MonoType> = parts.iter().map(|_| ctx.fresh()).collect();
            ctx.unify(expected, &MonoType::Tuple(part_tys.clone()))?;
            for (p, t) in parts.iter().zip(part_tys.iter()) {
                check_pattern(ctx, p, t, env)?;
            }
            Ok(())
        }
        PatKind::List(parts) => {
            let elem = ctx.fresh();
            ctx.unify(expected, &MonoType::List(Box::new(elem.clone())))?;
            for p in parts {
                check_pattern(ctx, p, &elem, env)?;
            }
            Ok(())
        }
        PatKind::Spread(name) => {
            // `...rest` binds a list of the element type.
            let elem = ctx.fresh();
            ctx.unify(expected, &MonoType::List(Box::new(elem.clone())))?;
            env.insert(
                name.clone(),
                TypeScheme::mono(MonoType::List(Box::new(elem))),
            );
            Ok(())
        }
        PatKind::Record { fields, rest } => {
            // Records are structurally typed here as a nominal `record`
            // constructor carrying field types; a dedicated record row type
            // arrives with the type-declaration environment.
            let mut field_tys = Vec::new();
            for f in fields {
                let ft = ctx.fresh();
                check_pattern(ctx, &f.pattern, &ft, env)?;
                field_tys.push(MonoType::Constructor(f.name.clone(), vec![ft]));
            }
            let rec = MonoType::Constructor("record".to_string(), field_tys);
            ctx.unify(expected, &rec)?;
            if let Some(rest) = rest {
                env.insert(rest.clone(), TypeScheme::mono(expected.clone()));
            }
            Ok(())
        }
    }
}

// --------------------------------------------------------------------------
// Expression inference
// --------------------------------------------------------------------------

/// Infer the type of an expression in `env`.
pub fn infer_expr(ctx: &mut InferCtx, expr: &Expr, env: &mut TypeEnv) -> Result<MonoType, TypeError> {
    match expr {
        Expr::Lit(l) => Ok(match l.value {
            Lit::Bool(_) => ctor::bool(),
            Lit::Int(_) => ctor::int(),
            Lit::Float(_) => ctor::float(),
            Lit::Str(_) => ctor::str(),
        }),
        Expr::Var(v) => match env.get(&v.name) {
            Some(scheme) => Ok(instantiate(&mut ctx.supply, scheme).0),
            None => Err(unbound(&v.name)),
        },
        Expr::Lambda(l) => {
            let mut local = env.clone();
            let mut param_tys = Vec::new();
            for p in &l.params {
                let pt = ctx.fresh();
                check_pattern(ctx, p, &pt, &mut local)?;
                param_tys.push(pt);
            }
            let body_ty = infer_expr(ctx, &l.body, &mut local)?;
            let mut ty = body_ty;
            for pt in param_tys.into_iter().rev() {
                ty = MonoType::Function(Box::new(pt), Box::new(ty));
            }
            Ok(ty)
        }
        Expr::Call(c) => {
            let callee_ty = infer_expr(ctx, &c.callee, env)?;
            // Fold the argument list right-to-left into a curried application.
            let mut result = callee_ty;
            for arg in &c.args {
                let arg_ty = infer_expr(ctx, arg, env)?;
                let ret = ctx.fresh();
                ctx.unify(
                    &result,
                    &MonoType::Function(Box::new(arg_ty), Box::new(ret.clone())),
                )?;
                result = ret;
            }
            Ok(result)
        }
        Expr::Unary(u) => {
            let operand = infer_expr(ctx, &u.operand, env)?;
            match u.op {
                UnaryOp::Not => {
                    ctx.unify(&operand, &ctor::bool())?;
                    Ok(ctor::bool())
                }
                UnaryOp::Neg => {
                    // Numeric negation; keep the operand type.
                    Ok(operand)
                }
            }
        }
        Expr::Binary(b) => infer_binary(ctx, b, env),
        Expr::Tuple(t) => {
            let mut items = Vec::new();
            for e in &t.items {
                items.push(infer_expr(ctx, e, env)?);
            }
            Ok(MonoType::Tuple(items))
        }
        Expr::List(l) => infer_list(ctx, l, env),
        Expr::Block(b) => {
            // A block evaluates its statements; the value is the last
            // expression (or unit). Local declarations extend the env.
            let mut local = env.clone();
            let mut last = ctor::unit();
            for stmt in &b.body {
                match stmt {
                    crate::ast::Stmt::Expr(e) => last = infer_expr(ctx, e, &mut local)?,
                    crate::ast::Stmt::Decl(crate::ast::Decl::Let(l)) => {
                        let vt = infer_expr(ctx, &l.value, &mut local)?;
                        check_pattern(ctx, &l.pattern, &vt, &mut local)?;
                    }
                    _ => {
                        // fn/spec/type inside a block: handled by the
                        // collection phase at top level; ignored here.
                    }
                }
            }
            Ok(last)
        }
        Expr::Match(m) => {
            let scrut = infer_expr(ctx, &m.scrutinee, env)?;
            let result = ctx.fresh();
            for arm in &m.arms {
                let mut local = env.clone();
                check_pattern(ctx, &arm.pattern, &scrut, &mut local)?;
                if let Some(guard) = &arm.guard {
                    let g = infer_expr(ctx, guard, &mut local)?;
                    ctx.unify(&g, &ctor::bool())?;
                }
                let body = infer_expr(ctx, &arm.body, &mut local)?;
                ctx.unify(&result, &body)?;
            }
            Ok(result)
        }
        Expr::Record(r) => {
            let mut fields = Vec::new();
            for entry in &r.entries {
                match entry {
                    crate::ast::RecordValueEntry::Field(name, e) => {
                        let ft = infer_expr(ctx, e, env)?;
                        fields.push(MonoType::Constructor(name.clone(), vec![ft]));
                    }
                    crate::ast::RecordValueEntry::Spread(_) => {
                        // Spread merges fields; approximated until record rows.
                    }
                }
            }
            Ok(MonoType::Constructor("record".to_string(), fields))
        }
        Expr::Member(m) => {
            let obj = infer_expr(ctx, &m.obj, env)?;
            match ctx.resolve(&obj) {
                MonoType::Constructor(name, fields) if name == "record" => {
                    for f in &fields {
                        if let MonoType::Constructor(fname, fargs) = f {
                            if *fname == m.field && fargs.len() == 1 {
                                return Ok(fargs[0].clone());
                            }
                        }
                    }
                    Err(TypeError {
                        kind: TypeErrorKind::BadMember {
                            ty: obj,
                            field: m.field.clone(),
                        },
                    })
                }
                other => Err(TypeError {
                    kind: TypeErrorKind::BadMember {
                        ty: other,
                        field: m.field.clone(),
                    },
                }),
            }
        }
        Expr::Index(i) => {
            let obj = infer_expr(ctx, &i.obj, env)?;
            let idx = infer_expr(ctx, &i.index, env)?;
            ctx.unify(&idx, &ctor::int())?;
            let elem = ctx.fresh();
            ctx.unify(&obj, &MonoType::List(Box::new(elem.clone())))?;
            Ok(elem)
        }
        Expr::Ref(r) => {
            let inner = infer_expr(ctx, &r.inner, env)?;
            Ok(MonoType::Ref(Box::new(inner)))
        }
        Expr::Assign(a) => {
            // `place := value` evaluates to unit; place must be a mut/ref.
            let value = infer_expr(ctx, &a.value, env)?;
            let place = infer_expr(ctx, &a.place, env)?;
            let _ = (place, value);
            Ok(ctor::unit())
        }
    }
}

fn infer_binary(
    ctx: &mut InferCtx,
    b: &crate::ast::BinaryExpr,
    env: &mut TypeEnv,
) -> Result<MonoType, TypeError> {
    let lhs = infer_expr(ctx, &b.lhs, env)?;
    let rhs = infer_expr(ctx, &b.rhs, env)?;
    match b.op {
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
            // Numeric arithmetic: operands share a numeric type; result is it.
            ctx.unify(&lhs, &rhs)?;
            Ok(lhs)
        }
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
            ctx.unify(&lhs, &rhs)?;
            Ok(ctor::bool())
        }
        BinaryOp::And | BinaryOp::Or => {
            ctx.unify(&lhs, &ctor::bool())?;
            ctx.unify(&rhs, &ctor::bool())?;
            Ok(ctor::bool())
        }
    }
}

fn infer_list(
    ctx: &mut InferCtx,
    l: &crate::ast::ListExpr,
    env: &mut TypeEnv,
) -> Result<MonoType, TypeError> {
    let elem = ctx.fresh();
    let mut cur = l;
    loop {
        match cur {
            crate::ast::ListExpr::Empty => break,
            crate::ast::ListExpr::Cells(cell) => {
                let h = infer_expr(ctx, &cell.head, env)?;
                ctx.unify(&elem, &h)?;
                cur = &cell.tail;
            }
        }
    }
    Ok(MonoType::List(Box::new(elem)))
}

// --------------------------------------------------------------------------
// Clause inference
// --------------------------------------------------------------------------

/// Infer one clause bidirectionally, returning its curried type and patterns.
///
/// Steps (per the phase description):
///   1. fresh `Pi` per parameter;
///   2. check each pattern against `Pi`, extending a clause-local env;
///   3. annotations unify with `Pi` (inside `check_pattern`);
///   4. body infers against fresh `R`, or unifies with the declared return;
///   5. the curried clause type is `P1 -> ... -> Pn -> R`.
pub fn infer_clause(
    ctx: &mut InferCtx,
    clause: &FnDecl,
    env: &TypeEnv,
) -> Result<InferredClause, TypeError> {
    let mut local = env.clone();
    let mut param_tys = Vec::with_capacity(clause.params.len());
    for p in &clause.params {
        let pi = ctx.fresh();
        check_pattern(ctx, p, &pi, &mut local)?;
        param_tys.push(pi);
    }
    let body_ty = infer_expr(ctx, &clause.body, &mut local)?;
    let result_ty = match &clause.ret {
        Some(ret) => {
            let declared = crate::types::lower_ty(ret, &BTreeMap::new());
            ctx.unify(&body_ty, &declared)?;
            declared
        }
        None => body_ty,
    };
    let mut ty = result_ty;
    for pt in param_tys.into_iter().rev() {
        ty = MonoType::Function(Box::new(pt), Box::new(ty));
    }
    Ok(InferredClause {
        ty,
        patterns: clause.params.clone(),
        constraints: ctx.constraints.clone(),
    })
}

/// The inferred principal scheme of a whole function group, plus each
/// clause's (ungeneralized) type and patterns.
#[derive(Debug, Clone, PartialEq)]
pub struct InferredGroup {
    pub name: String,
    /// Per-clause inferred types, in source order, resolved through the
    /// final substitution.
    pub clause_types: Vec<MonoType>,
    /// Per-clause patterns, in source order.
    pub clause_patterns: Vec<Vec<Pattern>>,
}

/// Infer every clause of a function group in a shared context.
///
/// Generalization is deliberately *not* done here per clause: the group's
/// clauses are inferred together and the caller generalizes once, after the
/// whole (possibly mutually recursive) group is processed.
pub fn infer_function_group(
    ctx: &mut InferCtx,
    group: &FunctionGroup,
    env: &TypeEnv,
) -> Result<InferredGroup, TypeError> {
    let mut clause_types = Vec::new();
    let mut clause_patterns = Vec::new();
    for clause in &group.raw_clauses {
        let inferred = infer_clause(ctx, clause, env)?;
        clause_types.push(inferred.ty);
        clause_patterns.push(inferred.patterns);
    }
    // Resolve through the accumulated substitution so callers see final types.
    let clause_types = clause_types.iter().map(|t| ctx.resolve(t)).collect();
    Ok(InferredGroup {
        name: group.name.clone(),
        clause_types,
        clause_patterns,
    })
}

/// Generalize a clause/group type relative to the ambient environment. This
/// is called once per group *after* the whole group (or its recursive SCC)
/// has been inferred — never per clause.
pub fn generalize_group(env: &TypeEnv, ty: &MonoType, constraints: Vec<SchemeConstraint>) -> TypeScheme {
    generalize(env, ty, constraints)
}
