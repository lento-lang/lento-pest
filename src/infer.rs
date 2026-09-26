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
    /// The function body with a canonical type annotation at every expression node.
    pub body: crate::semantics::TypedExpr,
    /// The parameter patterns, in order (value dispatch).
    pub patterns: Vec<Pattern>,
    /// Constraints arising from the clause body (e.g. from operators).
    pub constraints: Vec<SchemeConstraint>,
}

/// A base environment with the primitive types of the intrinsics and
/// operators, so inference has something to start from. Names match
/// `intrinsics.rs`.
///
/// Intrinsic type-variable ids start at `1_000_000` so they never collide with
/// a caller's clause variables (which start at 0). This keeps inferred clause
/// schemes quantifying their own low ids deterministically.
pub fn base_env(_supply: &mut TypeVarSupply) -> TypeEnv {
    // Fixed high ids for intrinsic type variables.
    let a = 1_000_000u32;
    let b = 1_000_001u32;
    let mut env = TypeEnv::new();
    let mono = |t: MonoType| TypeScheme::mono(t);
    // Intrinsics use broad schemes here.  Class declarations in the prelude
    // replace overloaded names with their constrained schemes; the fallback
    // schemes keep standalone programs and the canonical CLI pipeline typed.
    let unary = |input: MonoType, output: MonoType| {
        MonoType::Function(Box::new(input), Box::new(output))
    };
    let binary = |left: MonoType, right: MonoType, output: MonoType| {
        unary(left, unary(right, output))
    };
    let list = |element: MonoType| MonoType::List(Box::new(element));
    let var = |id| MonoType::Var(id);
    let poly = |quantified: Vec<u32>, body| TypeScheme {
        quantified,
        constraints: vec![],
        body,
    };

    env.insert("print".to_string(), mono(unary(var(a), ctor::unit())));
    env.insert("println".to_string(), mono(unary(var(a), ctor::unit())));
    env.insert(
        "assert".to_string(),
        mono(unary(ctor::bool(), ctor::unit())),
    );
    env.insert(
        "concat".to_string(),
        poly(vec![a], binary(var(a), var(a), var(a))),
    );
    env.insert(
        "head".to_string(),
        poly(vec![a], unary(list(var(a)), var(a))),
    );
    env.insert(
        "len".to_string(),
        poly(vec![a], unary(var(a), ctor::int())),
    );
    env.insert(
        "__list_len".to_string(),
        poly(vec![a], unary(list(var(a)), ctor::int())),
    );
    env.insert(
        "__str_len".to_string(),
        mono(unary(ctor::str(), ctor::int())),
    );
    env.insert(
        "to_string".to_string(),
        poly(vec![a], unary(var(a), ctor::str())),
    );
    env.insert("tail".to_string(), poly(vec![a], unary(list(var(a)), list(var(a)))));
    env.insert("is_empty".to_string(), poly(vec![a], unary(list(var(a)), ctor::bool())));
    env.insert("abs".to_string(), poly(vec![a], unary(var(a), var(a))));
    env.insert("min".to_string(), poly(vec![a], binary(var(a), var(a), var(a))));
    env.insert("max".to_string(), poly(vec![a], binary(var(a), var(a), var(a))));
    env.insert("parse_int".to_string(), mono(unary(ctor::str(), ctor::int())));
    env.insert("contains".to_string(), poly(vec![a, b], binary(var(a), var(b), ctor::bool())));
    env.insert("take".to_string(), poly(vec![a], binary(ctor::int(), var(a), var(a))));
    env.insert("drop".to_string(), poly(vec![a], binary(ctor::int(), var(a), var(a))));
    env.insert("reverse".to_string(), poly(vec![a], unary(var(a), var(a))));
    env.insert("slice".to_string(), poly(vec![a], unary(ctor::int(), unary(ctor::int(), unary(var(a), var(a))))));
    env.insert("join".to_string(), mono(binary(ctor::str(), list(ctor::str()), ctor::str())));
    env.insert("split".to_string(), mono(binary(ctor::str(), ctor::str(), list(ctor::str()))));
    env.insert(
        "map".to_string(),
        poly(vec![a, b], binary(unary(var(a), var(b)), list(var(a)), list(var(b)))),
    );
    env.insert(
        "filter".to_string(),
        poly(vec![a], binary(unary(var(a), ctor::bool()), list(var(a)), list(var(a)))),
    );
    env.insert(
        "foldl".to_string(),
        poly(vec![a, b], binary(unary(var(a), unary(var(b), var(a))), var(a), unary(list(var(b)), var(a)))),
    );
    env.insert("any".to_string(), poly(vec![a], binary(unary(var(a), ctor::bool()), list(var(a)), ctor::bool())));
    env.insert("all".to_string(), poly(vec![a], binary(unary(var(a), ctor::bool()), list(var(a)), ctor::bool())));
    env.insert("range".to_string(), mono(binary(ctor::int(), ctor::int(), list(ctor::int()))));
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
        PatKind::Constructor { name, payload } => {
            let declared = env.get(name).cloned().ok_or_else(|| {
                TypeError {
                    kind: TypeErrorKind::UnboundVariable(name.clone()),
                }
            })?;
            let ctor_ty = instantiate(&mut ctx.supply, &declared).0;
            let (payload_ty, result_ty) = match (payload, ctor_ty) {
                (Some(_), MonoType::Function(argument, result)) => (Some(*argument), *result),
                (None, result) => (None, result),
                (Some(_), other) => {
                    return Err(TypeError {
                        kind: TypeErrorKind::PatternMismatch {
                            expected: other,
                            got: name.clone(),
                        },
                    });
                }
            };
            ctx.unify(expected, &result_ty)?;
            if let (Some(pattern), Some(payload_ty)) = (payload, payload_ty) {
                check_pattern(ctx, pattern, &payload_ty, env)?;
            }
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

/// Infer an expression and retain annotations for every nested expression.
pub fn infer_typed_expr(
    ctx: &mut InferCtx,
    expr: &Expr,
    env: &mut TypeEnv,
) -> Result<crate::semantics::TypedExpr, TypeError> {
    use crate::semantics::{TypedExpr, TypedExprKind, TypedMatchArm};
    use crate::ast::{RecordValueEntry, Stmt};

    let composite = |ty, children| TypedExpr {
        ty,
        kind: TypedExprKind::Composite {
            source: Box::new(expr.clone()),
            children,
        },
    };

    match expr {
        Expr::Lit(l) => Ok(TypedExpr {
            ty: match l.value {
                Lit::Bool(_) => ctor::bool(),
                Lit::Int(_) => ctor::int(),
                Lit::Float(_) => ctor::float(),
                Lit::Str(_) => ctor::str(),
            },
            kind: TypedExprKind::Lit(l.value.clone()),
        }),
        Expr::Var(v) => match env.get(&v.name) {
            Some(scheme) => {
                let (ty, constraints) = instantiate(&mut ctx.supply, scheme);
                ctx.constraints.extend(constraints);
                Ok(TypedExpr {
                    ty,
                    kind: TypedExprKind::Var(v.name.clone()),
                })
            }
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
            let body = infer_typed_expr(ctx, &l.body, &mut local)?;
            let mut ty = body.ty.clone();
            for pt in param_tys.into_iter().rev() {
                ty = MonoType::Function(Box::new(pt), Box::new(ty));
            }
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Lambda {
                    params: l.params.clone(),
                    body: Box::new(body),
                },
            })
        }
        Expr::Call(c) => {
            let callee = infer_typed_expr(ctx, &c.callee, env)?;
            let mut result = callee.ty.clone();
            let mut args = Vec::with_capacity(c.args.len());
            for arg in &c.args {
                let arg = infer_typed_expr(ctx, arg, env)?;
                let ret = ctx.fresh();
                ctx.unify(
                    &result,
                    &MonoType::Function(Box::new(arg.ty.clone()), Box::new(ret.clone())),
                )?;
                result = ret;
                args.push(arg);
            }
            Ok(TypedExpr {
                ty: result,
                kind: TypedExprKind::Call {
                    callee: Box::new(callee),
                    args,
                    specialization: None,
                },
            })
        }
        Expr::Unary(u) => {
            let operand = infer_typed_expr(ctx, &u.operand, env)?;
            let ty = match u.op {
                UnaryOp::Not => {
                    ctx.unify(&operand.ty, &ctor::bool())?;
                    ctor::bool()
                }
                UnaryOp::Neg => operand.ty.clone(),
            };
            Ok(composite(ty, vec![operand]))
        }
        Expr::Binary(b) => {
            let lhs = infer_typed_expr(ctx, &b.lhs, env)?;
            let rhs = infer_typed_expr(ctx, &b.rhs, env)?;
            let ty = match b.op {
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    ctx.unify(&lhs.ty, &rhs.ty)?;
                    lhs.ty.clone()
                }
                BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
                    ctx.unify(&lhs.ty, &rhs.ty)?;
                    ctor::bool()
                }
                BinaryOp::And | BinaryOp::Or => {
                    ctx.unify(&lhs.ty, &ctor::bool())?;
                    ctx.unify(&rhs.ty, &ctor::bool())?;
                    ctor::bool()
                }
            };
            Ok(composite(ty, vec![lhs, rhs]))
        }
        Expr::Tuple(t) => {
            let mut items = Vec::with_capacity(t.items.len());
            for item in &t.items {
                items.push(infer_typed_expr(ctx, item, env)?);
            }
            Ok(composite(
                MonoType::Tuple(items.iter().map(|item| item.ty.clone()).collect()),
                items,
            ))
        }
        Expr::List(l) => {
            let elem = ctx.fresh();
            let mut current = l;
            let mut children = Vec::new();
            loop {
                match current {
                    crate::ast::ListExpr::Empty => break,
                    crate::ast::ListExpr::Cells(cell) => {
                        let head = infer_typed_expr(ctx, &cell.head, env)?;
                        ctx.unify(&elem, &head.ty)?;
                        children.push(head);
                        current = &cell.tail;
                    }
                }
            }
            Ok(composite(MonoType::List(Box::new(elem)), children))
        }
        Expr::Block(b) => {
            let mut local = env.clone();
            let mut last = ctor::unit();
            let mut children = Vec::new();
            for stmt in &b.body {
                match stmt {
                    Stmt::Expr(e) => {
                        let value = infer_typed_expr(ctx, e, &mut local)?;
                        last = value.ty.clone();
                        children.push(value);
                    }
                    Stmt::Decl(crate::ast::Decl::Let(binding)) => {
                        let value = infer_typed_expr(ctx, &binding.value, &mut local)?;
                        check_pattern(ctx, &binding.pattern, &value.ty, &mut local)?;
                        children.push(value);
                    }
                    _ => {}
                }
            }
            Ok(composite(last, children))
        }
        Expr::Match(m) => {
            let scrutinee = infer_typed_expr(ctx, &m.scrutinee, env)?;
            let result = ctx.fresh();
            let mut arms = Vec::with_capacity(m.arms.len());
            for arm in &m.arms {
                let mut local = env.clone();
                check_pattern(ctx, &arm.pattern, &scrutinee.ty, &mut local)?;
                let guard = if let Some(guard) = &arm.guard {
                    let guard = infer_typed_expr(ctx, guard, &mut local)?;
                    ctx.unify(&guard.ty, &ctor::bool())?;
                    Some(guard)
                } else {
                    None
                };
                let body = infer_typed_expr(ctx, &arm.body, &mut local)?;
                ctx.unify(&result, &body.ty)?;
                arms.push(TypedMatchArm {
                    pattern: arm.pattern.clone(),
                    guard,
                    body,
                });
            }
            Ok(TypedExpr {
                ty: result,
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                },
            })
        }
        Expr::Record(r) => {
            let mut fields = Vec::new();
            let mut children = Vec::new();
            for entry in &r.entries {
                match entry {
                    RecordValueEntry::Field(name, expression) => {
                        let field = infer_typed_expr(ctx, expression, env)?;
                        fields.push(MonoType::Constructor(name.clone(), vec![field.ty.clone()]));
                        children.push(field);
                    }
                    RecordValueEntry::Spread(expression) => {
                        children.push(infer_typed_expr(ctx, expression, env)?);
                    }
                }
            }
            Ok(composite(MonoType::Constructor("record".into(), fields), children))
        }
        Expr::Member(m) => {
            let object = infer_typed_expr(ctx, &m.obj, env)?;
            let ty = match ctx.resolve(&object.ty) {
                MonoType::Constructor(name, fields) if name == "record" => {
                    let found = fields.iter().find_map(|field| match field {
                        MonoType::Constructor(field_name, args) if *field_name == m.field && args.len() == 1 => Some(args[0].clone()),
                        _ => None,
                    });
                    found.ok_or_else(|| TypeError {
                        kind: TypeErrorKind::BadMember {
                            ty: object.ty.clone(),
                            field: m.field.clone(),
                        },
                    })?
                }
                other => return Err(TypeError {
                    kind: TypeErrorKind::BadMember { ty: other, field: m.field.clone() },
                }),
            };
            Ok(composite(ty, vec![object]))
        }
        Expr::Index(i) => {
            let object = infer_typed_expr(ctx, &i.obj, env)?;
            let index = infer_typed_expr(ctx, &i.index, env)?;
            ctx.unify(&index.ty, &ctor::int())?;
            let elem = ctx.fresh();
            ctx.unify(&object.ty, &MonoType::List(Box::new(elem.clone())))?;
            Ok(composite(elem, vec![object, index]))
        }
        Expr::Ref(r) => {
            let inner = infer_typed_expr(ctx, &r.inner, env)?;
            Ok(composite(MonoType::Ref(Box::new(inner.ty.clone())), vec![inner]))
        }
        Expr::Assign(a) => {
            let value = infer_typed_expr(ctx, &a.value, env)?;
            let place = infer_typed_expr(ctx, &a.place, env)?;
            Ok(composite(ctor::unit(), vec![place, value]))
        }
    }
}

/// Infer only the type when a caller does not need the typed expression tree.
pub fn infer_expr(ctx: &mut InferCtx, expr: &Expr, env: &mut TypeEnv) -> Result<MonoType, TypeError> {
    infer_typed_expr(ctx, expr, env).map(|typed| typed.ty)
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
    let constraints_start = ctx.constraints.len();
    let mut local = env.clone();
    let mut param_tys = Vec::with_capacity(clause.params.len());
    for p in &clause.params {
        let pi = ctx.fresh();
        check_pattern(ctx, p, &pi, &mut local)?;
        param_tys.push(pi);
    }
    let body = infer_typed_expr(ctx, &clause.body, &mut local)?;
    let result_ty = match &clause.ret {
        Some(ret) => {
            let declared = crate::types::lower_ty(ret, &BTreeMap::new());
            ctx.unify(&body.ty, &declared)?;
            declared
        }
        None => body.ty.clone(),
    };
    let mut ty = result_ty;
    for pt in param_tys.into_iter().rev() {
        ty = MonoType::Function(Box::new(pt), Box::new(ty));
    }
    Ok(InferredClause {
        ty,
        body,
        patterns: clause.params.clone(),
        constraints: ctx.constraints[constraints_start..].to_vec(),
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
    /// Per-clause recursively typed bodies, in source order.
    pub clause_bodies: Vec<crate::semantics::TypedExpr>,
    /// Per-clause class and prelude constraints after group substitution.
    pub clause_constraints: Vec<Vec<SchemeConstraint>>,
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
    let mut clause_bodies = Vec::new();
    let mut clause_constraints = Vec::new();
    for clause in &group.raw_clauses {
        let inferred = infer_clause(ctx, clause, env)?;
        clause_types.push(inferred.ty);
        clause_patterns.push(inferred.patterns);
        clause_bodies.push(inferred.body);
        clause_constraints.push(inferred.constraints);
    }
    // Resolve every annotation and constraint through the final group substitution.
    let clause_types = clause_types.iter().map(|t| ctx.resolve(t)).collect();
    for body in &mut clause_bodies {
        resolve_typed_expr(ctx, body);
    }
    for constraints in &mut clause_constraints {
        for constraint in constraints {
            for argument in &mut constraint.args {
                *argument = ctx.resolve(argument);
            }
        }
    }
    Ok(InferredGroup {
        name: group.name.clone(),
        clause_types,
        clause_patterns,
        clause_bodies,
        clause_constraints,
    })
}

pub(crate) fn resolve_typed_expr(ctx: &InferCtx, expression: &mut crate::semantics::TypedExpr) {
    use crate::semantics::TypedExprKind;
    expression.ty = ctx.resolve(&expression.ty);
    match &mut expression.kind {
        TypedExprKind::Call { callee, args, .. } => {
            resolve_typed_expr(ctx, callee);
            for arg in args { resolve_typed_expr(ctx, arg); }
        }
        TypedExprKind::Lambda { body, .. } => resolve_typed_expr(ctx, body),
        TypedExprKind::Match { scrutinee, arms } => {
            resolve_typed_expr(ctx, scrutinee);
            for arm in arms {
                if let Some(guard) = &mut arm.guard { resolve_typed_expr(ctx, guard); }
                resolve_typed_expr(ctx, &mut arm.body);
            }
        }
        TypedExprKind::Composite { children, .. } => {
            for child in children { resolve_typed_expr(ctx, child); }
        }
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) | TypedExprKind::Unresolved(_) => {}
    }
}

/// Generalize a clause/group type relative to the ambient environment. This
/// is called once per group *after* the whole group (or its recursive SCC)
/// has been inferred — never per clause.
pub fn generalize_group(env: &TypeEnv, ty: &MonoType, constraints: Vec<SchemeConstraint>) -> TypeScheme {
    generalize(env, ty, constraints)
}
