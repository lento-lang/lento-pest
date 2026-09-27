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

use crate::ast::{BinaryOp, Expr, FnDecl, Lit, PatKind, Pattern, RecordValueEntry, UnaryOp};
use crate::resolve::{resolve_call, Resolution};
use crate::semantics::FunctionGroup;
use crate::specialize::OverloadSet;
use crate::types::{
    generalize, instantiate, unify, MonoSumAlt, MonoType, SchemeConstraint, Substitution, TypeEnv, TypeScheme,
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
    NoOverload { name: String, arguments: Vec<MonoType> },
    AmbiguousOverload { name: String, arguments: Vec<MonoType> },
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
            TypeErrorKind::NoOverload { name, arguments } => {
                write!(f, "no overload of `{name}` accepts arguments {arguments:?}")
            }
            TypeErrorKind::AmbiguousOverload { name, arguments } => {
                write!(f, "ambiguous overload of `{name}` for arguments {arguments:?}")
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

/// Syntactic values are safe to generalize under the ML value restriction.
pub(crate) fn is_value(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(_) | Expr::Var(_) | Expr::Lambda(_) => true,
        Expr::Tuple(tuple) => tuple.items.iter().all(is_value),
        Expr::List(list) => {
            let mut current = list;
            while let crate::ast::ListExpr::Cells(cell) = current {
                if !is_value(&cell.head) {
                    return false;
                }
                current = &cell.tail;
            }
            true
        }
        Expr::Record(record) => record.entries.iter().all(|entry| match entry {
            RecordValueEntry::Field(_, value) | RecordValueEntry::Spread(value) => is_value(value),
        }),
        _ => false,
    }
}

/// The inference context: a substitution, a fresh-variable supply, and the
/// collected constraints.
pub struct InferCtx {
    pub supply: TypeVarSupply,
    pub subst: Substitution,
    pub constraints: Vec<SchemeConstraint>,
    /// Constraints waiting for annotations or later inference to make their
    /// type arguments concrete.
    pub pending_constraints: Vec<SchemeConstraint>,
    pub type_declarations: BTreeMap<String, (Vec<String>, crate::ast::Ty)>,
    /// Overload sets available while inferring later declarations and calls.
    pub overloads: BTreeMap<String, OverloadSet>,
}

impl InferCtx {
    pub fn new() -> Self {
        InferCtx {
            supply: TypeVarSupply::new(),
            subst: Substitution::new(),
            constraints: Vec::new(),
            pending_constraints: Vec::new(),
            type_declarations: BTreeMap::new(),
            overloads: BTreeMap::new(),
        }
    }

    fn fresh(&mut self) -> MonoType {
        self.supply.fresh()
    }

    pub(crate) fn unify(&mut self, a: &MonoType, b: &MonoType) -> Result<(), TypeError> {
        Ok(unify(&mut self.subst, a, b)?)
    }

    /// Resolve a type through the current substitution.
    pub fn resolve(&self, ty: &MonoType) -> MonoType {
        self.subst.apply(ty)
    }

    pub fn register_type_declaration(
        &mut self,
        name: String,
        parameters: Vec<String>,
        source: crate::ast::Ty,
    ) {
        self.type_declarations.insert(name, (parameters, source));
    }

    pub fn lower_surface_ty(
        &self,
        ty: &crate::ast::Ty,
        binders: &BTreeMap<String, MonoType>,
    ) -> MonoType {
        crate::types::lower_surface_ty(ty, binders, &self.type_declarations)
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

    env.insert("print".to_string(), poly(vec![a], unary(var(a), ctor::unit())));
    env.insert("println".to_string(), poly(vec![a], unary(var(a), ctor::unit())));
    env.insert("typeof".to_string(), poly(vec![a], unary(var(a), ctor::str())));
    env.insert("assert".to_string(), mono(unary(ctor::bool(), ctor::unit())));
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
    for (name, body) in [
        ("__int_add", binary(ctor::int(), ctor::int(), ctor::int())),
        ("__float_add", binary(ctor::float(), ctor::float(), ctor::float())),
        ("__int_sub", binary(ctor::int(), ctor::int(), ctor::int())),
        ("__float_sub", binary(ctor::float(), ctor::float(), ctor::float())),
        ("__int_mul", binary(ctor::int(), ctor::int(), ctor::int())),
        ("__float_mul", binary(ctor::float(), ctor::float(), ctor::float())),
        ("__int_div", binary(ctor::int(), ctor::int(), ctor::int())),
        ("__float_div", binary(ctor::float(), ctor::float(), ctor::float())),
        ("__int_mod", binary(ctor::int(), ctor::int(), ctor::int())),
        ("__int_abs", unary(ctor::int(), ctor::int())),
        ("__float_abs", unary(ctor::float(), ctor::float())),
        ("__int_equal", binary(ctor::int(), ctor::int(), ctor::bool())),
        ("__float_equal", binary(ctor::float(), ctor::float(), ctor::bool())),
        ("__bool_equal", binary(ctor::bool(), ctor::bool(), ctor::bool())),
        ("__str_equal", binary(ctor::str(), ctor::str(), ctor::bool())),
        ("__str_concat", binary(ctor::str(), ctor::str(), ctor::str())),
        ("__str_contains", binary(ctor::str(), ctor::str(), ctor::bool())),
        ("__int_to_string", unary(ctor::int(), ctor::str())),
        ("__float_to_string", unary(ctor::float(), ctor::str())),
        ("__bool_to_string", unary(ctor::bool(), ctor::str())),
        ("__str_to_string", unary(ctor::str(), ctor::str())),
        ("__bool_assert", unary(ctor::bool(), ctor::unit())),
    ] {
        env.insert(name.to_string(), mono(body));
    }
    for (name, body) in [
        ("__list_concat", binary(list(var(a)), list(var(a)), list(var(a)))),
        ("__list_contains", binary(list(var(a)), var(a), ctor::bool())),
        ("__list_take", binary(ctor::int(), list(var(a)), list(var(a)))),
        ("__list_drop", binary(ctor::int(), list(var(a)), list(var(a)))),
        ("__list_reverse", unary(list(var(a)), list(var(a)))),
        ("__list_slice", unary(ctor::int(), unary(ctor::int(), unary(list(var(a)), list(var(a)))))),
    ] {
        env.insert(name.to_string(), poly(vec![a], body));
    }
    for (name, body) in [
        ("__str_take", binary(ctor::int(), ctor::str(), ctor::str())),
        ("__str_drop", binary(ctor::int(), ctor::str(), ctor::str())),
        ("__str_reverse", unary(ctor::str(), ctor::str())),
        ("__str_slice", unary(ctor::int(), unary(ctor::int(), unary(ctor::str(), ctor::str())))),
    ] {
        env.insert(name.to_string(), mono(body));
    }
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
        let ann = ctx.lower_surface_ty(annotation, &BTreeMap::new());
        ctx.unify(expected, &ann)?;
    }
    match &pat.kind {
        PatKind::Var(name) => {
            let binding = pat
                .annotation
                .as_ref()
                .map(|annotation| ctx.lower_surface_ty(annotation, &BTreeMap::new()))
                .unwrap_or_else(|| expected.clone());
            env.insert(name.clone(), TypeScheme::mono(binding));
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
                if let PatKind::Spread(name) = &p.kind {
                    env.insert(
                        name.clone(),
                        TypeScheme::mono(MonoType::List(Box::new(elem.clone()))),
                    );
                } else {
                    check_pattern(ctx, p, &elem, env)?;
                }
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
            let mut field_tys = Vec::new();
            for f in fields {
                let ft = ctx.fresh();
                check_pattern(ctx, &f.pattern, &ft, env)?;
                field_tys.push((f.name.clone(), ft));
            }
            let row = rest.as_ref().map(|_| ctx.supply.fresh_id());
            let rec = MonoType::Record {
                fields: field_tys,
                rest: row,
            };
            ctx.unify(expected, &rec)?;
            if let Some(rest) = rest {
                env.insert(
                    rest.clone(),
                    TypeScheme::mono(MonoType::Record {
                        fields: Vec::new(),
                        rest: row,
                    }),
                );
            }
            Ok(())
        }
    }
}

// --------------------------------------------------------------------------
// Expression inference
// --------------------------------------------------------------------------

/// Infer an expression and retain annotations for every nested expression.
fn infer_list_element_type(ctx: &mut InferCtx, types: &[MonoType]) -> Result<MonoType, TypeError> {
    let element = ctx.fresh();
    let snapshot = ctx.subst.clone();
    let mut compatible = true;
    for ty in types {
        if ctx.unify(&element, ty).is_err() {
            compatible = false;
            break;
        }
    }
    if compatible {
        return Ok(ctx.resolve(&element));
    }
    ctx.subst = snapshot;

    let mut alternatives = Vec::new();
    for ty in types {
        let ty = ctx.resolve(ty);
        if !alternatives.contains(&ty) {
            alternatives.push(ty);
        }
    }
    if alternatives.len() == 1 {
        return Ok(alternatives.remove(0));
    }
    Ok(MonoType::Sum {
        name: "<list-union>".to_string(),
        args: Vec::new(),
        alts: alternatives.into_iter().map(MonoSumAlt::Bare).collect(),
    })
}

/// Gather a curried application before choosing an overload.
fn applied_call<'a>(expr: &'a Expr, arguments: &mut Vec<&'a Expr>) -> Option<&'a str> {
    match expr {
        Expr::Var(var) => Some(&var.name),
        Expr::Call(call) => {
            let name = applied_call(&call.callee, arguments)?;
            arguments.extend(call.args.iter());
            Some(name)
        }
        _ => None,
    }
}

fn callable_arity(ty: &MonoType) -> usize {
    match ty {
        MonoType::Function(_, result) => 1 + callable_arity(result),
        _ => 0,
    }
}

fn infer_overloaded_call(
    ctx: &mut InferCtx,
    expr: &Expr,
    env: &TypeEnv,
) -> Result<Option<crate::semantics::TypedExpr>, TypeError> {
    use crate::semantics::{TypedExpr, TypedExprKind};

    let mut source_arguments = Vec::new();
    let Some(name) = applied_call(expr, &mut source_arguments) else {
        return Ok(None);
    };
    let Some(set) = ctx.overloads.get(name).cloned() else {
        return Ok(None);
    };
    if !set.specializations.iter().any(|specialization| {
        callable_arity(&specialization.scheme.body) == source_arguments.len()
    }) {
        return Ok(None); // Partial applications retain their function type.
    }

    let mut arguments = Vec::with_capacity(source_arguments.len());
    for argument in source_arguments {
        arguments.push(infer_typed_expr(ctx, argument, &mut env.clone())?);
    }
    let argument_types = arguments.iter().map(|arg| ctx.resolve(&arg.ty)).collect::<Vec<_>>();
    let selected = match resolve_call(&mut ctx.supply, &set, &argument_types, None) {
        Resolution::Selected(id) => id,
        Resolution::NoMatch { .. } => return Err(TypeError { kind: TypeErrorKind::NoOverload {
            name: name.to_string(), arguments: argument_types,
        } }),
        Resolution::Ambiguous { .. } => return Err(TypeError { kind: TypeErrorKind::AmbiguousOverload {
            name: name.to_string(), arguments: argument_types,
        } }),
    };
    let (signature, constraints) = instantiate(&mut ctx.supply, &set.specializations[selected].scheme);
    let mut result = signature.clone();
    for argument in &arguments {
        let MonoType::Function(parameter, output) = result.clone() else {
            return Err(TypeError { kind: TypeErrorKind::NoOverload {
                name: name.to_string(), arguments: argument_types,
            } });
        };
        unify_call_argument(ctx, &argument.ty, &parameter)?;
        result = *output;
    }
    ctx.constraints.extend(constraints.clone());
    ctx.pending_constraints.extend(constraints);
    Ok(Some(TypedExpr {
        ty: ctx.resolve(&result),
        kind: TypedExprKind::Call {
            callee: Box::new(TypedExpr {
                ty: ctx.resolve(&signature),
                kind: TypedExprKind::Var(name.to_string()),
            }),
            args: arguments,
            specialization: Some(selected),
        },
    }))
}

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
                ctx.constraints.extend(constraints.clone());
                ctx.pending_constraints.extend(constraints);
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
                if let PatKind::Var(name) = &p.kind {
                    ctx.mutable_places.insert(name.clone(), true);
                }
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
            if let Some(overloaded) = infer_overloaded_call(ctx, expr, env)? {
                return Ok(overloaded);
            }
            let callee = infer_typed_expr(ctx, &c.callee, env)?;
            let mut result = callee.ty.clone();
            let mut args = Vec::with_capacity(c.args.len());
            for arg in &c.args {
                let arg = infer_typed_expr(ctx, arg, env)?;
                let ret = ctx.fresh();
                let expected = MonoType::Function(Box::new(arg.ty.clone()), Box::new(ret.clone()));
                match ctx.resolve(&result) {
                    MonoType::Function(input, output) => {
                        unify_call_argument(ctx, &arg.ty, &input)?;
                        ctx.unify(&output, &ret)?;
                    }
                    _ => ctx.unify(&result, &expected)?,
                }
                result = ret;
                args.push(arg);
            }
            validate_intrinsic_call(ctx, &callee, &args)?;
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
            let mut current = l;
            let mut children = Vec::new();
            loop {
                match current {
                    crate::ast::ListExpr::Empty => break,
                    crate::ast::ListExpr::Cells(cell) => {
                        let head = infer_typed_expr(ctx, &cell.head, env)?;
                        children.push(head);
                        current = &cell.tail;
                    }
                }
            }
            let element_types = children
                .iter()
                .map(|child| child.ty.clone())
                .collect::<Vec<_>>();
            let element = infer_list_element_type(ctx, &element_types)?;
            Ok(composite(MonoType::List(Box::new(element)), children))
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
                        let pending_start = ctx.pending_constraints.len();
                        let recursive = if let PatKind::Var(name) = &binding.pattern.kind {
                            let ty = ctx.fresh();
                            local.insert(name.clone(), TypeScheme::mono(ty.clone()));
                            Some(ty)
                        } else {
                            None
                        };
                        let value = infer_typed_expr(ctx, &binding.value, &mut local)?;
                        if let Some(recursive) = recursive {
                            ctx.unify(&recursive, &value.ty)?;
                        }
                        if let Some(annotation) = &binding.annotation {
                            let annotation = ctx.lower_surface_ty(annotation, &BTreeMap::new());
                            ctx.unify(&value.ty, &annotation)?;
                        }
                        check_pattern(ctx, &binding.pattern, &value.ty, &mut local)?;
                        let _pending = &ctx.pending_constraints[pending_start..];
                        children.push(value);
                    }
                    _ => {}
                }
            }
            Ok(composite(last, children))
        }
        Expr::Match(m) => {
            let scrutinee = infer_typed_expr(ctx, &m.scrutinee, env)?;
            let scrutinee = infer_match_scrutinee(ctx, scrutinee, &m.arms);
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
            let mut rest = None;
            let mut children = Vec::new();
            for entry in &r.entries {
                match entry {
                    RecordValueEntry::Field(name, expression) => {
                        let field = infer_typed_expr(ctx, expression, env)?;
                        fields.push((name.clone(), field.ty.clone()));
                        children.push(field);
                    }
                    RecordValueEntry::Spread(expression) => {
                        let spread = infer_typed_expr(ctx, expression, env)?;
                        match ctx.resolve(&spread.ty) {
                            MonoType::Record {
                                fields: spread_fields,
                                rest: spread_rest,
                            } => {
                                fields.extend(spread_fields);
                                rest = spread_rest;
                            }
                            other => {
                                return Err(TypeError {
                                    kind: TypeErrorKind::BadMember {
                                        ty: other,
                                        field: "record spread".to_string(),
                                    },
                                });
                            }
                        }
                        children.push(spread);
                    }
                }
            }
            Ok(composite(
                MonoType::Record {
                    fields,
                    rest,
                },
                children,
            ))
        }
        Expr::Member(m) => {
            let object = infer_typed_expr(ctx, &m.obj, env)?;
            if m.field == "len" {
                match ctx.resolve(&object.ty) {
                    MonoType::List(_) | MonoType::Tuple(_) => {
                        return Ok(composite(ctor::int(), vec![object]));
                    }
                    MonoType::Var(_) => {
                        let element = ctx.fresh();
                        ctx.unify(&object.ty, &MonoType::List(Box::new(element)))?;
                        return Ok(composite(ctor::int(), vec![object]));
                    }
                    _ => {}
                }
            }
            let ty = if let Some(field) = find_record_field(ctx, &object.ty, &m.field) {
                field
            } else {
                let field = ctx.fresh();
                let row = ctx.supply.fresh_id();
                ctx.unify(
                    &object.ty,
                    &MonoType::Record {
                        fields: vec![(m.field.clone(), field.clone())],
                        rest: Some(row),
                    },
                )?;
                field
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

/// Call arguments may be wider than closed record parameters.  The runtime
/// projects such arguments at the method boundary; inference only needs to
/// check the fields required by the parameter.
fn unify_call_argument(
    ctx: &mut InferCtx,
    actual: &MonoType,
    expected: &MonoType,
) -> Result<(), TypeError> {
    let actual = ctx.resolve(actual);
    let expected = ctx.resolve(expected);
    match (actual, expected) {
        (
            MonoType::Record {
                fields: actual_fields,
                ..
            },
            MonoType::Record {
                fields: expected_fields,
                rest: None,
            },
        ) => {
            for (name, expected_ty) in &expected_fields {
                let Some((_, actual_ty)) = actual_fields.iter().find(|(field, _)| field == name) else {
                    return ctx.unify(
                        &MonoType::Record {
                            fields: actual_fields,
                            rest: None,
                        },
                        &MonoType::Record {
                            fields: expected_fields,
                            rest: None,
                        },
                    );
                };
                ctx.unify(actual_ty, expected_ty)?;
            }
            Ok(())
        }
        (actual, expected) => ctx.unify(&actual, &expected),
    }
}

fn infer_match_scrutinee(
    ctx: &mut InferCtx,
    scrutinee: crate::semantics::TypedExpr,
    arms: &[crate::ast::MatchArm],
) -> crate::semantics::TypedExpr {
    if !matches!(ctx.resolve(&scrutinee.ty), MonoType::Var(_)) {
        return scrutinee;
    }
    let alternatives = arms
        .iter()
        .filter_map(|arm| arm.pattern.annotation.as_ref())
        .map(|ty| ctx.lower_surface_ty(ty, &BTreeMap::new()))
        .collect::<Vec<_>>();
    if alternatives.len() < 2 {
        return scrutinee;
    }
    let mut unique = Vec::new();
    for ty in alternatives {
        if !unique.contains(&ty) {
            unique.push(ty);
        }
    }
    if unique.len() >= 2 {
        let sum = MonoType::Sum {
            name: "<match>".to_string(),
            args: Vec::new(),
            alts: unique.into_iter().map(MonoSumAlt::Bare).collect(),
        };
        let _ = ctx.unify(&scrutinee.ty, &sum);
    }
    scrutinee
}

fn find_record_field(ctx: &InferCtx, ty: &MonoType, field: &str) -> Option<MonoType> {
    match ctx.resolve(ty) {
        MonoType::Record { fields, rest } => fields
            .into_iter()
            .find(|(name, _)| name == field)
            .map(|(_, ty)| ty)
            .or_else(|| rest.and_then(|row| find_record_field(ctx, &MonoType::Var(row), field))),
        _ => None,
    }
}

fn validate_intrinsic_call(
    ctx: &InferCtx,
    callee: &crate::semantics::TypedExpr,
    args: &[crate::semantics::TypedExpr],
) -> Result<(), TypeError> {
    let Some((name, all_args)) = flatten_typed_call(callee, args) else {
        return Ok(());
    };
    if all_args
        .iter()
        .any(|arg| matches!(ctx.resolve(&arg.ty), MonoType::Var(_)))
    {
        return Ok(());
    }
    let expected = match name.as_str() {
        "abs" if all_args.len() == 1 => matches!(ctx.resolve(&all_args[0].ty), MonoType::Constructor(kind, _) if kind == "int" || kind == "float"),
        "concat" if all_args.len() == 2 => match (ctx.resolve(&all_args[0].ty), ctx.resolve(&all_args[1].ty)) {
            (MonoType::Constructor(left, _), MonoType::Constructor(right, _)) => left == "str" && right == "str",
            (MonoType::List(left), MonoType::List(right)) => left == right,
            _ => false,
        },
        "contains" if all_args.len() == 2 => match (ctx.resolve(&all_args[0].ty), ctx.resolve(&all_args[1].ty)) {
            (MonoType::Constructor(left, _), MonoType::Constructor(right, _)) => left == "str" && right == "str",
            (MonoType::List(element), needle) => *element == needle,
            _ => false,
        },
        "take" | "drop" if all_args.len() == 2 => matches!(ctx.resolve(&all_args[0].ty), MonoType::Constructor(kind, _) if kind == "int")
            && (matches!(ctx.resolve(&all_args[1].ty), MonoType::Constructor(kind, _) if kind == "str")
                || matches!(ctx.resolve(&all_args[1].ty), MonoType::List(_))),
        "reverse" if all_args.len() == 1 => matches!(ctx.resolve(&all_args[0].ty), MonoType::Constructor(kind, _) if kind == "str")
            || matches!(ctx.resolve(&all_args[0].ty), MonoType::List(_)),
        "slice" if all_args.len() == 3 => all_args[..2]
            .iter()
            .all(|arg| matches!(ctx.resolve(&arg.ty), MonoType::Constructor(kind, _) if kind == "int"))
            && (matches!(ctx.resolve(&all_args[2].ty), MonoType::Constructor(kind, _) if kind == "str")
                || matches!(ctx.resolve(&all_args[2].ty), MonoType::List(_))),
        _ => true,
    };
    if expected {
        Ok(())
    } else {
        Err(TypeError {
            kind: TypeErrorKind::BadOperator {
                op: name.to_string(),
                ty: all_args.last().map(|arg| ctx.resolve(&arg.ty)).unwrap_or_else(ctor::unit),
            },
        })
    }
}

fn flatten_typed_call(
    callee: &crate::semantics::TypedExpr,
    args: &[crate::semantics::TypedExpr],
) -> Option<(String, Vec<crate::semantics::TypedExpr>)> {
    match &callee.kind {
        crate::semantics::TypedExprKind::Var(name) => Some((name.clone(), args.to_vec())),
        crate::semantics::TypedExprKind::Call { callee, args: prior, .. } => {
            let (name, mut all_args) = flatten_typed_call(callee, prior)?;
            all_args.extend_from_slice(args);
            Some((name, all_args))
        }
        _ => None,
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
        if let PatKind::Var(name) = &p.kind {
            // Function parameters are local cells in the evaluator. Their
            // annotations/specs determine which callers may provide a place.
            ctx.mutable_places.insert(name.clone(), true);
        }
        param_tys.push(pi);
    }
    let body = infer_typed_expr(ctx, &clause.body, &mut local)?;
    let result_ty = match &clause.ret {
        Some(ret) => {
            let declared = ctx.lower_surface_ty(ret, &BTreeMap::new());
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
