use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::{
    BinaryOp, BlockExpr, Decl, Expr, FnDecl, LambdaExpr, LetDecl, Lit, MatchArm, MatchExpr,
    PatKind, Pattern, Program, RecordValueExpr, Span, Stmt, SumAlt, Ty, TupleExpr, UnaryOp,
    VarExpr,
};
use crate::intrinsics::{apply_intrinsic, install_intrinsics, Intrinsic};

pub type CellRef = Rc<RefCell<Value>>;
pub type Env = HashMap<String, Binding>;

#[derive(Debug, Clone)]
pub enum Binding {
    Inline(Value),
    Cell { value: CellRef, mutable: bool },
    /// A nullary or unary constructor introduced by a `type ... = [Name t | ...]`
    /// declaration. `has_payload` distinguishes `Some` from `None`.
    Constructor { tag: String, has_payload: bool },
    /// A `type` declaration usable at runtime for typed-pattern checks.
    TypeDef { params: Vec<String>, ty: Ty },
    Methods(Vec<MethodBinding>),
}

#[derive(Debug, Clone)]
pub struct MethodBinding {
    pub target: Vec<Ty>,
    pub arity: usize,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub enum Value {
    Unit,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    Tuple(Vec<Value>),
    List(Vec<Value>),
    Record(HashMap<String, Value>),
    /// A constructor-tagged sum value: `Some 5` -> tag "Some", payload `5`.
    /// Bare sum alternatives (`type X = int | str`) stay untagged.
    Sum { tag: String, payload: Rc<Value> },
    Closure(Rc<Closure>),
    Intrinsic(Intrinsic),
    Ref(CellRef),
}

#[derive(Debug, Clone)]
pub struct Closure {
    params: Vec<Pattern>,
    body: Expr,
    env: Env,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Bool(v) => write!(f, "{v}"),
            Value::Int(v) => write!(f, "{v}"),
            Value::Float(v) => write!(f, "{v}"),
            Value::Str(v) => write!(f, "{v}"),
            Value::Tuple(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
            Value::List(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, "]")
            }
            Value::Record(fields) => {
                let mut keys: Vec<_> = fields.keys().collect();
                keys.sort();
                write!(f, "{{")?;
                for (i, key) in keys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", key, fields[*key])?;
                }
                write!(f, "}}")
            }
            Value::Sum { tag, payload } => {
                if matches!(**payload, Value::Unit) {
                    write!(f, "{tag}")
                } else {
                    write!(f, "{tag}({payload})")
                }
            }
            Value::Closure(_) => write!(f, "<closure>"),
            Value::Intrinsic(intrinsic) => write!(f, "<intrinsic:{}>", intrinsic.name),
            Value::Ref(_) => write!(f, "<ref>"),
        }
    }
}

pub fn eval_program_with_declarations(
    program: &Program,
    declarations: &crate::analysis::DeclarationMetadata,
) -> Result<Value, String> {
    let mut env = initial_env();
    install_resolved_declarations(declarations, &mut env);
    let mut statements = Vec::new();
    let mut spans = Vec::new();
    for (index, statement) in program.statements.iter().enumerate() {
        if matches!(statement, Stmt::Decl(Decl::Type(_))) {
            continue;
        }
        statements.push(statement.clone());
        spans.push(
            program
                .spans
                .get(index)
                .copied()
                .unwrap_or(crate::ast::Span { line: 0, col: 0 }),
        );
    }
    let runtime_program = Program { statements, spans };
    eval_program_in_env(&runtime_program, &mut env)
}

fn install_resolved_declarations(
    declarations: &crate::analysis::DeclarationMetadata,
    env: &mut Env,
) {
    for declaration in &declarations.types {
        env.insert(
            declaration.name.clone(),
            Binding::TypeDef {
                params: declaration.parameters.clone(),
                ty: declaration.source.clone(),
            },
        );
        for constructor in &declaration.constructors {
            env.insert(
                constructor.name.clone(),
                Binding::Constructor {
                    tag: constructor.name.clone(),
                    has_payload: constructor.payload.is_some(),
                },
            );
        }
    }
}

pub fn initial_env() -> Env {
    let mut env = Env::new();
    install_intrinsics(&mut env);
    env
}

pub fn eval_program_in_env(program: &Program, env: &mut Env) -> Result<Value, String> {
    let program = prepare_runtime_program(program);
    let mut last = Value::Unit;
    for stmt in &program.statements {
        last = eval_stmt(stmt, env)?;
    }
    Ok(last)
}

fn prepare_runtime_program(program: &Program) -> Program {
    let mut statements = Vec::with_capacity(program.statements.len());
    let mut spans = Vec::with_capacity(program.spans.len());
    let mut index = 0;
    while index < program.statements.len() {
        let Stmt::Decl(Decl::Fn(first)) = &program.statements[index] else {
            statements.push(program.statements[index].clone());
            spans.push(program.spans.get(index).copied().unwrap_or(Span { line: 0, col: 0 }));
            index += 1;
            continue;
        };

        let name = first.name.clone();
        let arity = first.params.len();
        let mut clauses = vec![(first.params.clone(), first.body.clone())];
        let mut end = index + 1;
        while end < program.statements.len() {
            let Stmt::Decl(Decl::Fn(next)) = &program.statements[end] else { break };
            if next.name != name || next.params.len() != arity { break; }
            clauses.push((next.params.clone(), next.body.clone()));
            end += 1;
        }
        let let_decl = if clauses.len() == 1 {
            FnDecl {
                name: name.clone(),
                params: clauses[0].0.clone(),
                ret: first.ret.clone(),
                body: clauses[0].1.clone(),
            }.desugar()
        } else {
            grouped_runtime_fn(name, clauses)
        };
        statements.push(Stmt::Decl(Decl::Let(let_decl)));
        spans.push(program.spans.get(index).copied().unwrap_or(Span { line: 0, col: 0 }));
        index = end;
    }
    Program { statements, spans }
}

fn grouped_runtime_fn(name: String, clauses: Vec<(Vec<Pattern>, Expr)>) -> LetDecl {
    let arity = clauses[0].0.len();
    let bind: Vec<String> = (0..arity)
        .map(|index| match clauses[0].0[index].kind {
            PatKind::Var(ref name) => name.clone(),
            _ => format!("__l{name}{index}"),
        })
        .collect();
    let scrutinee = if arity == 1 {
        Expr::Var(VarExpr { name: bind[0].clone() })
    } else {
        Expr::Tuple(TupleExpr {
            items: bind.iter().map(|name| Expr::Var(VarExpr { name: name.clone() })).collect(),
        })
    };
    let arms = clauses.into_iter().map(|(params, body)| MatchArm {
        pattern: if params.len() == 1 {
            params.into_iter().next().unwrap()
        } else {
            Pattern { annotation: None, kind: PatKind::Tuple(params) }
        },
        guard: None,
        body: Box::new(body),
    }).collect();
    let mut value = Expr::Match(MatchExpr { scrutinee: Box::new(scrutinee), arms });
    for name in bind.iter().rev() {
        value = Expr::Lambda(LambdaExpr {
            params: vec![Pattern { annotation: None, kind: PatKind::Var(name.clone()) }],
            body: Box::new(value),
        });
    }
    LetDecl {
        mutable: false,
        pattern: Pattern { annotation: None, kind: PatKind::Var(name) },
        annotation: None,
        value,
    }
}

fn eval_stmt(stmt: &Stmt, env: &mut Env) -> Result<Value, String> {
    match stmt {
        Stmt::Decl(decl) => eval_decl(decl, env),
        Stmt::Expr(expr) => eval_expr(expr, env),
    }
}

fn eval_decl(decl: &Decl, env: &mut Env) -> Result<Value, String> {
    match decl {
        Decl::Class(_) => Ok(Value::Unit),
        Decl::Impl(i) => {
            for method in &i.methods {
                let let_decl = method.clone().desugar();
                let previous = env.get(&method.name).cloned();
                eval_method_decl(&let_decl, env)?;
                let value = match env.remove(&method.name) {
                    Some(Binding::Inline(value)) => value,
                    Some(Binding::Cell { value, .. }) => value.borrow().clone(),
                    Some(_) => return Err(format!("impl method '{}' is not a value", method.name)),
                    None => return Err(format!("impl method '{}' was not bound", method.name)),
                };
                if let Some(previous) = previous {
                    env.insert(method.name.clone(), previous);
                } else {
                    env.remove(&method.name);
                }
                let method_binding = MethodBinding {
                    target: i.target.clone(),
                    arity: method.params.len(),
                    value,
                };
                let existing = env.remove(&method.name);
                match existing {
                    Some(Binding::Methods(mut methods)) => {
                        methods.push(method_binding);
                        env.insert(method.name.clone(), Binding::Methods(methods));
                    }
                    Some(_) => {
                        env.insert(method.name.clone(), Binding::Methods(vec![method_binding]));
                    }
                    None => {
                        env.insert(method.name.clone(), Binding::Methods(vec![method_binding]));
                    }
                }
            }
            Ok(Value::Unit)
        }
        Decl::Spec(_) => Ok(Value::Unit),
        Decl::Type(t) => {
            install_type_decl(t, env);
            Ok(Value::Unit)
        }
        Decl::Fn(_) => Err("unexpected fn declaration at evaluation time; desugar first".into()),
        Decl::Let(let_decl) => eval_let_decl(let_decl, env),
        Decl::Mod(_) | Decl::Use(_) => Ok(Value::Unit),
    }
}

/// Install the runtime artifacts of a `type` declaration: constructor
/// bindings for each uppercase alternative and a `TypeDef` used by typed
/// patterns for runtime type tests.
fn install_type_decl(t: &crate::ast::TypeDecl, env: &mut Env) {
    if let Ty::Sum(alts) = &t.ty {
        for alt in alts {
            if let SumAlt::Ctor { name, payload } = alt {
                env.insert(
                    name.clone(),
                    Binding::Constructor {
                        tag: name.clone(),
                        has_payload: payload.is_some(),
                    },
                );
            }
        }
    }
    env.insert(
        t.name.clone(),
        Binding::TypeDef {
            params: t.params.clone(),
            ty: t.ty.clone(),
        },
    );
}

fn eval_let_decl(let_decl: &LetDecl, env: &mut Env) -> Result<Value, String> {
    if let PatKind::Var(name) = &let_decl.pattern.kind {
        if let_decl.mutable || binding_needs_cell(&let_decl.value) {
            let cell = Rc::new(RefCell::new(Value::Unit));
            env.insert(
                name.clone(),
                Binding::Cell {
                    value: cell.clone(),
                    mutable: let_decl.mutable,
                },
            );
            let value = eval_expr(&let_decl.value, env)?;
            *cell.borrow_mut() = value.clone();
            return Ok(value);
        }

        let value = eval_expr(&let_decl.value, env)?;
        env.insert(name.clone(), Binding::Inline(value.clone()));
        return Ok(value);
    }

    let value = eval_expr(&let_decl.value, env)?;
    bind_pattern(&let_decl.pattern, value.clone(), let_decl.mutable, env)?;
    Ok(value)
}

/// Impl methods are ordinary functions, but their definitions are not
/// recursive bindings.  Avoid installing a self-referential cell while
/// evaluating a method that delegates to a same-named intrinsic.
fn eval_method_decl(let_decl: &LetDecl, env: &mut Env) -> Result<Value, String> {
    if let PatKind::Var(name) = &let_decl.pattern.kind {
        let value = eval_expr(&let_decl.value, env)?;
        env.insert(name.clone(), Binding::Inline(value.clone()));
        Ok(value)
    } else {
        eval_let_decl(let_decl, env)
    }
}

fn eval_expr(expr: &Expr, env: &mut Env) -> Result<Value, String> {
    match expr {
        Expr::Lit(lit) => Ok(eval_lit(&lit.value)),
        Expr::Var(var) => lookup_var(env, &var.name),
        Expr::Ref(expr) => eval_ref(expr.inner.as_ref(), env),
        Expr::Assign(expr) => eval_assign(expr.place.as_ref(), expr.value.as_ref(), env),
        Expr::Lambda(lambda) => Ok(Value::Closure(Rc::new(Closure {
            params: lambda.params.clone(),
            body: (*lambda.body).clone(),
            env: env.clone(),
        }))),
        Expr::Call(call) => {
            if let Expr::Var(var) = call.callee.as_ref() {
                if let Some(Binding::Methods(methods)) = env.get(&var.name).cloned() {
                    let mut args = Vec::with_capacity(call.args.len());
                    for arg in &call.args {
                        args.push(eval_expr(arg, env)?);
                    }
                    let method = methods
                        .iter()
                        .find(|method| method_matches(&method.target, method.arity, &args, env))
                        .ok_or_else(|| format!("no matching method '{}'", var.name))?;
                    let args = args
                        .into_iter()
                        .zip(method.target.iter())
                        .map(|(value, ty)| coerce_value_to_type(value, ty))
                        .collect::<Result<Vec<_>, _>>()?;
                    return apply_call(method.value.clone(), args);
                }
            }
            // Constructor application: `Some 5` parses as a call whose callee
            // is a variable bound to a constructor.
            if let Expr::Var(var) = call.callee.as_ref() {
                if let Some(Binding::Constructor { tag, has_payload }) = env.get(&var.name) {
                    let tag = tag.clone();
                    let has_payload = *has_payload;
                    return eval_ctor_call(&tag, has_payload, &call.args, env);
                }
            }
            let callee = eval_expr(&call.callee, env)?;
            let mut args = Vec::with_capacity(call.args.len());
            for arg in &call.args {
                args.push(eval_expr(arg, env)?);
            }
            apply_call(callee, args)
        }
        Expr::Member(member) => {
            let value = eval_expr(&member.obj, env)?;
            eval_member(value, &member.field)
        }
        Expr::Index(index) => {
            let value = eval_expr(&index.obj, env)?;
            let at = eval_expr(&index.index, env)?;
            eval_index(value, at)
        }
        Expr::Unary(unary) => {
            let operand = eval_expr(&unary.operand, env)?;
            eval_unary(&unary.op, operand)
        }
        Expr::Binary(binary) => eval_binary(&binary.op, &binary.lhs, &binary.rhs, env),
        Expr::Tuple(tuple) => {
            let mut items = Vec::with_capacity(tuple.items.len());
            for item in &tuple.items {
                items.push(eval_expr(item, env)?);
            }
            Ok(Value::Tuple(items))
        }
        Expr::List(list) => eval_list(list, env),
        Expr::Record(record) => eval_record(record, env),
        Expr::Block(block) => eval_block(block, env),
        Expr::Match(match_expr) => {
            let scrutinee = eval_expr(&match_expr.scrutinee, env)?;
            eval_match(scrutinee, &match_expr.arms, env)
        }
    }
}

fn eval_ctor_call(
    tag: &str,
    has_payload: bool,
    args: &[Expr],
    env: &mut Env,
) -> Result<Value, String> {
    match (has_payload, args.len()) {
        (false, 0) => Ok(Value::Sum {
            tag: tag.to_string(),
            payload: Rc::new(Value::Unit),
        }),
        (true, 1) => {
            let payload = eval_expr(&args[0], env)?;
            Ok(Value::Sum {
                tag: tag.to_string(),
                payload: Rc::new(payload),
            })
        }
        (false, _) => Err(format!("constructor '{tag}' takes no arguments")),
        (true, n) => Err(format!("constructor '{tag}' expects 1 argument, got {n}")),
    }
}

fn eval_lit(lit: &Lit) -> Value {
    match lit {
        Lit::Bool(v) => Value::Bool(*v),
        Lit::Int(v) => Value::Int(*v),
        Lit::Float(v) => Value::Float(*v),
        Lit::Str(v) => Value::Str(v.clone()),
    }
}

fn eval_ref(expr: &Expr, env: &mut Env) -> Result<Value, String> {
    match expr {
        Expr::Var(var) => match env.get(&var.name) {
            Some(Binding::Cell { value, .. }) => Ok(Value::Ref(value.clone())),
            Some(Binding::Inline(_)) => Err(format!(
                "cannot take ref of immutable binding '{}'",
                var.name
            )),
            None => Err(format!("undefined variable '{}'", var.name)),
            _ => Err(format!("'{}' is not a mutable binding", var.name)),
        },
        _ => Err("ref currently supports only variable places".into()),
    }
}

fn eval_assign(place: &Expr, value_expr: &Expr, env: &mut Env) -> Result<Value, String> {
    let value = eval_expr(value_expr, env)?;
    match place {
        Expr::Var(var) => match env.get(&var.name) {
            Some(Binding::Cell {
                value: cell,
                mutable: true,
            }) => {
                *cell.borrow_mut() = value.clone();
                Ok(value)
            }
            Some(Binding::Cell { mutable: false, .. }) | Some(Binding::Inline(_)) => {
                Err(format!("cannot assign to immutable binding '{}'", var.name))
            }
            None => Err(format!("undefined variable '{}'", var.name)),
            _ => Err(format!("cannot assign to '{}'", var.name)),
        },
        _ => Err("assignment currently supports only variable places".into()),
    }
}

fn apply_call(callee: Value, args: Vec<Value>) -> Result<Value, String> {
    match callee {
        Value::Closure(closure) if closure.params.len() == args.len() => {
            let mut local_env = closure.env.clone();
            for (param, arg) in closure.params.iter().zip(args.into_iter()) {
                let arg = param
                    .annotation
                    .as_ref()
                    .map(|ty| coerce_value_to_type(arg.clone(), ty))
                    .transpose()?
                    .unwrap_or(arg);
                bind_pattern(param, arg, true, &mut local_env)?;
            }
            eval_expr(&closure.body, &mut local_env)
        }
        other => {
            let mut current = other;
            for arg in args {
                current = apply_one(current, arg)?;
            }
            Ok(current)
        }
    }
}

pub(crate) fn apply_one(callee: Value, arg: Value) -> Result<Value, String> {
    match callee {
        Value::Closure(closure) => {
            let mut local_env = closure.env.clone();
            let arg = closure.params[0]
                .annotation
                .as_ref()
                .map(|ty| coerce_value_to_type(arg.clone(), ty))
                .transpose()?
                .unwrap_or(arg);
            bind_pattern(&closure.params[0], arg, true, &mut local_env)?;
            if closure.params.len() == 1 {
                eval_expr(&closure.body, &mut local_env)
            } else {
                // Partial application: bind the first parameter and hand
                // back a closure carrying the remaining parameters and the
                // extended environment.
                Ok(Value::Closure(Rc::new(Closure {
                    params: closure.params[1..].to_vec(),
                    body: closure.body.clone(),
                    env: local_env,
                })))
            }
        }
        Value::Intrinsic(mut intrinsic) => {
            intrinsic.args.push(arg);
            if intrinsic.args.len() < intrinsic.arity {
                Ok(Value::Intrinsic(intrinsic))
            } else {
                apply_intrinsic(intrinsic)
            }
        }
        _ => Err(format!("cannot call non-function value {callee}")),
    }
}

fn eval_member(value: Value, field: &str) -> Result<Value, String> {
    match value {
        Value::List(items) if field == "len" => Ok(Value::Int(items.len() as i64)),
        Value::Tuple(items) if field == "len" => Ok(Value::Int(items.len() as i64)),
        Value::Str(text) if field == "len" => Ok(Value::Int(text.chars().count() as i64)),
        Value::Record(fields) => fields
            .get(field)
            .cloned()
            .ok_or_else(|| format!("record has no field '{field}'")),
        _ => Err(format!("cannot access field '{field}' on value {value}")),
    }
}

fn eval_index(value: Value, index: Value) -> Result<Value, String> {
    let idx = match index {
        Value::Int(v) if v >= 0 => v as usize,
        _ => return Err("index must be a non-negative integer".into()),
    };
    match value {
        Value::List(items) => items
            .get(idx)
            .cloned()
            .ok_or_else(|| format!("list index {idx} out of bounds")),
        Value::Tuple(items) => items
            .get(idx)
            .cloned()
            .ok_or_else(|| format!("tuple index {idx} out of bounds")),
        Value::Str(text) => text
            .chars()
            .nth(idx)
            .map(|c| Value::Str(c.to_string()))
            .ok_or_else(|| format!("string index {idx} out of bounds")),
        _ => Err(format!("cannot index value {value}")),
    }
}

fn eval_unary(op: &UnaryOp, operand: Value) -> Result<Value, String> {
    match op {
        UnaryOp::Not => match operand {
            Value::Bool(v) => Ok(Value::Bool(!v)),
            _ => Err("! expects a boolean".into()),
        },
        UnaryOp::Neg => match operand {
            Value::Int(v) => v
                .checked_neg()
                .map(Value::Int)
                .ok_or_else(|| "integer overflow in unary -".to_string()),
            Value::Float(v) => Ok(Value::Float(-v)),
            _ => Err("unary - expects a number".into()),
        },
    }
}

fn eval_binary(op: &BinaryOp, lhs: &Expr, rhs: &Expr, env: &mut Env) -> Result<Value, String> {
    match op {
        BinaryOp::And => match eval_expr(lhs, env)? {
            Value::Bool(false) => Ok(Value::Bool(false)),
            Value::Bool(true) => match eval_expr(rhs, env)? {
                Value::Bool(v) => Ok(Value::Bool(v)),
                _ => Err("&& expects boolean operands".into()),
            },
            _ => Err("&& expects boolean operands".into()),
        },
        BinaryOp::Or => match eval_expr(lhs, env)? {
            Value::Bool(true) => Ok(Value::Bool(true)),
            Value::Bool(false) => match eval_expr(rhs, env)? {
                Value::Bool(v) => Ok(Value::Bool(v)),
                _ => Err("|| expects boolean operands".into()),
            },
            _ => Err("|| expects boolean operands".into()),
        },
        _ => {
            let left = eval_expr(lhs, env)?;
            let right = eval_expr(rhs, env)?;
            eval_binary_values(op, left, right)
        }
    }
}

fn eval_binary_values(op: &BinaryOp, left: Value, right: Value) -> Result<Value, String> {
    match op {
        BinaryOp::Add => match (left, right) {
            (Value::Int(a), Value::Int(b)) => a
                .checked_add(b)
                .map(Value::Int)
                .ok_or_else(|| "integer overflow in +".to_string()),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            (Value::Int(a), Value::Float(b)) => Ok(Value::Float(a as f64 + b)),
            (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a + b as f64)),
            (Value::Str(a), Value::Str(b)) => Ok(Value::Str(a + &b)),
            (Value::List(mut a), Value::List(b)) => {
                a.extend(b);
                Ok(Value::List(a))
            }
            _ => Err("+ expects numbers, strings, or lists".into()),
        },
        BinaryOp::Sub => numeric_binop(left, right, |a, b| a.checked_sub(b), |a, b| a - b, "-"),
        BinaryOp::Mul => numeric_binop(left, right, |a, b| a.checked_mul(b), |a, b| a * b, "*"),
        BinaryOp::Div => numeric_binop(
            left,
            right,
            |a, b| a.checked_div(b),
            |a, b| a / b,
            "/",
        ),
        BinaryOp::Mod => match (left, right) {
            (Value::Int(a), Value::Int(b)) => a
                .checked_rem(b)
                .map(Value::Int)
                .ok_or_else(|| "integer error in %".to_string()),
            _ => Err("% expects integer operands".into()),
        },
        BinaryOp::Eq => Ok(Value::Bool(value_eq(&left, &right))),
        BinaryOp::Ne => Ok(Value::Bool(!value_eq(&left, &right))),
        BinaryOp::Lt => cmp_values(left, right, |o| o < 0),
        BinaryOp::Gt => cmp_values(left, right, |o| o > 0),
        BinaryOp::Le => cmp_values(left, right, |o| o <= 0),
        BinaryOp::Ge => cmp_values(left, right, |o| o >= 0),
        BinaryOp::And | BinaryOp::Or => unreachable!(),
    }
}

fn numeric_binop(
    left: Value,
    right: Value,
    int_op: impl FnOnce(i64, i64) -> Option<i64>,
    float_op: impl FnOnce(f64, f64) -> f64,
    op_name: &str,
) -> Result<Value, String> {
    match (left, right) {
        (Value::Int(a), Value::Int(b)) => int_op(a, b)
            .map(Value::Int)
            .ok_or_else(|| format!("integer error in {op_name}")),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(float_op(a, b))),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float(float_op(a as f64, b))),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(float_op(a, b as f64))),
        _ => Err("numeric operator expects number operands".into()),
    }
}

fn cmp_values(left: Value, right: Value, pred: impl FnOnce(i8) -> bool) -> Result<Value, String> {
    let ord = match (left, right) {
        (Value::Int(a), Value::Int(b)) => compare_i64(a, b),
        (Value::Float(a), Value::Float(b)) => compare_f64(a, b)?,
        (Value::Int(a), Value::Float(b)) => compare_f64(a as f64, b)?,
        (Value::Float(a), Value::Int(b)) => compare_f64(a, b as f64)?,
        (Value::Str(a), Value::Str(b)) => compare_i8(a.cmp(&b) as i32),
        _ => return Err("comparison expects comparable operands".into()),
    };
    Ok(Value::Bool(pred(ord)))
}

fn compare_i64(a: i64, b: i64) -> i8 {
    compare_i8(a.cmp(&b) as i32)
}

fn compare_f64(a: f64, b: f64) -> Result<i8, String> {
    if a < b {
        Ok(-1)
    } else if a > b {
        Ok(1)
    } else {
        Ok(0)
    }
}

fn compare_i8(value: i32) -> i8 {
    if value < 0 {
        -1
    } else if value > 0 {
        1
    } else {
        0
    }
}

fn eval_list(list: &crate::ast::ListExpr, env: &mut Env) -> Result<Value, String> {
    let mut items = Vec::new();
    let mut current = list;
    loop {
        match current {
            crate::ast::ListExpr::Empty => return Ok(Value::List(items)),
            crate::ast::ListExpr::Cells(cons) => {
                items.push(eval_expr(&cons.head, env)?);
                current = cons.tail.as_ref();
            }
        }
    }
}

fn eval_record(record: &RecordValueExpr, env: &mut Env) -> Result<Value, String> {
    use std::collections::HashMap;
    let mut fields: HashMap<String, Value> = HashMap::new();
    for entry in &record.entries {
        match entry {
            crate::ast::RecordValueEntry::Field(name, value) => {
                fields.insert(name.clone(), eval_expr(value, env)?);
            }
            crate::ast::RecordValueEntry::Spread(source) => {
                let value = eval_expr(source, env)?;
                match value {
                    Value::Record(mut src) => {
                        for (k, v) in src.drain() {
                            fields.insert(k, v);
                        }
                    }
                    other => {
                        return Err(format!(
                            "record spread expects a record, got {other}"
                        ));
                    }
                }
            }
        }
    }
    Ok(Value::Record(fields))
}

fn eval_block(block: &BlockExpr, env: &mut Env) -> Result<Value, String> {
    let mut local_env = env.clone();
    let mut last = Value::Unit;
    for stmt in &block.body {
        last = eval_stmt(stmt, &mut local_env)?;
    }
    Ok(last)
}

fn eval_match(scrutinee: Value, arms: &[MatchArm], env: &mut Env) -> Result<Value, String> {
    for arm in arms {
        let mut local_env = env.clone();
        if pattern_matches(&arm.pattern, &scrutinee, &mut local_env)? {
            if let Some(guard) = &arm.guard {
                match eval_expr(guard, &mut local_env)? {
                    Value::Bool(true) => return eval_expr(&arm.body, &mut local_env),
                    Value::Bool(false) => continue,
                    _ => return Err("match guard must evaluate to a boolean".into()),
                }
            }
            return eval_expr(&arm.body, &mut local_env);
        }
    }
    Err("non-exhaustive match".into())
}

fn bind_pattern(
    pattern: &Pattern,
    value: Value,
    mutable: bool,
    env: &mut Env,
) -> Result<(), String> {
    let mut binds = Vec::new();
    collect_pattern_bindings(pattern, &value, env, &mut binds)?;
    for (name, bound) in binds {
        env.insert(name, make_binding(bound, mutable));
    }
    Ok(())
}

fn pattern_matches(pattern: &Pattern, value: &Value, env: &mut Env) -> Result<bool, String> {
    let mut binds = Vec::new();
    if !collect_pattern_bindings(pattern, value, env, &mut binds)? {
        return Ok(false);
    }
    for (name, bound) in binds {
        env.insert(name, Binding::Inline(bound));
    }
    Ok(true)
}

fn make_binding(value: Value, mutable: bool) -> Binding {
    if mutable {
        Binding::Cell {
            value: Rc::new(RefCell::new(value)),
            mutable: true,
        }
    } else {
        Binding::Inline(value)
    }
}

fn binding_needs_cell(expr: &Expr) -> bool {
    matches!(expr, Expr::Lambda(_))
}

fn collect_pattern_bindings(
    pattern: &Pattern,
    value: &Value,
    env: &Env,
    out: &mut Vec<(String, Value)>,
) -> Result<bool, String> {
    // A typed pattern `(n : int)` performs a runtime type test before its
    // own shape matches; bare type sum alternatives are matched this way.
    if let Some(ty) = &pattern.annotation {
        if !value_matches_ty(value, ty, env) {
            return Ok(false);
        }
    }
    match &pattern.kind {
        PatKind::Var(name) => {
            // A bare uppercase identifier may name a nullary constructor
            // (`None`); in that case it matches instead of binding.
            if let Some(Binding::Constructor { tag, has_payload: false }) = env.get(name) {
                return Ok(matches!(value, Value::Sum { tag: vtag, .. } if vtag == tag));
            }
            out.push((name.clone(), value.clone()));
            Ok(true)
        }
        PatKind::Wildcard => Ok(true),
        PatKind::Lit(lit) => Ok(value_eq(value, &eval_lit(lit))),
        PatKind::Constructor { name, payload } => match value {
            Value::Sum { tag, payload: sum_payload } if tag == name => match payload {
                Some(pat) => collect_pattern_bindings(pat, sum_payload, env, out),
                None => Ok(matches!(**sum_payload, Value::Unit)),
            },
            _ => Ok(false),
        },
        PatKind::Tuple(items) => match value {
            Value::Tuple(values) if values.len() == items.len() => {
                for (pattern, value) in items.iter().zip(values.iter()) {
                    if !collect_pattern_bindings(pattern, value, env, out)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
        PatKind::List(items) => match value {
            Value::List(values) => {
                let spread_at = items
                    .iter()
                    .position(|pat| matches!(pat.kind, PatKind::Spread(_)));

                match spread_at {
                    Some(i) => {
                        if i + 1 != items.len() || values.len() < i {
                            return Ok(false);
                        }
                        for (pattern, value) in items[..i].iter().zip(values[..i].iter()) {
                            if !collect_pattern_bindings(pattern, value, env, out)? {
                                return Ok(false);
                            }
                        }
                        match &items[i].kind {
                            PatKind::Spread(name) => {
                                out.push((name.clone(), Value::List(values[i..].to_vec())));
                                Ok(true)
                            }
                            _ => Ok(false),
                        }
                    }
                    None if values.len() == items.len() => {
                        for (pattern, value) in items.iter().zip(values.iter()) {
                            if !collect_pattern_bindings(pattern, value, env, out)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    None => Ok(false),
                }
            }
            _ => Ok(false),
        },
        PatKind::Spread(name) => {
            out.push((name.clone(), value.clone()));
            Ok(true)
        }
        PatKind::Record { fields, rest } => match value {
            Value::Record(values) => {
                let mut remainder = values.clone();
                for field in fields {
                    let Some(field_value) = values.get(&field.name) else {
                        return Ok(false);
                    };
                    if !collect_pattern_bindings(&field.pattern, field_value, env, out)? {
                        return Ok(false);
                    }
                    remainder.remove(&field.name);
                }
                if let Some(rest) = rest {
                    out.push((rest.clone(), Value::Record(remainder)));
                }
                Ok(true)
            }
            _ => Ok(false),
        },
    }
}

fn lookup_var(env: &Env, name: &str) -> Result<Value, String> {
    match env.get(name) {
        Some(Binding::Inline(value)) => Ok(value.clone()),
        Some(Binding::Cell { value, .. }) => Ok(value.borrow().clone()),
        Some(Binding::Constructor { tag, has_payload: false }) => Ok(Value::Sum {
            tag: tag.clone(),
            payload: Rc::new(Value::Unit),
        }),
        Some(Binding::Constructor { tag, has_payload: true }) => Err(format!(
            "constructor '{tag}' expects one argument; use '{tag} value'"
        )),
        Some(Binding::TypeDef { .. }) => Err(format!("'{name}' is a type, not a value")),
        Some(Binding::Methods(_)) => Err(format!("method '{name}' requires a typed call")),
        None => Err(format!("undefined variable '{name}'")),
    }
}

fn method_matches(target: &[Ty], arity: usize, args: &[Value], env: &Env) -> bool {
    if target.is_empty() {
        return true;
    }
    if args.len() < arity {
        return target.len() == 1
            && (args.iter().any(|arg| value_matches_ty(arg, &target[0], env))
                || args.len() == 1);
    }
    if target.len() == args.len() {
        return target
            .iter()
            .zip(args)
            .all(|(ty, arg)| value_matches_ty(arg, ty, env));
    }
    target.len() == 1 && args.iter().any(|arg| value_matches_ty(arg, &target[0], env))
}

/// Runtime type test for typed patterns `(n : int)` / `(x : Option)`.
/// Builtin names check the value's shape; a user type name checks constructor
/// tag membership (for sums) or the declared record/list/tuple shape.
/// Unresolvable names (type variables) impose no runtime restriction.
fn value_matches_ty(value: &Value, ty: &Ty, env: &Env) -> bool {
    match ty {
        Ty::Named { name, args } => match name.as_str() {
            "int" => matches!(value, Value::Int(_)),
            "float" => matches!(value, Value::Float(_)),
            "bool" => matches!(value, Value::Bool(_)),
            "str" | "string" => matches!(value, Value::Str(_)),
            "unit" => matches!(value, Value::Unit),
            _ => match env.get(name) {
                Some(Binding::TypeDef { params, ty: decl }) => {
                    // A type parameter matches anything at runtime.
                    if params.contains(name) {
                        return true;
                    }
                    match decl {
                        Ty::Sum(alts) => match value {
                            Value::Sum { tag, .. } => alts.iter().any(|alt| {
                                matches!(alt, SumAlt::Ctor { name, .. } if name == tag)
                                    || matches!(alt, SumAlt::Row(_))
                            }),
                            other => alts.iter().any(|alt| {
                                matches!(alt, SumAlt::Bare(t) if value_matches_ty(other, t, env))
                                    || matches!(alt, SumAlt::Row(_))
                            }),
                        },
                        other => {
                            if args.len() != params.len() {
                                return true; // cannot substitute params at runtime
                            }
                            value_matches_ty_open(other, value, params, args, env)
                        }
                    }
                }
                _ => true, // unknown name: no runtime check
            },
        },
        Ty::List(elem) => match value {
            Value::List(items) => items.iter().all(|item| value_matches_ty(item, elem, env)),
            _ => false,
        },
        Ty::Tuple(elems) => match value {
            Value::Tuple(items) => {
                items.len() == elems.len()
                    && items.iter().zip(elems.iter()).all(|(v, t)| value_matches_ty(v, t, env))
            }
            _ => false,
        },
        Ty::RecordType(fields) => match value {
            Value::Record(fs) => fields.iter().all(|(name, t)| {
                fs.get(name).map(|v| value_matches_ty(v, t, env)).unwrap_or(false)
            }),
            _ => false,
        },
        Ty::OpenRecordType { fields, .. } => match value {
            Value::Record(fs) => fields.iter().all(|(name, t)| {
                fs.get(name).map(|v| value_matches_ty(v, t, env)).unwrap_or(false)
            }),
            _ => false,
        },
        Ty::Ref(inner) | Ty::Mut(inner) => match value {
            Value::Ref(cell) => value_matches_ty(&cell.borrow(), inner, env),
            _ => false,
        },
        Ty::NamedBinder { ty, .. } => value_matches_ty(value, ty, env),
        // Arrow/sum shapes carry no runtime info to test against.
        Ty::Arrow { .. } | Ty::Sum(_) => true,
    }
}

/// Closed record types are runtime coercion boundaries: callers may provide a
/// wider record, but the callee receives only fields named by the type.
fn coerce_value_to_type(value: Value, ty: &Ty) -> Result<Value, String> {
    match ty {
        Ty::RecordType(fields) => match value {
            Value::Record(values) => {
                let mut projected = HashMap::new();
                for (name, _) in fields {
                    let Some(field) = values.get(name) else {
                        return Err(format!("record is missing field '{name}'"));
                    };
                    projected.insert(name.clone(), field.clone());
                }
                Ok(Value::Record(projected))
            }
            other => Ok(other),
        },
        Ty::OpenRecordType { .. } => Ok(value),
        _ => Ok(value),
    }
}

/// Like `value_matches_ty` but substitutes type parameters by position, so a
/// declared `type Pair a = { fst: a, snd: a }` can be tested as `Pair int`.
fn value_matches_ty_open(ty: &Ty, value: &Value, params: &[String], args: &[Ty], env: &Env) -> bool {
    if let Ty::Named { name, .. } = ty {
        if let Some(i) = params.iter().position(|p| p == name) {
            return args.get(i).map(|a| value_matches_ty(value, a, env)).unwrap_or(true);
        }
    }
    match ty {
        Ty::List(elem) => match value {
            Value::List(items) => items
                .iter()
                .all(|item| value_matches_ty_open(elem, item, params, args, env)),
            _ => false,
        },
        Ty::Tuple(elems) => match value {
            Value::Tuple(items) => {
                items.len() == elems.len()
                    && items
                        .iter()
                        .zip(elems.iter())
                        .all(|(v, t)| value_matches_ty_open(t, v, params, args, env))
            }
            _ => false,
        },
        Ty::RecordType(fields) => match value {
            Value::Record(fs) => fields.iter().all(|(name, t)| {
                fs.get(name)
                    .map(|v| value_matches_ty_open(t, v, params, args, env))
                    .unwrap_or(false)
            }),
            _ => false,
        },
        Ty::OpenRecordType { fields, .. } => match value {
            Value::Record(fs) => fields.iter().all(|(name, t)| {
                fs.get(name)
                    .map(|v| value_matches_ty_open(t, v, params, args, env))
                    .unwrap_or(false)
            }),
            _ => false,
        },
        Ty::NamedBinder { ty, .. } => value_matches_ty_open(ty, value, params, args, env),
        Ty::Ref(inner) | Ty::Mut(inner) => match value {
            Value::Ref(cell) => value_matches_ty_open(inner, &cell.borrow(), params, args, env),
            _ => false,
        },
        _ => true,
    }
}

pub(crate) fn value_eq(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Unit, Value::Unit) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Tuple(a), Value::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| value_eq(a, b))
        }
        (Value::List(a), Value::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| value_eq(a, b))
        }
        (Value::Record(a), Value::Record(b)) => {
            a.len() == b.len()
                && a.iter()
                    .all(|(key, value)| b.get(key).map(|other| value_eq(value, other)).unwrap_or(false))
        }
        (Value::Intrinsic(a), Value::Intrinsic(b)) => a.name == b.name && a.args.len() == b.args.len(),
        (Value::Ref(a), Value::Ref(b)) => Rc::ptr_eq(a, b),
        (Value::Sum { tag: ta, payload: pa }, Value::Sum { tag: tb, payload: pb }) => {
            ta == tb && value_eq(pa, pb)
        }
        _ => false,
    }
}
