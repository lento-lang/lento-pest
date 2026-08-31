use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::{
    BinaryOp, BlockExpr, Decl, Expr, LetDecl, Lit, MatchArm, PatKind, Pattern, Program, Stmt,
    UnaryOp,
};
use crate::intrinsics::{apply_intrinsic, install_intrinsics, Intrinsic};

pub type CellRef = Rc<RefCell<Value>>;
pub type Env = HashMap<String, Binding>;

#[derive(Debug, Clone)]
pub enum Binding {
    Inline(Value),
    Cell { value: CellRef, mutable: bool },
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
            Value::Closure(_) => write!(f, "<closure>"),
            Value::Intrinsic(intrinsic) => write!(f, "<intrinsic:{}>", intrinsic.name),
            Value::Ref(_) => write!(f, "<ref>"),
        }
    }
}

pub fn eval_program(program: &Program) -> Result<Value, String> {
    let mut env = initial_env();
    eval_program_in_env(program, &mut env)
}

pub fn initial_env() -> Env {
    let mut env = Env::new();
    install_intrinsics(&mut env);
    env
}

pub fn eval_program_in_env(program: &Program, env: &mut Env) -> Result<Value, String> {
    let mut last = Value::Unit;
    for stmt in &program.statements {
        last = eval_stmt(stmt, env)?;
    }
    Ok(last)
}

fn eval_stmt(stmt: &Stmt, env: &mut Env) -> Result<Value, String> {
    match stmt {
        Stmt::Decl(decl) => eval_decl(decl, env),
        Stmt::Expr(expr) => eval_expr(expr, env),
    }
}

fn eval_decl(decl: &Decl, env: &mut Env) -> Result<Value, String> {
    match decl {
        Decl::Spec(_) | Decl::Type(_) => Ok(Value::Unit),
        Decl::Fn(_) => Err("unexpected fn declaration at evaluation time; desugar first".into()),
        Decl::Let(let_decl) => eval_let_decl(let_decl, env),
    }
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
        Expr::Block(block) => eval_block(block, env),
        Expr::Match(match_expr) => {
            let scrutinee = eval_expr(&match_expr.scrutinee, env)?;
            eval_match(scrutinee, &match_expr.arms, env)
        }
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
        },
        _ => Err("assignment currently supports only variable places".into()),
    }
}

fn apply_call(callee: Value, args: Vec<Value>) -> Result<Value, String> {
    match callee {
        Value::Closure(closure) if closure.params.len() == args.len() => {
            let mut local_env = closure.env.clone();
            for (param, arg) in closure.params.iter().zip(args.into_iter()) {
                bind_pattern(param, arg, false, &mut local_env)?;
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
            if closure.params.len() != 1 {
                return Err(format!(
                    "closure expected {} arguments, got 1",
                    closure.params.len()
                ));
            }
            let mut local_env = closure.env.clone();
            bind_pattern(&closure.params[0], arg, false, &mut local_env)?;
            eval_expr(&closure.body, &mut local_env)
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
        BinaryOp::Cons => {
            let head = eval_expr(lhs, env)?;
            let tail = eval_expr(rhs, env)?;
            match tail {
                Value::List(mut items) => {
                    items.insert(0, head);
                    Ok(Value::List(items))
                }
                _ => Err(":: expects a list on the right-hand side".into()),
            }
        }
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
        BinaryOp::And | BinaryOp::Or | BinaryOp::Cons => unreachable!(),
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

fn bind_pattern(pattern: &Pattern, value: Value, mutable: bool, env: &mut Env) -> Result<(), String> {
    let mut binds = Vec::new();
    collect_pattern_bindings(pattern, &value, &mut binds)?;
    for (name, bound) in binds {
        env.insert(name, make_binding(bound, mutable));
    }
    Ok(())
}

fn pattern_matches(pattern: &Pattern, value: &Value, env: &mut Env) -> Result<bool, String> {
    let mut binds = Vec::new();
    if !collect_pattern_bindings(pattern, value, &mut binds)? {
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
    out: &mut Vec<(String, Value)>,
) -> Result<bool, String> {
    match &pattern.kind {
        PatKind::Var(name) => {
            out.push((name.clone(), value.clone()));
            Ok(true)
        }
        PatKind::Wildcard => Ok(true),
        PatKind::Lit(lit) => Ok(value_eq(value, &eval_lit(lit))),
        PatKind::Tuple(items) => match value {
            Value::Tuple(values) if values.len() == items.len() => {
                for (pattern, value) in items.iter().zip(values.iter()) {
                    if !collect_pattern_bindings(pattern, value, out)? {
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
                            if !collect_pattern_bindings(pattern, value, out)? {
                                return Ok(false);
                            }
                        }
                        match &items[i].kind {
                            PatKind::Spread(rest) => collect_pattern_bindings(
                                rest,
                                &Value::List(values[i..].to_vec()),
                                out,
                            ),
                            _ => Ok(false),
                        }
                    }
                    None if values.len() == items.len() => {
                        for (pattern, value) in items.iter().zip(values.iter()) {
                            if !collect_pattern_bindings(pattern, value, out)? {
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
        PatKind::Spread(inner) => collect_pattern_bindings(inner, value, out),
        PatKind::Record { fields, rest } => match value {
            Value::Record(values) => {
                let mut remainder = values.clone();
                for field in fields {
                    let Some(field_value) = values.get(&field.name) else {
                        return Ok(false);
                    };
                    if !collect_pattern_bindings(&field.pattern, field_value, out)? {
                        return Ok(false);
                    }
                    remainder.remove(&field.name);
                }
                if let Some(rest) = rest {
                    if !collect_pattern_bindings(rest, &Value::Record(remainder), out)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
    }
}

fn lookup_var(env: &Env, name: &str) -> Result<Value, String> {
    env.get(name)
        .map(|binding| match binding {
            Binding::Inline(value) => value.clone(),
            Binding::Cell { value, .. } => value.borrow().clone(),
        })
        .ok_or_else(|| format!("undefined variable '{name}'"))
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
        _ => false,
    }
}
