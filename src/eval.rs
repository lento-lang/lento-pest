use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::io::{self, Write};
use std::rc::Rc;

use crate::ast::{
    BinaryOp, BlockExpr, Decl, Expr, LetDecl, Lit, MatchArm, PatKind, Pattern, Program, Stmt,
    UnaryOp,
};

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
pub struct Intrinsic {
    name: &'static str,
    kind: IntrinsicKind,
    arity: usize,
    args: Vec<Value>,
}

#[derive(Debug, Clone, Copy)]
enum IntrinsicKind {
    Print,
    Println,
    Len,
    Assert,
    Concat,
    Head,
    Tail,
    IsEmpty,
    Abs,
    Min,
    Max,
    ToString,
    ParseInt,
    Contains,
    Take,
    Drop,
    Reverse,
    Slice,
    Join,
    Split,
    Map,
    Filter,
    Foldl,
    Any,
    All,
    Range,
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

fn install_intrinsics(env: &mut Env) {
    for (name, kind, arity) in [
        ("print", IntrinsicKind::Print, 1),
        ("println", IntrinsicKind::Println, 1),
        ("len", IntrinsicKind::Len, 1),
        ("assert", IntrinsicKind::Assert, 1),
        ("concat", IntrinsicKind::Concat, 2),
        ("head", IntrinsicKind::Head, 1),
        ("tail", IntrinsicKind::Tail, 1),
        ("is_empty", IntrinsicKind::IsEmpty, 1),
        ("abs", IntrinsicKind::Abs, 1),
        ("min", IntrinsicKind::Min, 2),
        ("max", IntrinsicKind::Max, 2),
        ("to_string", IntrinsicKind::ToString, 1),
        ("parse_int", IntrinsicKind::ParseInt, 1),
        ("contains", IntrinsicKind::Contains, 2),
        ("take", IntrinsicKind::Take, 2),
        ("drop", IntrinsicKind::Drop, 2),
        ("reverse", IntrinsicKind::Reverse, 1),
        ("slice", IntrinsicKind::Slice, 3),
        ("join", IntrinsicKind::Join, 2),
        ("split", IntrinsicKind::Split, 2),
        ("map", IntrinsicKind::Map, 2),
        ("filter", IntrinsicKind::Filter, 2),
        ("foldl", IntrinsicKind::Foldl, 3),
        ("any", IntrinsicKind::Any, 2),
        ("all", IntrinsicKind::All, 2),
        ("range", IntrinsicKind::Range, 2),
    ] {
        env.insert(
            name.to_string(),
            Binding::Inline(Value::Intrinsic(Intrinsic {
                name,
                kind,
                arity,
                args: Vec::new(),
            })),
        );
    }
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

fn apply_one(callee: Value, arg: Value) -> Result<Value, String> {
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

fn apply_intrinsic(intrinsic: Intrinsic) -> Result<Value, String> {
    match intrinsic.kind {
        IntrinsicKind::Print => {
            print!("{}", intrinsic.args[0]);
            io::stdout().flush().map_err(|err| err.to_string())?;
            Ok(Value::Unit)
        }
        IntrinsicKind::Println => {
            println!("{}", intrinsic.args[0]);
            Ok(Value::Unit)
        }
        IntrinsicKind::Len => match &intrinsic.args[0] {
            Value::List(items) => Ok(Value::Int(items.len() as i64)),
            Value::Tuple(items) => Ok(Value::Int(items.len() as i64)),
            Value::Str(text) => Ok(Value::Int(text.chars().count() as i64)),
            value => Err(format!("len expects list, tuple, or string; got {value}")),
        },
        IntrinsicKind::Assert => match &intrinsic.args[0] {
            Value::Bool(true) => Ok(Value::Unit),
            Value::Bool(false) => Err("assert failed".into()),
            value => Err(format!("assert expects a boolean; got {value}")),
        },
        IntrinsicKind::Concat => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (Value::List(left), Value::List(right)) => {
                let mut out = left.clone();
                out.extend(right.iter().cloned());
                Ok(Value::List(out))
            }
            (Value::Str(left), Value::Str(right)) => Ok(Value::Str(format!("{left}{right}"))),
            (left, right) => Err(format!(
                "concat expects two lists or two strings; got {left} and {right}"
            )),
        },
        IntrinsicKind::Head => match &intrinsic.args[0] {
            Value::List(items) => items
                .first()
                .cloned()
                .ok_or_else(|| "head expects a non-empty list".to_string()),
            value => Err(format!("head expects a list; got {value}")),
        },
        IntrinsicKind::Tail => match &intrinsic.args[0] {
            Value::List(items) => {
                if items.is_empty() {
                    Err("tail expects a non-empty list".into())
                } else {
                    Ok(Value::List(items[1..].to_vec()))
                }
            }
            value => Err(format!("tail expects a list; got {value}")),
        },
        IntrinsicKind::IsEmpty => match &intrinsic.args[0] {
            Value::List(items) => Ok(Value::Bool(items.is_empty())),
            value => Err(format!("is_empty expects a list; got {value}")),
        },
        IntrinsicKind::Abs => match &intrinsic.args[0] {
            Value::Int(v) => v
                .checked_abs()
                .map(Value::Int)
                .ok_or_else(|| "integer overflow in abs".to_string()),
            Value::Float(v) => Ok(Value::Float(v.abs())),
            value => Err(format!("abs expects a number; got {value}")),
        },
        IntrinsicKind::Min => intrinsic_min_max(&intrinsic.args[0], &intrinsic.args[1], true),
        IntrinsicKind::Max => intrinsic_min_max(&intrinsic.args[0], &intrinsic.args[1], false),
        IntrinsicKind::ToString => Ok(Value::Str(format!("{}", intrinsic.args[0]))),
        IntrinsicKind::ParseInt => match &intrinsic.args[0] {
            Value::Str(text) => text
                .trim()
                .parse::<i64>()
                .map(Value::Int)
                .map_err(|_| format!("parse_int could not parse '{text}'")),
            value => Err(format!("parse_int expects a string; got {value}")),
        },
        IntrinsicKind::Contains => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (Value::Str(text), Value::Str(needle)) => Ok(Value::Bool(text.contains(needle))),
            (Value::List(items), needle) => Ok(Value::Bool(
                items.iter().any(|item| value_eq(item, needle)),
            )),
            (value, needle) => Err(format!(
                "contains expects (string, string) or (list, value); got {value} and {needle}"
            )),
        },
        IntrinsicKind::Take => {
            let n = expect_non_negative_int(&intrinsic.args[0], "take")?;
            match &intrinsic.args[1] {
                Value::List(items) => Ok(Value::List(items.iter().take(n).cloned().collect())),
                Value::Str(text) => Ok(Value::Str(text.chars().take(n).collect())),
                value => Err(format!("take expects a list or string; got {value}")),
            }
        }
        IntrinsicKind::Drop => {
            let n = expect_non_negative_int(&intrinsic.args[0], "drop")?;
            match &intrinsic.args[1] {
                Value::List(items) => Ok(Value::List(items.iter().skip(n).cloned().collect())),
                Value::Str(text) => Ok(Value::Str(text.chars().skip(n).collect())),
                value => Err(format!("drop expects a list or string; got {value}")),
            }
        }
        IntrinsicKind::Reverse => match &intrinsic.args[0] {
            Value::List(items) => {
                let mut out = items.clone();
                out.reverse();
                Ok(Value::List(out))
            }
            Value::Str(text) => Ok(Value::Str(text.chars().rev().collect())),
            value => Err(format!("reverse expects a list or string; got {value}")),
        },
        IntrinsicKind::Slice => {
            let start = expect_non_negative_int(&intrinsic.args[0], "slice")?;
            let len = expect_non_negative_int(&intrinsic.args[1], "slice")?;
            match &intrinsic.args[2] {
                Value::List(items) => Ok(Value::List(
                    items.iter().skip(start).take(len).cloned().collect(),
                )),
                Value::Str(text) => Ok(Value::Str(text.chars().skip(start).take(len).collect())),
                value => Err(format!("slice expects a list or string; got {value}")),
            }
        }
        IntrinsicKind::Join => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (Value::Str(sep), Value::List(items)) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    match item {
                        Value::Str(text) => out.push(text.clone()),
                        value => {
                            return Err(format!(
                                "join expects a list of strings; got element {value}"
                            ))
                        }
                    }
                }
                Ok(Value::Str(out.join(sep)))
            }
            (sep, items) => Err(format!(
                "join expects (string, list of strings); got {sep} and {items}"
            )),
        },
        IntrinsicKind::Split => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (Value::Str(sep), Value::Str(text)) => Ok(Value::List(
                text.split(sep)
                    .map(|part| Value::Str(part.to_string()))
                    .collect(),
            )),
            (sep, text) => Err(format!(
                "split expects (string, string); got {sep} and {text}"
            )),
        },
        IntrinsicKind::Map => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(apply_one(func.clone(), item.clone())?);
                }
                Ok(Value::List(out))
            }
            (func, value) => Err(format!("map expects (function, list); got {func} and {value}")),
        },
        IntrinsicKind::Filter => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                let mut out = Vec::new();
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => out.push(item.clone()),
                        Value::Bool(false) => {}
                        value => return Err(format!("filter predicate must return bool; got {value}")),
                    }
                }
                Ok(Value::List(out))
            }
            (func, value) => Err(format!("filter expects (function, list); got {func} and {value}")),
        },
        IntrinsicKind::Foldl => match (&intrinsic.args[0], &intrinsic.args[1], &intrinsic.args[2]) {
            (func, init, Value::List(items)) => {
                let mut acc = init.clone();
                for item in items {
                    acc = apply_one(apply_one(func.clone(), acc)?, item.clone())?;
                }
                Ok(acc)
            }
            (func, init, value) => Err(format!(
                "foldl expects (function, init, list); got {func}, {init}, and {value}"
            )),
        },
        IntrinsicKind::Any => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => return Ok(Value::Bool(true)),
                        Value::Bool(false) => {}
                        value => return Err(format!("any predicate must return bool; got {value}")),
                    }
                }
                Ok(Value::Bool(false))
            }
            (func, value) => Err(format!("any expects (function, list); got {func} and {value}")),
        },
        IntrinsicKind::All => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => {}
                        Value::Bool(false) => return Ok(Value::Bool(false)),
                        value => return Err(format!("all predicate must return bool; got {value}")),
                    }
                }
                Ok(Value::Bool(true))
            }
            (func, value) => Err(format!("all expects (function, list); got {func} and {value}")),
        },
        IntrinsicKind::Range => {
            let start = expect_int(&intrinsic.args[0], "range")?;
            let end = expect_int(&intrinsic.args[1], "range")?;
            let mut out = Vec::new();
            if start <= end {
                for i in start..end {
                    out.push(Value::Int(i));
                }
            } else {
                for i in (end + 1..=start).rev() {
                    out.push(Value::Int(i));
                }
            }
            Ok(Value::List(out))
        }
    }
}

fn expect_non_negative_int(value: &Value, name: &str) -> Result<usize, String> {
    match value {
        Value::Int(v) if *v >= 0 => Ok(*v as usize),
        _ => Err(format!("{name} expects a non-negative integer index/count; got {value}")),
    }
}

fn expect_int(value: &Value, name: &str) -> Result<i64, String> {
    match value {
        Value::Int(v) => Ok(*v),
        _ => Err(format!("{name} expects an integer; got {value}")),
    }
}

fn intrinsic_min_max(left: &Value, right: &Value, want_min: bool) -> Result<Value, String> {
    match (left, right) {
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(if want_min { (*a).min(*b) } else { (*a).max(*b) })),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(if (want_min && a <= b) || (!want_min && a >= b) {
            *a
        } else {
            *b
        })),
        (Value::Int(a), Value::Float(b)) => {
            let a = *a as f64;
            Ok(Value::Float(if (want_min && a <= *b) || (!want_min && a >= *b) {
                a
            } else {
                *b
            }))
        }
        (Value::Float(a), Value::Int(b)) => {
            let b = *b as f64;
            Ok(Value::Float(if (want_min && *a <= b) || (!want_min && *a >= b) {
                *a
            } else {
                b
            }))
        }
        (Value::Str(a), Value::Str(b)) => Ok(Value::Str(if (want_min && a <= b) || (!want_min && a >= b) {
            a.clone()
        } else {
            b.clone()
        })),
        _ => Err(format!(
            "{} expects comparable numbers or strings; got {} and {}",
            if want_min { "min" } else { "max" },
            left,
            right
        )),
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
            Value::List(values) if values.len() == items.len() => {
                for (pattern, value) in items.iter().zip(values.iter()) {
                    if !collect_pattern_bindings(pattern, value, out)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
        PatKind::Record(fields) => match value {
            Value::Record(values) => {
                for field in fields {
                    let Some(field_value) = values.get(&field.name) else {
                        return Ok(false);
                    };
                    if !collect_pattern_bindings(&field.pattern, field_value, out)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
        PatKind::Cons { head, tail } => match value {
            Value::List(values) if !values.is_empty() => {
                if !collect_pattern_bindings(head, &values[0], out)? {
                    return Ok(false);
                }
                collect_pattern_bindings(tail, &Value::List(values[1..].to_vec()), out)
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

fn value_eq(left: &Value, right: &Value) -> bool {
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
