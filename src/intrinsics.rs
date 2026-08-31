use std::io::{self, Write};

use crate::eval::{apply_one, value_eq, Binding, Env, Value};

#[derive(Debug, Clone)]
pub struct Intrinsic {
    pub(crate) name: &'static str,
    kind: IntrinsicKind,
    pub(crate) arity: usize,
    pub(crate) args: Vec<Value>,
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

pub(crate) fn install_intrinsics(env: &mut Env) {
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

pub(crate) fn apply_intrinsic(intrinsic: Intrinsic) -> Result<Value, String> {
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
            Value::Record(fields) => Ok(Value::Int(fields.len() as i64)),
            value => Err(format!("len expects list, tuple, record, or string; got {value}")),
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
            (Value::List(items), needle) => {
                Ok(Value::Bool(items.iter().any(|item| value_eq(item, needle))))
            }
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
