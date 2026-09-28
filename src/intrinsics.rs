use std::io::{self, Write};
use std::rc::Rc;

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
    Native,
    Print,
    Println,
    TypeOf,
    Len,
    ListLen,
    StrLen,
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
        ("typeof", IntrinsicKind::TypeOf, 1),
        ("len", IntrinsicKind::Len, 1),
        ("__list_len", IntrinsicKind::ListLen, 1),
        ("__str_len", IntrinsicKind::StrLen, 1),
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
        ("__bool_assert", IntrinsicKind::Native, 1),
        ("__int_add", IntrinsicKind::Native, 2),
        ("__float_add", IntrinsicKind::Native, 2),
        ("__int_sub", IntrinsicKind::Native, 2),
        ("__float_sub", IntrinsicKind::Native, 2),
        ("__int_mul", IntrinsicKind::Native, 2),
        ("__float_mul", IntrinsicKind::Native, 2),
        ("__int_div", IntrinsicKind::Native, 2),
        ("__float_div", IntrinsicKind::Native, 2),
        ("__int_mod", IntrinsicKind::Native, 2),
        ("__int_abs", IntrinsicKind::Native, 1),
        ("__float_abs", IntrinsicKind::Native, 1),
        ("__int_equal", IntrinsicKind::Native, 2),
        ("__float_equal", IntrinsicKind::Native, 2),
        ("__bool_equal", IntrinsicKind::Native, 2),
        ("__str_equal", IntrinsicKind::Native, 2),
        ("__str_concat", IntrinsicKind::Native, 2),
        ("__list_concat", IntrinsicKind::Native, 2),
        ("__list_take", IntrinsicKind::Native, 2),
        ("__str_take", IntrinsicKind::Native, 2),
        ("__list_drop", IntrinsicKind::Native, 2),
        ("__str_drop", IntrinsicKind::Native, 2),
        ("__list_reverse", IntrinsicKind::Native, 1),
        ("__str_reverse", IntrinsicKind::Native, 1),
        ("__list_slice", IntrinsicKind::Native, 3),
        ("__str_slice", IntrinsicKind::Native, 3),
        ("__str_contains", IntrinsicKind::Native, 2),
        ("__list_contains", IntrinsicKind::Native, 2),
        ("__str_trim", IntrinsicKind::Native, 1),
        ("__str_chars", IntrinsicKind::Native, 1),
        ("__str_to_int", IntrinsicKind::Native, 1),
        ("__int_to_string", IntrinsicKind::Native, 1),
        ("__float_to_string", IntrinsicKind::Native, 1),
        ("__bool_to_string", IntrinsicKind::Native, 1),
        ("__str_to_string", IntrinsicKind::Native, 1),
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
        IntrinsicKind::Native => apply_native(intrinsic.name, &intrinsic.args),
        IntrinsicKind::Print => {
            print!("{}", intrinsic.args[0]);
            io::stdout().flush().map_err(|err| err.to_string())?;
            Ok(Value::Unit)
        }
        IntrinsicKind::Println => {
            println!("{}", intrinsic.args[0]);
            Ok(Value::Unit)
        }
        IntrinsicKind::TypeOf => Ok(Value::Str(
            match &intrinsic.args[0] {
                Value::Unit => "unit",
                Value::Bool(_) => "bool",
                Value::Int(_) => "int",
                Value::Float(_) => "float",
                Value::Str(_) => "str",
                Value::Tuple(_) => "tuple",
                Value::List(_) => "list",
                Value::Record(_) => "record",
                Value::Sum { .. } => "sum",
                Value::Closure(_) => "function",
                Value::Intrinsic(_) => "function",
                Value::Ref(_) => "ref",
            }
            .to_string(),
        )),
        IntrinsicKind::Len => match &intrinsic.args[0] {
            Value::List(items) => Ok(Value::Int(items.len() as i64)),
            Value::Tuple(items) => Ok(Value::Int(items.len() as i64)),
            Value::Str(text) => Ok(Value::Int(text.chars().count() as i64)),
            Value::Record(fields) => Ok(Value::Int(fields.len() as i64)),
            value => Err(format!(
                "len expects list, tuple, record, or string; got {value}"
            )),
        },
        IntrinsicKind::ListLen => match &intrinsic.args[0] {
            Value::List(items) => Ok(Value::Int(items.len() as i64)),
            value => Err(format!("__list_len expects a list; got {value}")),
        },
        IntrinsicKind::StrLen => match &intrinsic.args[0] {
            Value::Str(text) => Ok(Value::Int(text.chars().count() as i64)),
            value => Err(format!("__str_len expects a string; got {value}")),
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
            (func, value) => Err(format!(
                "map expects (function, list); got {func} and {value}"
            )),
        },
        IntrinsicKind::Filter => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                let mut out = Vec::new();
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => out.push(item.clone()),
                        Value::Bool(false) => {}
                        value => {
                            return Err(format!("filter predicate must return bool; got {value}"))
                        }
                    }
                }
                Ok(Value::List(out))
            }
            (func, value) => Err(format!(
                "filter expects (function, list); got {func} and {value}"
            )),
        },
        IntrinsicKind::Foldl => {
            match (&intrinsic.args[0], &intrinsic.args[1], &intrinsic.args[2]) {
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
            }
        }
        IntrinsicKind::Any => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => return Ok(Value::Bool(true)),
                        Value::Bool(false) => {}
                        value => {
                            return Err(format!("any predicate must return bool; got {value}"))
                        }
                    }
                }
                Ok(Value::Bool(false))
            }
            (func, value) => Err(format!(
                "any expects (function, list); got {func} and {value}"
            )),
        },
        IntrinsicKind::All => match (&intrinsic.args[0], &intrinsic.args[1]) {
            (func, Value::List(items)) => {
                for item in items {
                    match apply_one(func.clone(), item.clone())? {
                        Value::Bool(true) => {}
                        Value::Bool(false) => return Ok(Value::Bool(false)),
                        value => {
                            return Err(format!("all predicate must return bool; got {value}"))
                        }
                    }
                }
                Ok(Value::Bool(true))
            }
            (func, value) => Err(format!(
                "all expects (function, list); got {func} and {value}"
            )),
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

fn apply_native(name: &str, args: &[Value]) -> Result<Value, String> {
    match name {
        "__bool_assert" => match args {
            [Value::Bool(true)] => Ok(Value::Unit),
            [Value::Bool(false)] => Err("assert failed".into()),
            [value] => Err(format!("__bool_assert expects bool; got {value}")),
            _ => unreachable!(),
        },
        "__int_add" => int_bin(args, |a, b| a.checked_add(b), "add"),
        "__int_sub" => int_bin(args, |a, b| a.checked_sub(b), "sub"),
        "__int_mul" => int_bin(args, |a, b| a.checked_mul(b), "mul"),
        "__int_div" => int_bin(args, |a, b| a.checked_div(b), "div"),
        "__int_mod" => int_bin(args, |a, b| a.checked_rem(b), "mod"),
        "__int_abs" => match args {
            [Value::Int(value)] => value
                .checked_abs()
                .map(Value::Int)
                .ok_or_else(|| "integer overflow in abs".into()),
            _ => Err("__int_abs expects int".into()),
        },
        "__float_add" => float_bin(args, |a, b| a + b),
        "__float_sub" => float_bin(args, |a, b| a - b),
        "__float_mul" => float_bin(args, |a, b| a * b),
        "__float_div" => float_bin(args, |a, b| a / b),
        "__float_abs" => match args {
            [Value::Float(value)] => Ok(Value::Float(value.abs())),
            _ => Err("__float_abs expects float".into()),
        },
        "__int_equal" | "__float_equal" | "__bool_equal" | "__str_equal" => equal_native(args),
        "__str_concat" => match args {
            [Value::Str(left), Value::Str(right)] => Ok(Value::Str(format!("{left}{right}"))),
            _ => Err("__str_concat expects str, str".into()),
        },
        "__list_concat" => match args {
            [Value::List(left), Value::List(right)] => {
                let mut result = left.clone();
                result.extend(right.iter().cloned());
                Ok(Value::List(result))
            }
            _ => Err("__list_concat expects list, list".into()),
        },
        "__str_to_string" => exact_string(args),
        "__int_to_string" | "__float_to_string" | "__bool_to_string" => match args {
            [value] => Ok(Value::Str(value.to_string())),
            _ => Err(format!("{name} expects one argument")),
        },
        "__str_contains" => match args {
            [Value::Str(haystack), Value::Str(needle)] => {
                Ok(Value::Bool(haystack.contains(needle)))
            }
            _ => Err("__str_contains expects str, str".into()),
        },
        "__list_contains" => match args {
            [Value::List(items), needle] => {
                Ok(Value::Bool(items.iter().any(|item| value_eq(item, needle))))
            }
            _ => Err("__list_contains expects list, value".into()),
        },
        "__str_trim" => match args {
            [Value::Str(text)] => Ok(Value::Str(text.trim().to_string())),
            _ => Err("__str_trim expects str".into()),
        },
        "__str_chars" => match args {
            [Value::Str(text)] => Ok(Value::List(
                text.chars().map(|ch| Value::Str(ch.to_string())).collect(),
            )),
            _ => Err("__str_chars expects str".into()),
        },
        // Total parse: `Some n` on success, `None` on failure (no runtime error).
        "__str_to_int" => match args {
            [Value::Str(text)] => Ok(match text.trim().parse::<i64>() {
                Ok(value) => Value::Sum {
                    tag: "Some".to_string(),
                    payload: Rc::new(Value::Int(value)),
                },
                Err(_) => Value::Sum {
                    tag: "None".to_string(),
                    payload: Rc::new(Value::Unit),
                },
            }),
            _ => Err("__str_to_int expects str".into()),
        },
        "__list_take" | "__list_drop" | "__list_reverse" | "__list_slice"
        | "__str_take" | "__str_drop" | "__str_reverse" | "__str_slice" => {
            apply_sequence_native(name, args)
        }
        _ => Err(format!("unknown native intrinsic {name}")),
    }
}

fn int_bin(
    args: &[Value],
    op: impl FnOnce(i64, i64) -> Option<i64>,
    name: &str,
) -> Result<Value, String> {
    match args {
        [Value::Int(left), Value::Int(right)] => op(*left, *right)
            .map(Value::Int)
            .ok_or_else(|| format!("integer overflow or invalid {name}")),
        _ => Err(format!("__int_{name} expects int, int")),
    }
}

fn float_bin(args: &[Value], op: impl FnOnce(f64, f64) -> f64) -> Result<Value, String> {
    match args {
        [Value::Float(left), Value::Float(right)] => Ok(Value::Float(op(*left, *right))),
        _ => Err("float native expects float, float".into()),
    }
}

fn equal_native(args: &[Value]) -> Result<Value, String> {
    match args {
        [left, right] => Ok(Value::Bool(value_eq(left, right))),
        _ => Err("equality native expects two arguments".into()),
    }
}

fn exact_string(args: &[Value]) -> Result<Value, String> {
    match args {
        [Value::Str(value)] => Ok(Value::Str(value.clone())),
        _ => Err("__str_to_string expects str".into()),
    }
}

fn apply_sequence_native(name: &str, args: &[Value]) -> Result<Value, String> {
    let is_string = name.starts_with("__str_");
    let operation = &name[6..];
    match (operation, args) {
        ("take", [Value::Int(count), value]) | ("drop", [Value::Int(count), value])
            if *count >= 0 =>
        {
            let count = *count as usize;
            if is_string {
                let Value::Str(text) = value else {
                    return Err(format!("{name} expects str"));
                };
                let chars: Vec<_> = text.chars().collect();
                let range = if operation == "take" {
                    0..count.min(chars.len())
                } else {
                    count.min(chars.len())..chars.len()
                };
                Ok(Value::Str(chars[range].iter().collect()))
            } else {
                let Value::List(items) = value else {
                    return Err(format!("{name} expects list"));
                };
                let range = if operation == "take" {
                    0..count.min(items.len())
                } else {
                    count.min(items.len())..items.len()
                };
                Ok(Value::List(items[range].to_vec()))
            }
        }
        ("reverse", [value]) => {
            if is_string {
                let Value::Str(text) = value else {
                    return Err(format!("{name} expects str"));
                };
                Ok(Value::Str(text.chars().rev().collect()))
            } else {
                let Value::List(items) = value else {
                    return Err(format!("{name} expects list"));
                };
                let mut result = items.clone();
                result.reverse();
                Ok(Value::List(result))
            }
        }
        ("slice", [Value::Int(start), Value::Int(length), value])
            if *start >= 0 && *length >= 0 =>
        {
            let (start, length) = (*start as usize, *length as usize);
            if is_string {
                let Value::Str(text) = value else {
                    return Err(format!("{name} expects str"));
                };
                Ok(Value::Str(text.chars().skip(start).take(length).collect()))
            } else {
                let Value::List(items) = value else {
                    return Err(format!("{name} expects list"));
                };
                Ok(Value::List(
                    items.iter().skip(start).take(length).cloned().collect(),
                ))
            }
        }
        _ => Err(format!("invalid arguments to {name}")),
    }
}

fn expect_non_negative_int(value: &Value, name: &str) -> Result<usize, String> {
    match value {
        Value::Int(v) if *v >= 0 => Ok(*v as usize),
        _ => Err(format!(
            "{name} expects a non-negative integer index/count; got {value}"
        )),
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
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(if want_min {
            (*a).min(*b)
        } else {
            (*a).max(*b)
        })),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(
            if (want_min && a <= b) || (!want_min && a >= b) {
                *a
            } else {
                *b
            },
        )),
        (Value::Int(a), Value::Float(b)) => {
            let a = *a as f64;
            Ok(Value::Float(
                if (want_min && a <= *b) || (!want_min && a >= *b) {
                    a
                } else {
                    *b
                },
            ))
        }
        (Value::Float(a), Value::Int(b)) => {
            let b = *b as f64;
            Ok(Value::Float(
                if (want_min && *a <= b) || (!want_min && *a >= b) {
                    *a
                } else {
                    b
                },
            ))
        }
        (Value::Str(a), Value::Str(b)) => Ok(Value::Str(
            if (want_min && a <= b) || (!want_min && a >= b) {
                a.clone()
            } else {
                b.clone()
            },
        )),
        _ => Err(format!(
            "{} expects comparable numbers or strings; got {} and {}",
            if want_min { "min" } else { "max" },
            left,
            right
        )),
    }
}
