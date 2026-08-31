use pest::iterators::{Pair, Pairs};
use pest::Parser;

use crate::ast::*;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct LentoParser;

/// Parse a source string and translate the resulting parse tree into the
/// internal AST.
pub fn parse_program(source: &str) -> Result<Program, pest::error::Error<Rule>> {
    let pairs = LentoParser::parse(Rule::program, source)?;
    let root = pairs.into_iter().next().unwrap(); // the root `program` pair
    Ok(program(root.into_inner()))
}

/// Parse into raw pest pairs (useful for debugging the grammar).
pub fn parse_pairs(source: &str) -> Result<Pairs<'_, Rule>, pest::error::Error<Rule>> {
    LentoParser::parse(Rule::program, source)
}

pub fn print_pairs(pairs: Pairs<'_, Rule>) {
    pest_ascii_tree::print_ascii_tree(Ok(pairs));
}

// --------------------------------------------------------------------------
// Top level
// --------------------------------------------------------------------------

fn program(pairs: Pairs<'_, Rule>) -> Program {
    let mut statements = Vec::new();
    for pair in pairs {
        if pair.as_rule() == Rule::EOI {
            continue;
        }
        if let Some(stmt) = stmt(pair) {
            statements.push(stmt);
        }
    }
    Program { statements }
}

fn stmt(pair: Pair<'_, Rule>) -> Option<Stmt> {
    match pair.as_rule() {
        Rule::spec_decl => Some(Stmt::Decl(Decl::Spec(spec_decl(pair)))),
        Rule::type_decl => Some(Stmt::Decl(Decl::Type(type_decl(pair)))),
        Rule::let_decl => Some(Stmt::Decl(Decl::Let(let_decl(pair)))),
        // `fn` is kept as its own node in the AST so the source round-trips;
        // the evaluator desugars it via `desugar_program`/`desugar_fn`.
        Rule::fn_clause => Some(Stmt::Decl(Decl::Fn(fn_clause(pair)))),
        _ => Some(Stmt::Expr(expression(pair))),
    }
}

// --------------------------------------------------------------------------
// Declarations
// --------------------------------------------------------------------------

fn spec_decl(pair: Pair<'_, Rule>) -> SpecDecl {
    let mut name = String::new();
    let mut quantifiers = Vec::new();
    let mut ty = Ty::Tuple(Vec::new());
    let mut where_ = None;
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::identifier => name = inner.as_str().to_string(),
            Rule::quantifier => quantifiers.push(quantifier(inner)),
            Rule::arrow_type => ty = type_(inner),
            Rule::where_clause => where_ = Some(where_clause(inner)),
            _ => {}
        }
    }
    SpecDecl {
        name,
        ty: SpecType {
            quantifiers,
            ty,
            where_,
        },
    }
}

fn quantifier(pair: Pair<'_, Rule>) -> Quantifier {
    let mut vars = Vec::new();
    let mut constraints = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::type_var => vars.push(inner.as_str().to_string()),
            Rule::constraint => constraints.push(constraint(inner)),
            _ => {}
        }
    }
    Quantifier { vars, constraints }
}

fn constraint(pair: Pair<'_, Rule>) -> Constraint {
    let mut name = String::new();
    let mut args = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::identifier => name = inner.as_str().to_string(),
            _ => args.push(type_(inner)),
        }
    }
    Constraint { name, args }
}

fn where_clause(pair: Pair<'_, Rule>) -> Vec<Expr> {
    pair.into_inner().map(expression).collect()
}

fn type_decl(pair: Pair<'_, Rule>) -> TypeDecl {
    let mut name = String::new();
    let mut ty = Ty::Tuple(Vec::new());
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::identifier => name = inner.as_str().to_string(),
            _ => ty = type_(inner),
        }
    }
    TypeDecl { name, ty }
}

fn let_decl(pair: Pair<'_, Rule>) -> LetDecl {
    let mut mutable = false;
    let mut pat = Pattern { annotation: None, kind: PatKind::Wildcard };
    let mut annotation = None;
    let mut value = none_expr();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::let_mut => mutable = true,
            Rule::pattern => pat = pattern(inner),
            Rule::arrow_type | Rule::type_base | Rule::ty_ref | Rule::ty_mut => {
                annotation = Some(type_(inner))
            }
            _ => value = expression(inner),
        }
    }
    LetDecl {
        mutable,
        pattern: pat,
        annotation,
        value,
    }
}

fn fn_clause(pair: Pair<'_, Rule>) -> FnDecl {
    let (name, params, ret, body) = fn_clause_parts(pair);
    FnDecl {
        name,
        params,
        ret,
        body,
    }
}

/// Extract the ingredients of a `fn` clause: name, parameter patterns,
/// optional return type, and body.
fn fn_clause_parts(pair: Pair<'_, Rule>) -> (String, Vec<Pattern>, Option<Ty>, Expr) {
    let mut name = String::new();
    let mut params = Vec::new();
    let mut ret = None;
    let mut body = none_expr();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::identifier => name = inner.as_str().to_string(),
            // function_pattern = { pattern }
            Rule::function_pattern => {
                let pat = pattern(inner.into_inner().next().unwrap());
                params.push(pat);
            }
            Rule::arrow_type | Rule::type_base | Rule::ty_ref | Rule::ty_mut => {
                ret = Some(type_(inner))
            }
            _ => body = expression(inner),
        }
    }
    (name, params, ret, body)
}

// --------------------------------------------------------------------------
// Patterns
// --------------------------------------------------------------------------

/// Build a `Pattern` from a `pattern` pair.
fn pattern(pair: Pair<'_, Rule>) -> Pattern {
    pat_alt(pair.into_inner().next().unwrap())
}

/// Build a `Pattern` from the single `pattern_alt` pair inside a `pattern`.
fn pat_alt(pair: Pair<'_, Rule>) -> Pattern {
    let kids: Vec<Pair<'_, Rule>> = pair.into_inner().collect();

    // Tuple destructuring `(a, b)` / `(a : Int, b)`.
    if kids.iter().any(|k| k.as_rule() == Rule::pattern_elem) {
        let elems = kids
            .into_iter()
            .filter(|k| k.as_rule() == Rule::pattern_elem)
            .map(pat_elem)
            .collect();
        return Pattern { annotation: None, kind: PatKind::Tuple(elems) };
    }

    // Single annotation `(x : Int)`.
    if let Some(ty) = kids.iter().find(|k| is_type(k.as_rule())) {
        let ty = type_(ty.clone());
        let kind = match kids.iter().find(|k| k.as_rule() == Rule::pattern) {
            Some(p) => pattern(p.clone()).kind,
            None => PatKind::Wildcard,
        };
        return Pattern { annotation: Some(ty), kind };
    }

    // Grouped `(a)` — transparent.
    if kids.len() == 1 && kids[0].as_rule() == Rule::pattern {
        return pattern(kids.into_iter().next().unwrap());
    }

    // Atom.
    match kids.into_iter().next() {
        Some(atom) => atom_pattern(atom),
        None => Pattern { annotation: None, kind: PatKind::Wildcard },
    }
}

/// Build a `Pattern` from a `pattern_elem` pair (a tuple element that may
/// carry its own annotation `pattern : T`).
fn pat_elem(pair: Pair<'_, Rule>) -> Pattern {
    let mut inner_pat: Option<Pattern> = None;
    let mut annotation = None;
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::pattern {
            inner_pat = Some(pattern(inner));
        } else {
            annotation = Some(type_(inner));
        }
    }
    let mut pat = inner_pat.unwrap_or(Pattern {
        annotation: None,
        kind: PatKind::Wildcard,
    });
    // An element-level `pattern : T` annotation overrides the pattern's own.
    if let Some(ty) = annotation {
        pat.annotation = Some(ty);
    }
    pat
}

/// Build a `Pattern` from an atom (identifier, `_`, literal, list, record).
fn atom_pattern(pair: Pair<'_, Rule>) -> Pattern {
    match pair.as_rule() {
        Rule::identifier => Pattern {
            annotation: None,
            kind: PatKind::Var(pair.as_str().to_string()),
        },
        Rule::list_pattern => list_pattern(pair),
        Rule::spread_pattern => Pattern {
            annotation: None,
            kind: PatKind::Spread(Box::new(pattern(pair.into_inner().next().unwrap()))),
        },
        Rule::record_pattern => record_pattern(pair),
        Rule::boolean => Pattern {
            annotation: None,
            kind: PatKind::Lit(Lit::Bool(pair.as_str() == "true")),
        },
        Rule::integer | Rule::float => Pattern {
            annotation: None,
            kind: PatKind::Lit(number_lit(pair.as_str())),
        },
        Rule::string => {
            let s = &pair.as_str()[1..pair.as_str().len() - 1];
            Pattern {
                annotation: None,
                kind: PatKind::Lit(Lit::Str(s.to_string())),
            }
        }
        _ => Pattern { annotation: None, kind: PatKind::Wildcard },
    }
}

fn list_pattern(pair: Pair<'_, Rule>) -> Pattern {
    let mut items = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::pattern => items.push(pattern(inner)),
            Rule::spread_pattern => items.push(Pattern {
                annotation: None,
                kind: PatKind::Spread(Box::new(pattern(inner.into_inner().next().unwrap()))),
            }),
            _ => {}
        }
    }
    Pattern {
        annotation: None,
        kind: PatKind::List(items),
    }
}

fn record_pattern(pair: Pair<'_, Rule>) -> Pattern {
    let mut fields = Vec::new();
    let mut rest = None;
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::record_field => fields.push(record_field(inner)),
            Rule::spread_pattern => {
                rest = Some(Box::new(pattern(inner.into_inner().next().unwrap())))
            }
            _ => {}
        }
    }
    Pattern {
        annotation: None,
        kind: PatKind::Record { fields, rest },
    }
}

/// Build a `RecordField` from a `record_field` pair.
fn record_field(pair: Pair<'_, Rule>) -> RecordField {
    let mut name = String::new();
    let mut pat = Pattern { annotation: None, kind: PatKind::Wildcard };
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::identifier {
            name = inner.as_str().to_string();
        } else {
            pat = pattern(inner);
        }
    }
    RecordField { name, pattern: pat }
}

// --------------------------------------------------------------------------
// Expressions
// --------------------------------------------------------------------------

fn expression(pair: Pair<'_, Rule>) -> Expr {
    match pair.as_rule() {
        Rule::assignment => assignment(pair),
        Rule::lambda_expr => lambda_expr(pair),
        Rule::binop_expr => binop_expr(pair),
        Rule::match_scrutinee => binop_expr(pair),
        Rule::boolean => Expr::Lit(LitExpr {
            value: Lit::Bool(pair.as_str() == "true"),
        }),
        Rule::string => {
            let s = &pair.as_str()[1..pair.as_str().len() - 1];
            Expr::Lit(LitExpr {
                value: Lit::Str(s.to_string()),
            })
        }
        Rule::number => Expr::Lit(LitExpr {
            value: number_lit(pair.as_str()),
        }),
        Rule::integer => Expr::Lit(LitExpr {
            value: Lit::Int(pair.as_str().parse().unwrap_or(0)),
        }),
        Rule::float => Expr::Lit(LitExpr {
            value: Lit::Float(pair.as_str().parse().unwrap_or(0.0)),
        }),
        Rule::identifier => Expr::Var(VarExpr {
            name: pair.as_str().to_string(),
        }),
        Rule::ref_expr => ref_expr(pair),
        Rule::ref_match_expr => ref_expr(pair),
        Rule::match_expr => match_expr(pair),
        Rule::call => call(pair),
        Rule::tuple => tuple(pair),
        Rule::list => list(pair),
        Rule::block => block(pair),
        Rule::member_access => member_access(pair),
        Rule::index_access => index_access(pair),
        other => panic!("unexpected expression rule: {other:?}"),
    }
}

fn none_expr() -> Expr {
    Expr::Block(BlockExpr { body: Vec::new() })
}

fn number_lit(s: &str) -> Lit {
    if s.contains('.') {
        Lit::Float(s.parse().unwrap_or(0.0))
    } else {
        Lit::Int(s.parse().unwrap_or(0))
    }
}

fn assignment(pair: Pair<'_, Rule>) -> Expr {
    let mut place = none_expr();
    let mut value = none_expr();
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::place_expr {
            place = operand(inner.into_inner().collect());
        } else {
            value = expression(inner);
        }
    }
    Expr::Assign(AssignExpr {
        place: Box::new(place),
        value: Box::new(value),
    })
}

fn lambda_expr(pair: Pair<'_, Rule>) -> Expr {
    let mut params = Vec::new();
    let mut body = none_expr();
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::lambda_pattern {
            params.push(pattern(inner.into_inner().next().unwrap()));
        } else {
            body = expression(inner);
        }
    }
    Expr::Lambda(LambdaExpr {
        params,
        body: Box::new(body),
    })
}

fn match_expr(pair: Pair<'_, Rule>) -> Expr {
    let mut scrutinee = none_expr();
    let mut arms = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::match_arm => arms.push(match_arm(inner)),
            // The only other meaningful child is the scrutinee expression.
            _ => scrutinee = expression(inner),
        }
    }
    Expr::Match(MatchExpr {
        scrutinee: Box::new(scrutinee),
        arms,
    })
}

fn match_arm(pair: Pair<'_, Rule>) -> MatchArm {
    let mut pat = Pattern {
        annotation: None,
        kind: PatKind::Wildcard,
    };
    let mut guard = None;
    let mut body = none_expr();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::pattern => pat = pattern(inner),
            Rule::guard => guard = Some(expression(inner.into_inner().next().unwrap())),
            _ => body = expression(inner),
        }
    }
    MatchArm {
        pattern: pat,
        guard,
        body: Box::new(body),
    }
}

fn binop_expr(pair: Pair<'_, Rule>) -> Expr {
    // Children are a flat mix of operand primaries, postfix ops, and infix ops
    // (applicative/postfix were made silent). Rebuild application + binary.
    let mut operands: Vec<Expr> = Vec::new();
    let mut ops: Vec<BinaryOp> = Vec::new();
    let mut current: Vec<Pair<'_, Rule>> = Vec::new();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::infix_op {
            operands.push(operand(std::mem::take(&mut current)));
            ops.push(infix_op(inner.as_str()));
        } else {
            current.push(inner);
        }
    }
    operands.push(operand(current));

    let mut iter = operands.into_iter();
    let mut acc = iter.next().unwrap_or_else(none_expr);
    for op in ops {
        let rhs = iter.next().unwrap_or_else(none_expr);
        acc = Expr::Binary(BinaryExpr {
            op,
            lhs: Box::new(acc),
            rhs: Box::new(rhs),
        });
    }
    acc
}

fn infix_op(s: &str) -> BinaryOp {
    match s {
        "+" => BinaryOp::Add,
        "-" => BinaryOp::Sub,
        "*" => BinaryOp::Mul,
        "/" => BinaryOp::Div,
        "%" => BinaryOp::Mod,
        "==" => BinaryOp::Eq,
        "!=" => BinaryOp::Ne,
        "<" => BinaryOp::Lt,
        ">" => BinaryOp::Gt,
        "<=" => BinaryOp::Le,
        ">=" => BinaryOp::Ge,
        "&&" => BinaryOp::And,
        "||" => BinaryOp::Or,
        "::" => BinaryOp::Cons,
        _ => BinaryOp::Add,
    }
}

/// Fold a run of operand primaries and postfix ops (application + postfix).
fn operand(items: Vec<Pair<'_, Rule>>) -> Expr {
    let mut acc: Option<Expr> = None;
    for item in items {
        match item.as_rule() {
            Rule::member_access => {
                let field = item.into_inner().next().unwrap().as_str().to_string();
                let obj = acc.take().unwrap_or_else(none_expr);
                acc = Some(Expr::Member(MemberExpr {
                    obj: Box::new(obj),
                    field,
                }));
            }
            Rule::index_access => {
                let mut inner = item.into_inner();
                let idx = expression(inner.next().unwrap());
                let obj = acc.take().unwrap_or_else(none_expr);
                acc = Some(Expr::Index(IndexExpr {
                    obj: Box::new(obj),
                    index: Box::new(idx),
                }));
            }
            _ => {
                let arg = expression(item);
                match acc.take() {
                    Some(callee) => {
                        acc = Some(Expr::Call(CallExpr {
                            callee: Box::new(callee),
                            args: vec![arg],
                        }));
                    }
                    None => acc = Some(arg),
                }
            }
        }
    }
    acc.unwrap_or_else(none_expr)
}

fn ref_expr(pair: Pair<'_, Rule>) -> Expr {
    Expr::Ref(RefExpr {
        inner: Box::new(expression(pair.into_inner().next().unwrap())),
    })
}

fn call(pair: Pair<'_, Rule>) -> Expr {
    let mut inner = pair.into_inner();
    let callee = inner.next().unwrap();
    let args = inner.map(expression).collect();
    Expr::Call(CallExpr {
        callee: Box::new(Expr::Var(VarExpr {
            name: callee.as_str().to_string(),
        })),
        args,
    })
}

fn tuple(pair: Pair<'_, Rule>) -> Expr {
    Expr::Tuple(TupleExpr {
        items: pair.into_inner().map(expression).collect(),
    })
}

fn list(pair: Pair<'_, Rule>) -> Expr {
    let items: Vec<Expr> = pair.into_inner().map(expression).collect();
    if items.is_empty() {
        return Expr::List(ListExpr::Empty);
    }
    let mut tail = ListExpr::Empty;
    for item in items.into_iter().rev() {
        tail = ListExpr::Cells(Box::new(ListCons {
            head: Box::new(item),
            tail: Box::new(tail),
        }));
    }
    Expr::List(tail)
}

fn block(pair: Pair<'_, Rule>) -> Expr {
    let mut body = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::body => {
                for stmt_pair in inner.into_inner() {
                    if let Some(s) = stmt(stmt_pair) {
                        body.push(s);
                    }
                }
            }
            _ => {
                if let Some(s) = stmt(inner) {
                    body.push(s);
                }
            }
        }
    }
    Expr::Block(BlockExpr { body })
}

fn member_access(pair: Pair<'_, Rule>) -> Expr {
    let field = pair.into_inner().next().unwrap().as_str().to_string();
    Expr::Member(MemberExpr {
        obj: Box::new(none_expr()),
        field,
    })
}

fn index_access(pair: Pair<'_, Rule>) -> Expr {
    let idx = expression(pair.into_inner().next().unwrap());
    Expr::Index(IndexExpr {
        obj: Box::new(none_expr()),
        index: Box::new(idx),
    })
}

// --------------------------------------------------------------------------
// Types
// --------------------------------------------------------------------------

fn is_type(rule: Rule) -> bool {
    matches!(
        rule,
        Rule::arrow_type
            | Rule::type_base
            | Rule::ty_ref
            | Rule::ty_mut
            | Rule::type_atom
            | Rule::named_binder
    )
}

fn type_(pair: Pair<'_, Rule>) -> Ty {
    match pair.as_rule() {
        Rule::ty_ref => Ty::Ref(Box::new(type_(pair.into_inner().next().unwrap()))),
        Rule::ty_mut => Ty::Mut(Box::new(type_(pair.into_inner().next().unwrap()))),
        Rule::arrow_type => arrow_type(pair),
        Rule::type_base => type_base(pair),
        Rule::named_binder => named_binder(pair),
        other => panic!("unexpected type rule: {other:?}"),
    }
}

fn arrow_type(pair: Pair<'_, Rule>) -> Ty {
    let mut inner = pair.into_inner();
    let from = type_(inner.next().unwrap());
    match inner.next() {
        Some(to) => Ty::Arrow {
            from: Box::new(from),
            to: Box::new(type_(to)),
        },
        None => from,
    }
}

fn named_binder(pair: Pair<'_, Rule>) -> Ty {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_string();
    let ty = type_(inner.next().unwrap());
    Ty::NamedBinder {
        name,
        ty: Box::new(ty),
    }
}

fn type_base(pair: Pair<'_, Rule>) -> Ty {
    let kids: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    if kids.is_empty() {
        return Ty::Tuple(Vec::new()); // unit `()`
    }
    let first = &kids[0];
    match first.as_rule() {
        Rule::identifier => {
            let name = first.as_str().to_string();
            let mut args = Vec::new();
            for k in kids.iter().skip(1) {
                for arg in k.clone().into_inner() {
                    args.push(type_(arg));
                }
            }
            Ty::Named { name, args }
        }
        Rule::arrow_type => type_(first.clone()), // paren grouping `(T)` / `(a -> b)`
        Rule::named_binder => named_binder(first.clone()), // `(x: T)`
        _ => Ty::List(Box::new(type_(first.clone()))), // `[T]`
    }
}
