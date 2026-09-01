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

/// Keyword tokens are atomic (so they get a word boundary) and therefore
/// appear as named pairs in the parse tree; the lowering skips them.
fn is_keyword(rule: Rule) -> bool {
    matches!(
        rule,
        Rule::kw_spec
            | Rule::kw_type
            | Rule::kw_let
            | Rule::kw_fn
            | Rule::kw_mut
            | Rule::kw_ref
            | Rule::kw_match
            | Rule::kw_if
            | Rule::kw_all
            | Rule::kw_where
    )
}

fn stmt(pair: Pair<'_, Rule>) -> Option<Stmt> {
    match pair.as_rule() {
        Rule::spec_decl => Some(Stmt::Decl(Decl::Spec(spec_decl(pair)))),
        Rule::type_decl => Some(Stmt::Decl(Decl::Type(type_decl(pair)))),
        Rule::let_decl => Some(Stmt::Decl(Decl::Let(let_decl(pair)))),
        // `fn` is kept as its own node in the AST so the source round-trips;
        // the evaluator desugars it via `desugar_program`/`desugar_fn`.
        Rule::fn_clause => Some(Stmt::Decl(Decl::Fn(fn_clause(pair)))),
        r if is_keyword(r) => None,
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
    pair.into_inner()
        .filter(|p| !is_keyword(p.as_rule()))
        .map(expression)
        .collect()
}

fn type_decl(pair: Pair<'_, Rule>) -> TypeDecl {
    let mut name = String::new();
    let mut ty = Ty::Tuple(Vec::new());
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::identifier => name = inner.as_str().to_string(),
            r if is_keyword(r) => {}
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
            r if is_keyword(r) => {}
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
            // function_pattern wraps one parameter shape (see grammar).
            Rule::function_pattern => {
                params.push(fn_param(inner.into_inner().next().unwrap()));
            }
            Rule::arrow_type | Rule::type_base | Rule::ty_ref | Rule::ty_mut => {
                ret = Some(type_(inner))
            }
            r if is_keyword(r) => {}
            _ => body = expression(inner),
        }
    }
    (name, params, ret, body)
}

/// Build a `Pattern` from one `function_pattern` child: a parenthesized
/// destructuring parameter, or a bare name/wildcard/literal.
fn fn_param(pair: Pair<'_, Rule>) -> Pattern {
    match pair.as_rule() {
        Rule::tuple_param => {
            let elems: Vec<Pattern> = pair
                .into_inner()
                .filter(|p| p.as_rule() == Rule::param_field)
                .map(param_field)
                .collect();
            // A single-element parenthesized parameter is just grouping:
            // `({x: a})` / `([x])` are record/list patterns, not 1-tuples.
            if elems.len() == 1 && !matches!(elems[0].kind, PatKind::Tuple(_)) {
                return elems.into_iter().next().unwrap();
            }
            Pattern {
                annotation: None,
                kind: PatKind::Tuple(elems),
            }
        }
        Rule::list_param => list_pattern(pair),
        Rule::record_param => record_pattern(pair),
        Rule::wildcard => Pattern {
            annotation: None,
            kind: PatKind::Wildcard,
        },
        _ => atom_pattern(pair),
    }
}

/// Build a `Pattern` from a `param_field`: a nested function parameter with
/// an optional `: T` annotation.
fn param_field(pair: Pair<'_, Rule>) -> Pattern {
    let mut pat = Pattern {
        annotation: None,
        kind: PatKind::Wildcard,
    };
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::function_pattern => {
                pat = fn_param(inner.into_inner().next().unwrap());
            }
            _ => pat.annotation = Some(type_(inner)),
        }
    }
    pat
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
    // Drop silent-context strays: `wildcard` is the only leaf atom that is a
    // named rule, everything else arrives via `atom_pattern`'s alternatives.
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

/// Build a `Pattern` from an atom (wildcard, identifier, literal, list,
/// record).
fn atom_pattern(pair: Pair<'_, Rule>) -> Pattern {
    match pair.as_rule() {
        Rule::identifier => Pattern {
            annotation: None,
            kind: PatKind::Var(pair.as_str().to_string()),
        },
        Rule::list_pattern | Rule::list_param => list_pattern(pair),
        Rule::record_pattern | Rule::record_param => record_pattern(pair),
        Rule::boolean => Pattern {
            annotation: None,
            kind: PatKind::Lit(Lit::Bool(pair.as_str() == "true")),
        },
        Rule::integer | Rule::float => Pattern {
            annotation: None,
            kind: PatKind::Lit(number_lit(pair.as_str())),
        },
        Rule::string => Pattern {
            annotation: None,
            kind: PatKind::Lit(Lit::Str(unescape_str(pair.as_str()))),
        },
        // `_` and any fallback: wildcard.
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
                kind: PatKind::Spread(inner.into_inner().next().unwrap().as_str().to_string()),
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
                rest = Some(inner.into_inner().next().unwrap().as_str().to_string())
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
        Rule::boolean => Expr::Lit(LitExpr {
            value: Lit::Bool(pair.as_str() == "true"),
        }),
        Rule::string => Expr::Lit(LitExpr {
            value: Lit::Str(unescape_str(pair.as_str())),
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
        Rule::match_expr => match_expr(pair),
        Rule::tuple => tuple(pair),
        Rule::unit => Expr::Tuple(TupleExpr { items: Vec::new() }),
        Rule::grouped_expr => expression(pair.into_inner().next().unwrap()),
        Rule::list => list(pair),
        Rule::record_value => record_value(pair),
        Rule::block => block(pair),
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

/// Decode the escape sequences in the interior of a string literal (the
/// grammar guarantees every backslash escape is well-formed).
fn unescape_str(quoted: &str) -> String {
    let inner = &quoted[1..quoted.len() - 1];
    if !inner.contains('\\') {
        return inner.to_string();
    }
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('0') => out.push('\0'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('\'') => out.push('\''),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn assignment(pair: Pair<'_, Rule>) -> Expr {
    // Children are the place (a flat applicative run) and the value.
    let children: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let (place, children) = children.split_at(children.len().saturating_sub(1));
    let place = operand(place.to_vec());
    let value = children.first().map(|p| expression(p.clone())).unwrap_or_else(none_expr);
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
        } else if !is_keyword(inner.as_rule()) {
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
            r if is_keyword(r) => {}
            _ => scrutinee = expression(inner),
        }
    }
    Expr::Match(MatchExpr {
        scrutinee: Box::new(scrutinee),
        arms,
    })
}

/// The guard condition: `guard = { kw_if ~ binop_expr }` — skip the keyword
/// token and lower the condition expression.
fn guard_expr(pair: Pair<'_, Rule>) -> Expr {
    for inner in pair.into_inner() {
        if !is_keyword(inner.as_rule()) {
            return expression(inner);
        }
    }
    none_expr()
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
            Rule::guard => guard = Some(guard_expr(inner)),
            r if is_keyword(r) => {}
            _ => body = expression(inner),
        }
    }
    MatchArm {
        pattern: pat,
        guard,
        body: Box::new(body),
    }
}

/// Infix operator precedence, loosest to tightest: `||`, `&&`, comparisons,
/// additive, multiplicative. The grammar keeps `binop_expr` flat on purpose;
/// this table is the single place where precedence and associativity live.
/// All operators are left-associative.
fn infix_prec(op: &str) -> u8 {
    match op {
        "||" => 1,
        "&&" => 2,
        "==" | "!=" | "<" | ">" | "<=" | ">=" => 3,
        "+" | "-" => 4,
        "*" | "/" | "%" => 5,
        _ => 0,
    }
}

fn binop_expr(pair: Pair<'_, Rule>) -> Expr {
    // Children are a flat mix of operand atoms, prefix/postfix ops, and
    // infix ops (applicative/prefix/postfix are silent). First fold each
    // applicative run into one operand, then fold the operands according to
    // precedence (left-associative within one level). This is a hand-rolled
    // Pratt/precedence-climbing pass: `precedence` is the single source of
    // truth, the flat grammar stays simple.
    let mut operands: Vec<Expr> = Vec::new();
    let mut ops: Vec<String> = Vec::new();
    let mut current: Vec<Pair<'_, Rule>> = Vec::new();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::infix_op {
            operands.push(operand(std::mem::take(&mut current)));
            ops.push(inner.as_str().to_string());
        } else if !is_keyword(inner.as_rule()) {
            current.push(inner);
        }
    }
    operands.push(operand(current));

    precedence_fold(operands, ops)
}

/// Fold flat `operands`/`ops` into a binary tree honoring `infix_prec`,
/// left-associative within one precedence level (precedence climbing).
fn precedence_fold(operands: Vec<Expr>, ops: Vec<String>) -> Expr {
    let mut values: Vec<Expr> = Vec::with_capacity(operands.len());
    let mut operators: Vec<String> = Vec::with_capacity(ops.len());
    let mut operands = operands.into_iter();

    values.push(operands.next().unwrap_or_else(none_expr));
    for op in ops {
        let rhs = operands.next().unwrap_or_else(none_expr);
        while let Some(top) = operators.last() {
            if infix_prec(top) < infix_prec(&op) {
                break;
            }
            let top = operators.pop().unwrap();
            let rhs = values.pop().unwrap();
            let lhs = values.pop().unwrap();
            values.push(Expr::Binary(BinaryExpr {
                op: infix_op(&top),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            }));
        }
        operators.push(op);
        values.push(rhs);
    }
    while let Some(top) = operators.pop() {
        let rhs = values.pop().unwrap();
        let lhs = values.pop().unwrap();
        values.push(Expr::Binary(BinaryExpr {
            op: infix_op(&top),
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }));
    }
    values.pop().unwrap_or_else(none_expr)
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
        _ => BinaryOp::Add,
    }
}

/// A prefix operator in source order (`ref`, `-`, `!`).
#[derive(Debug, Clone, Copy, PartialEq)]
enum PrefixOp {
    Ref,
    Neg,
    Not,
}

impl PrefixOp {
    fn from_str(s: &str) -> PrefixOp {
        match s {
            "ref" => PrefixOp::Ref,
            "-" => PrefixOp::Neg,
            "!" => PrefixOp::Not,
            other => panic!("unexpected prefix op: {other}"),
        }
    }

    /// Wrap `operand` in this prefix operator's AST node.
    fn apply(self, operand: Expr) -> Expr {
        match self {
            PrefixOp::Ref => Expr::Ref(RefExpr {
                inner: Box::new(operand),
            }),
            PrefixOp::Neg => Expr::Unary(UnaryExpr {
                op: UnaryOp::Neg,
                operand: Box::new(operand),
            }),
            PrefixOp::Not => Expr::Unary(UnaryExpr {
                op: UnaryOp::Not,
                operand: Box::new(operand),
            }),
        }
    }
}

/// Fold a flat run of expression children (atoms, prefix ops, postfix ops)
/// into a nested `Expr`. Prefix operators bind the following postfix chain
/// (`ref x + y` is `(ref x) + y`), postfix ops extend the current chain,
/// and adjacent chains are space-separated function application. Used for
/// both `binop_expr` operands and assignment places.
fn operand(items: Vec<Pair<'_, Rule>>) -> Expr {
    let mut iter = items.into_iter().peekable();
    let mut acc: Option<Expr> = None;
    while iter.peek().is_some() {
        let chain = postfix_chain(&mut iter);
        match acc.take() {
            Some(callee) => {
                acc = Some(Expr::Call(CallExpr {
                    callee: Box::new(callee),
                    args: vec![chain],
                }));
            }
            None => acc = Some(chain),
        }
    }
    acc.unwrap_or_else(none_expr)
}

/// Consume exactly one `prefix_op* ~ atom ~ postfix_op*` chain from `iter`.
fn postfix_chain<'a, I>(iter: &mut std::iter::Peekable<I>) -> Expr
where
    I: Iterator<Item = Pair<'a, Rule>>,
{
    // 1. Leading prefix operators (source order).
    let mut prefixes = Vec::new();
    while let Some(item) = iter.peek() {
        if item.as_rule() == Rule::prefix_op {
            prefixes.push(PrefixOp::from_str(item.as_str()));
            iter.next();
        } else {
            break;
        }
    }

    // 2. The atom (absent only for a dangling prefix at end of input).
    let mut acc = match iter.next() {
        Some(item) if item.as_rule() != Rule::prefix_op => expression(item),
        _ => none_expr(),
    };

    // 3. Trailing postfix operators. A postfix op never absorbs a prefix op
    //    that belongs to the next operand (e.g. `n - 1` must not parse the
    //    `-` as a postfix on `n`): only call/member/index continue a chain.
    while let Some(item) = iter.peek() {
        acc = match item.as_rule() {
            Rule::call_args => {
                let args = iter
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(expression)
                    .collect();
                Expr::Call(CallExpr {
                    callee: Box::new(acc),
                    args,
                })
            }
            Rule::member_access => {
                let field = iter
                    .next()
                    .unwrap()
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_str()
                    .to_string();
                Expr::Member(MemberExpr {
                    obj: Box::new(acc),
                    field,
                })
            }
            Rule::index_access => {
                let idx = expression(iter.next().unwrap().into_inner().next().unwrap());
                Expr::Index(IndexExpr {
                    obj: Box::new(acc),
                    index: Box::new(idx),
                })
            }
            _ => break,
        };
    }

    // 4. Apply the prefix operators inside-out: the innermost (rightmost in
    //    source) wraps the postfix chain first.
    for op in prefixes.into_iter().rev() {
        acc = op.apply(acc);
    }
    acc
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

fn record_value(pair: Pair<'_, Rule>) -> Expr {
    let mut entries = Vec::new();
    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::record_value_field => {
                let mut it = inner.into_inner();
                let name = it.next().unwrap().as_str().to_string();
                let value = expression(it.next().unwrap());
                entries.push(RecordValueEntry::Field(name, value));
            }
            Rule::record_value_spread => {
                let value = expression(inner.into_inner().next().unwrap());
                entries.push(RecordValueEntry::Spread(value));
            }
            _ => panic!("unexpected record_value child: {:?}", inner.as_rule()),
        }
    }
    Expr::Record(RecordValueExpr { entries })
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

/// The single non-keyword child of a wrapper rule (e.g. `ty_ref`'s inner
/// type after the `ref` keyword token).
fn sole_child(pair: Pair<'_, Rule>) -> Pair<'_, Rule> {
    pair.into_inner()
        .find(|p| !is_keyword(p.as_rule()))
        .expect("wrapper rule has a non-keyword child")
}

fn type_(pair: Pair<'_, Rule>) -> Ty {
    match pair.as_rule() {
        Rule::ty_ref => Ty::Ref(Box::new(type_(sole_child(pair)))),
        Rule::ty_mut => Ty::Mut(Box::new(type_(sole_child(pair)))),
        Rule::arrow_type => arrow_type(pair),
        Rule::type_base => type_base(pair),
        Rule::named_binder => named_binder(pair),
        other => panic!("unexpected type rule: {other:?}"),
    }
}

fn arrow_type(pair: Pair<'_, Rule>) -> Ty {
    let mut inner = pair.into_inner().filter(|p| !is_keyword(p.as_rule()));
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
    let mut inner = pair.into_inner().filter(|p| !is_keyword(p.as_rule()));
    let name = inner.next().unwrap().as_str().to_string();
    let ty = type_(inner.next().unwrap());
    Ty::NamedBinder {
        name,
        ty: Box::new(ty),
    }
}

fn type_base(pair: Pair<'_, Rule>) -> Ty {
    let kids: Vec<Pair<'_, Rule>> = pair
        .into_inner()
        .filter(|p| !is_keyword(p.as_rule()))
        .collect();
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
