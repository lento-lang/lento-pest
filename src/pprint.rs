// Pretty printer for the Lento AST.
//
// `format_program` walks a parsed `Program` and emits the source code it
// represents. It is the inverse of `lento::parser::parse_program`: parse ->
// format recovers readable Lento code. Comments, insignificant whitespace,
// and the original grouping are not stored in the AST, so the output is
// semantically equivalent but not byte-identical to the input.
//
// Round-trip identity (format(parse(x)) reparses to the same tree) holds for
// well-formed programs. Two pre-existing grammar properties bound what can
// round-trip:
//
// 1. The parser folds all binary expressions flat and left-associative with
//    no operator precedence. A mixed-precedence expression such as
//    `1 + 2 * 3` binds as `(1 + 2) * 3`; the printer restores grouping with
//    parentheses, but Lento has no transparent single-expression parens
//    (a bare `(expr)` is a 1-tuple), so such a recovered tree cannot be
//    re-encoded losslessly. Same-precedence and unambiguous programs
//    round-trip exactly.
// 2. A `fn` clause following a spec's `where` block is absorbed into the
//    where conditions (no statement boundary after a where block), so such
//    a program is not printer-round-trippable either.

use std::fmt::Write;

use crate::ast::*;

/// Render a program back into Lento source text.
pub fn format_program(program: &Program) -> String {
    let mut out = String::new();
    for stmt in &program.statements {
        format_stmt(&mut out, stmt);
        out.push('\n');
    }
    out
}

fn format_stmt(out: &mut String, stmt: &Stmt) {
    match stmt {
        Stmt::Decl(decl) => format_decl(out, decl),
        Stmt::Expr(expr) => format_expr(out, expr, Prec::Top),
    }
}

fn format_decl(out: &mut String, decl: &Decl) {
    match decl {
        Decl::Spec(spec) => {
            let _ = writeln!(out, "spec {}:", spec.name);
            format_spec_type(out, &spec.ty);
        }
        Decl::Type(t) => {
            let _ = write!(out, "type {} = ", t.name);
            format_type(out, &t.ty);
            out.push('\n');
        }
        Decl::Let(l) => {
            let _ = write!(out, "let ");
            if l.mutable {
                out.push_str("mut ");
            }
            format_pattern(out, &l.pattern);
            if let Some(ty) = &l.annotation {
                let _ = write!(out, " : ");
                format_type(out, ty);
            }
            let _ = write!(out, " = ");
            format_expr(out, &l.value, Prec::Top);
            out.push('\n');
        }
        // `fn` prints in its source form, one clause per declaration. The
        // evaluator desugars it (see `desugar_program`), but the printer is
        // faithful to what the user wrote so files round-trip.
        Decl::Fn(f) => {
            let _ = write!(out, "fn {} ", f.name);
            for p in &f.params {
                format_pattern(out, p);
                out.push(' ');
            }
            if let Some(ty) = &f.ret {
                let _ = write!(out, "-> ");
                format_type(out, ty);
                out.push(' ');
            }
            if matches!(f.body, Expr::Block(_)) {
                format_expr(out, &f.body, Prec::Top);
            } else {
                let _ = write!(out, "= ");
                format_expr(out, &f.body, Prec::Top);
            }
            out.push('\n');
        }
    }
}

fn format_spec_type(out: &mut String, st: &SpecType) {
    for q in &st.quantifiers {
        let _ = write!(out, "    all {}", q.vars.join(", "),);
        if !q.constraints.is_empty() {
            let cs: Vec<String> = q
                .constraints
                .iter()
                .map(|c| {
                    let mut s = c.name.clone();
                    if !c.args.is_empty() {
                        let args: Vec<String> = c.args.iter().map(type_str).collect();
                        let _ = write!(s, " {}", args.join(", "));
                    }
                    s
                })
                .collect();
            let _ = write!(out, " :: {}", cs.join(", "),);
        }
        out.push_str(".\n");
    }
    let _ = write!(out, "    ");
    format_type(out, &st.ty);
    out.push('\n');
    if let Some(conds) = &st.where_ {
        let _ = write!(out, "    where ");
        for (i, c) in conds.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            format_expr(out, c, Prec::Top);
        }
        out.push('\n');
    }
}

/// Render a type into its own `String` (used to build joined pieces).
fn type_str(t: &Ty) -> String {
    let mut s = String::new();
    format_type(&mut s, t);
    s
}

fn format_type(out: &mut String, ty: &Ty) {
    match ty {
        Ty::Named { name, args } => {
            let _ = write!(out, "{name}");
            if !args.is_empty() {
                let as_: Vec<String> = args.iter().map(type_str).collect();
                let _ = write!(out, "<{}>", as_.join(", "));
            }
        }
        Ty::Tuple(tys) => {
            let pieces: Vec<String> = tys.iter().map(type_str).collect();
            let _ = write!(out, "({})", pieces.join(", "));
        }
        Ty::List(inner) => {
            let _ = write!(out, "[");
            format_type(out, inner);
            out.push(']');
        }
        Ty::Arrow { from, to } => {
            let from = arrow_domain_str(from);
            let _ = write!(out, "{from} -> ");
            format_type(out, to);
        }
        Ty::Ref(inner) => {
            let _ = write!(out, "ref ");
            format_type(out, inner);
        }
        Ty::Mut(inner) => {
            let _ = write!(out, "mut ");
            format_type(out, inner);
        }
        Ty::NamedBinder { name, ty } => {
            let _ = write!(out, "({name} : ");
            format_type(out, ty);
            out.push(')');
        }
    }
}

/// The left side of an arrow must be a single atom; wrap if compound.
fn arrow_domain_str(t: &Ty) -> String {
    match t {
        Ty::Arrow { .. } => format!("({})", type_str(t)),
        _ => type_str(t),
    }
}

fn format_pattern(out: &mut String, pat: &Pattern) {
    format_pat_kind(out, &pat.kind, pat.annotation.as_ref());
}

fn format_pat_kind(out: &mut String, kind: &PatKind, annotation: Option<&Ty>) {
    match kind {
        PatKind::Var(name) => {
            let bare = name.clone();
            render_pat_atom(out, &bare, annotation);
        }
        PatKind::Wildcard => render_pat_atom(out, "_", annotation),
        PatKind::Lit(lit) => {
            let s = format_lit(lit);
            render_pat_atom(out, &s, annotation);
        }
        PatKind::Tuple(pats) => {
            let inner: Vec<String> = pats.iter().map(pat_str).collect();
            let body = format!("({})", inner.join(", "));
            render_pat_atom(out, &body, annotation);
        }
        PatKind::List(pats) => {
            let inner: Vec<String> = pats.iter().map(pat_str).collect();
            let body = format!("[{}]", inner.join(", "));
            render_pat_atom(out, &body, annotation);
        }
        PatKind::Spread(inner) => {
            let body = format!("...{}", pat_str(inner));
            render_pat_atom(out, &body, annotation);
        }
        PatKind::Record { fields, rest } => {
            let mut inner: Vec<String> = fields
                .iter()
                .map(|f| format!("{}: {}", f.name, pat_str(&f.pattern)))
                .collect();
            if let Some(rest) = rest {
                inner.push(format!("...{}", pat_str(rest)));
            }
            let body = format!("{{{}}}", inner.join(", "));
            render_pat_atom(out, &body, annotation);
        }
    }
}

/// Render a pattern into its own `String`.
fn pat_str(p: &Pattern) -> String {
    let mut s = String::new();
    format_pattern(&mut s, p);
    s
}

/// A pattern with an annotation renders as `(atom : T)`.
fn render_pat_atom(out: &mut String, atom: &str, annotation: Option<&Ty>) {
    if let Some(ty) = annotation {
        let _ = write!(out, "({} : ", atom);
        format_type(out, ty);
        out.push(')');
    } else {
        out.push_str(atom);
    }
}

// --------------------------------------------------------------------------
// Expressions
// --------------------------------------------------------------------------

/// Binary operator precedence (higher binds tighter). Used to restore
/// grouping that the left-fold parser loses.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum Prec {
    Top,   // statement / argument context: lowest, allows any infix
    Or,
    And,
    Cmp,
    Cons,
    Add,
    Mul,
    Atom, // atomic operand: never needs parens
}

fn binary_prec(op: &BinaryOp) -> Prec {
    match op {
        BinaryOp::Or => Prec::Or,
        BinaryOp::And => Prec::And,
        BinaryOp::Eq
        | BinaryOp::Ne
        | BinaryOp::Lt
        | BinaryOp::Gt
        | BinaryOp::Le
        | BinaryOp::Ge => Prec::Cmp,
        BinaryOp::Cons => Prec::Cons,
        BinaryOp::Add | BinaryOp::Sub => Prec::Add,
        BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => Prec::Mul,
    }
}

fn op_symbol(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Mod => "%",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Gt => ">",
        BinaryOp::Le => "<=",
        BinaryOp::Ge => ">=",
        BinaryOp::And => "&&",
        BinaryOp::Or => "||",
        BinaryOp::Cons => "::",
    }
}

/// Print an expression, parenthesizing it if its precedence is weaker than
/// `ctx` (so it composes correctly inside a larger expression).
fn format_expr(out: &mut String, expr: &Expr, ctx: Prec) {
    let mut buf = String::new();
    format_expr_inner(&mut buf, expr, ctx);
    let needs_paren = match expr {
        Expr::Binary(b) => binary_prec(&b.op) < ctx,
        _ => false,
    };
    if needs_paren {
        let _ = write!(out, "({buf})");
    } else {
        out.push_str(&buf);
    }
}

fn format_expr_inner(out: &mut String, expr: &Expr, ctx: Prec) {
    match expr {
        Expr::Lit(lit) => out.push_str(&format_lit(&lit.value)),
        Expr::Var(v) => out.push_str(&v.name),
        Expr::Ref(r) => {
            out.push_str("ref ");
            format_expr(out, &r.inner, Prec::Atom);
        }
        Expr::Assign(a) => {
            format_expr(out, &a.place, Prec::Top);
            out.push_str(" = ");
            format_expr(out, &a.value, Prec::Top);
        }
        Expr::Lambda(l) => {
            let params: Vec<String> = l.params.iter().map(pat_str).collect();
            let _ = write!(out, "{} => ", params.join(" "));
            format_expr(out, &l.body, Prec::Top);
        }
        Expr::Call(c) => format_call(out, c),
        Expr::Member(m) => {
            format_expr(out, &m.obj, Prec::Atom);
            let _ = write!(out, ".{}", m.field);
        }
        Expr::Index(ix) => {
            format_expr(out, &ix.obj, Prec::Atom);
            out.push('[');
            format_expr(out, &ix.index, Prec::Top);
            out.push(']');
        }
        Expr::Unary(u) => {
            match u.op {
                UnaryOp::Not => out.push('!'),
                UnaryOp::Neg => out.push('-'),
            }
            format_expr(out, &u.operand, Prec::Atom);
        }
        Expr::Binary(b) => {
            let p = binary_prec(&b.op);
            format_expr(out, &b.lhs, p);
            let _ = write!(out, " {} ", op_symbol(&b.op));
            // Right side of equal-or-higher precedence gets parens to
            // preserve the original left-associative grouping.
            format_expr(out, &b.rhs, next_tighter(p));
        }
        Expr::Tuple(t) => {
            let items: Vec<String> = t.items.iter().map(expr_str_top).collect();
            let _ = write!(out, "({})", items.join(", "));
        }
        Expr::List(l) => format_list(out, l),
        Expr::Block(b) => {
            out.push_str("{\n");
            for stmt in &b.body {
                out.push_str("    ");
                let mut line = String::new();
                format_stmt(&mut line, stmt);
                out.push_str(line.trim_end());
                out.push('\n');
            }
            out.push('}');
        }
        Expr::Match(m) => {
            out.push_str("match ");
            format_expr(out, &m.scrutinee, Prec::Top);
            out.push_str(" {\n");
            for arm in &m.arms {
                out.push_str("    ");
                format_pattern(out, &arm.pattern);
                if let Some(g) = &arm.guard {
                    out.push_str(" if ");
                    format_expr(out, g, Prec::Top);
                }
                out.push_str(" => ");
                format_expr(out, &arm.body, Prec::Top);
                out.push('\n');
            }
            out.push('}');
        }
    }
    let _ = ctx; // ctx read to force paren grouping at call sites above
}

/// Print a call as juxtaposed application, `f a b c`. Nested calls from
/// curried application (`f x y` = `Call(Call(f, x), [y])`) are flattened so
/// the output is the idiomatic space-separated form, which re-parses to the
/// same tree. A non-atomic argument (binary, lambda, call) is parenthesized
/// so application grouping is preserved.
fn format_call(out: &mut String, call: &CallExpr) {
    // Flatten the curried callee chain into a base and an argument list.
    let mut args: Vec<&Expr> = call.args.iter().collect();
    let mut base = &call.callee;
    loop {
        match base.as_ref() {
            Expr::Call(inner) => {
                let mut tmp: Vec<&Expr> = inner.args.iter().collect();
                tmp.extend(args);
                args = tmp;
                base = &inner.callee;
            }
            _ => break,
        }
    }
    format_expr(out, base, Prec::Atom);
    for arg in args {
        out.push(' ');
        let atomic = matches!(
            arg,
            Expr::Var(_)
                | Expr::Lit(_)
                | Expr::Member(_)
                | Expr::Index(_)
                | Expr::Tuple(_)
                | Expr::List(_)
                | Expr::Block(_)
                | Expr::Match(_)
        );
        if atomic {
            format_expr(out, arg, Prec::Atom);
        } else {
            out.push('(');
            format_expr(out, arg, Prec::Top);
            out.push(')');
        }
    }
}

fn next_tighter(p: Prec) -> Prec {
    match p {
        Prec::Top => Prec::Top,
        Prec::Or => Prec::And,
        Prec::And => Prec::Cmp,
        Prec::Cmp => Prec::Cons,
        Prec::Cons => Prec::Add,
        Prec::Add => Prec::Mul,
        Prec::Mul => Prec::Atom,
        Prec::Atom => Prec::Atom,
    }
}

/// A list is stored as cons cells; print a proper list back as `[a, b, c]`.
fn format_list(out: &mut String, list: &ListExpr) {
    let mut items = Vec::new();
    let mut cur = list;
    while let ListExpr::Cells(c) = cur {
        items.push(expr_str_top(&c.head));
        cur = &c.tail;
    }
    if items.is_empty() {
        out.push_str("[]");
    } else {
        let _ = write!(out, "[{}]", items.join(", "));
    }
}

fn format_lit(lit: &Lit) -> String {
    match lit {
        Lit::Bool(b) => b.to_string(),
        Lit::Int(i) => i.to_string(),
        Lit::Float(f) => f.to_string(),
        Lit::Str(s) => format!("\"{}\"", s),
    }
}

/// Render an expression as a top-level (argument-position) string.
fn expr_str_top(e: &Expr) -> String {
    let mut s = String::new();
    format_expr(&mut s, e, Prec::Top);
    s
}
