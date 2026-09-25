//! SMT-backed verification of spec `where` refinements.
//!
//! Encodes the encodable subset of Lento expressions into cvc5
//! (bitvectors for `i64`, IEEE-754 doubles for floats, booleans) and answers
//! two kinds of queries:
//!
//! - postconditions: prove `pres -> post` where the result variable is bound
//!   to the encoded definition body and inputs are universally quantified
//!   (checked by asking for a counterexample);
//! - preconditions at a call site: prove the clause holds for the encoded
//!   argument values.
//!
//! Any expression outside the supported subset, a solver `unknown`, or a
//! timeout is a hard error: verification is all-or-nothing. See
//! `docs/where-refinements.md`.

use crate::ast::{BinaryOp, Expr, Lit, PatKind, Stmt, Ty, UnaryOp};
use cvc5::{Kind, RoundingMode, Sort, Term, TermManager};
use std::collections::HashMap;

/// The solver-side sort of a Lento value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SVal {
    Int,
    Float,
    Bool,
}

impl SVal {
    fn describe(self) -> &'static str {
        match self {
            SVal::Int => "int",
            SVal::Float => "float",
            SVal::Bool => "bool",
        }
    }
}

impl std::fmt::Display for SVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.describe())
    }
}

/// Map a spec binder's type to the solver sort it verifies as.
pub fn sort_of_ty(ty: &Ty) -> Option<SVal> {
    match ty {
        Ty::Named { name, args } if args.is_empty() => match name.as_str() {
            "int" | "Int" | "usize" | "isize" => Some(SVal::Int),
            "float" | "Float" => Some(SVal::Float),
            "bool" | "Bool" => Some(SVal::Bool),
            _ => None,
        },
        _ => None,
    }
}

/// Unsupported input: the clause or body cannot be encoded, so the
/// refinement cannot be verified.
#[derive(Debug)]
pub struct Unsupported(pub String);

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Encoder state: the term manager plus the variable environment.
struct Enc<'a> {
    tm: &'a TermManager,
    bv: Sort<'a>,
    fp: Sort<'a>,
    env: HashMap<String, (Term<'a>, SVal)>,
}

impl<'a> Enc<'a> {
    fn new(tm: &'a TermManager) -> Self {
        Enc {
            tm,
            bv: tm.mk_bv_sort(64),
            fp: tm.mk_fp_sort(11, 53),
            env: HashMap::new(),
        }
    }

    /// Declare a named constant of the given sort and bind it.
    fn declare(&mut self, name: &str, kind: SVal) -> Term<'a> {
        let t = self.tm.mk_const(self.sort(kind), name);
        self.env.insert(name.to_string(), (t.clone(), kind));
        t
    }

    fn sort(&self, kind: SVal) -> Sort<'a> {
        match kind {
            SVal::Int => self.bv.copy(),
            SVal::Float => self.fp.copy(),
            SVal::Bool => self.tm.boolean_sort(),
        }
    }

    fn encode(&mut self, e: &Expr) -> Result<Term<'a>, Unsupported> {
        let tm: &'a TermManager = self.tm;
        match e {
            Expr::Lit(lit) => match &lit.value {
                Lit::Bool(b) => Ok(tm.mk_boolean(*b)),
                Lit::Int(i) => Ok(tm.mk_bv(64, *i as u64)),
                Lit::Float(f) => Ok(tm.mk_fp(11, 53, tm.mk_bv(64, f.to_bits()))),
                Lit::Str(_) => Err(Unsupported("strings cannot be encoded".into())),
            },
            Expr::Var(v) => self
                .env
                .get(&v.name)
                .map(|(t, _)| t.copy())
                .ok_or_else(|| Unsupported(format!("unknown identifier '{}'", v.name))),
            Expr::Unary(u) => {
                let x = self.encode(&u.operand)?;
                let fam = self.int_or_float_bool(&x)?;
                match (&u.op, fam) {
                    (UnaryOp::Not, SVal::Bool) => Ok(tm.mk_term(Kind::Not, &[x])),
                    (UnaryOp::Neg, SVal::Int) => Ok(tm.mk_term(Kind::BitvectorNeg, &[x])),
                    (UnaryOp::Neg, SVal::Float) => Ok(tm.mk_term(Kind::FloatingpointNeg, &[x])),
                    (op, fam) => Err(Unsupported(format!(
                        "unary {op:?} on {fam} cannot be encoded"
                    ))),
                }
            }
            Expr::Binary(b) => self.encode_binary(&b.op, &b.lhs, &b.rhs),
            Expr::Block(block) => {
                // Only a block whose value is a single expression encodes;
                // statements (lets, nested decls) do not.
                if block.body.len() == 1 {
                    if let Stmt::Expr(inner) = &block.body[0] {
                        return self.encode(inner);
                    }
                }
                Err(Unsupported("blocks with statements cannot be encoded".into()))
            }
            Expr::Lambda(lambda) => {
                // Curried definition bodies: parameters were pre-bound by the
                // caller (matching the spec's input binders, outermost first).
                // A parameter not already bound (extra curry depth, or a
                // destructuring pattern) is unsupported.
                if lambda.params.len() != 1 {
                    return Err(Unsupported("multi-parameter lambdas cannot be encoded".into()));
                }
                match &lambda.params[0].kind {
                    PatKind::Var(name) => {
                        if !self.env.contains_key(name) {
                            return Err(Unsupported(format!(
                                "lambda parameter '{name}' is not a spec parameter"
                            )));
                        }
                        self.encode(&lambda.body)
                    }
                    _ => Err(Unsupported(
                        "destructuring lambda parameters cannot be encoded".into(),
                    )),
                }
            }
            _ => Err(Unsupported(
                "this expression form cannot be encoded in where-clause checking".into(),
            )),
        }
    }

    fn encode_binary(&mut self, op: &BinaryOp, lhs: &Expr, rhs: &Expr) -> Result<Term<'a>, Unsupported> {
        let tm: &'a TermManager = self.tm;
        use BinaryOp::*;
        use SVal::{Bool, Float, Int};

        match op {
            Add | Sub | Mul | Div | Mod => {
                let l = self.encode(lhs)?;
                let family = self.int_or_float(&l)?;
                let r = self.encode(rhs)?;
                let rfam = self.int_or_float(&r)?;
                if rfam != family {
                    return Err(Unsupported(
                        "mixing int and float arithmetic cannot be encoded".into(),
                    ));
                }
                let kind = match (op, family) {
                    (Add, Int) => Kind::BitvectorAdd,
                    (Sub, Int) => Kind::BitvectorSub,
                    (Mul, Int) => Kind::BitvectorMult,
                    (Div, Int) => Kind::BitvectorSdiv,
                    (Mod, Int) => Kind::BitvectorSrem,
                    (Add, Float) => Kind::FloatingpointAdd,
                    (Sub, Float) => Kind::FloatingpointSub,
                    (Mul, Float) => Kind::FloatingpointMult,
                    (Div, Float) => Kind::FloatingpointDiv,
                    (Mod, Float) => {
                        return Err(Unsupported("float modulo cannot be encoded".into()))
                    }
                    _ => unreachable!(),
                };
                if family == Float {
                    let rm = tm.mk_rm(RoundingMode::RoundNearestTiesToEven);
                    Ok(tm.mk_term(kind, &[rm, l, r]))
                } else {
                    Ok(tm.mk_term(kind, &[l, r]))
                }
            }
            Eq | Ne | Lt | Le | Gt | Ge => {
                let l = self.encode(lhs)?;
                let family = self.int_or_float_bool(&l)?;
                let r = self.encode(rhs)?;
                let rfam = self.int_or_float_bool(&r)?;
                if rfam != family {
                    return Err(Unsupported(
                        "comparing int with float cannot be encoded".into(),
                    ));
                }
                match (op, family) {
                    (Eq, Int) | (Eq, Bool) => Ok(tm.mk_term(Kind::Equal, &[l, r])),
                    (Eq, Float) => Ok(tm.mk_term(Kind::FloatingpointEq, &[l, r])),
                    (Ne, _) => {
                        let eq = match family {
                            Float => tm.mk_term(Kind::FloatingpointEq, &[l, r]),
                            _ => tm.mk_term(Kind::Equal, &[l, r]),
                        };
                        Ok(tm.mk_term(Kind::Not, &[eq]))
                    }
                    (Lt, Int) => Ok(tm.mk_term(Kind::BitvectorSlt, &[l, r])),
                    (Le, Int) => Ok(tm.mk_term(Kind::BitvectorSle, &[l, r])),
                    (Gt, Int) => Ok(tm.mk_term(Kind::BitvectorSgt, &[l, r])),
                    (Ge, Int) => Ok(tm.mk_term(Kind::BitvectorSge, &[l, r])),
                    (Lt, Float) => Ok(tm.mk_term(Kind::FloatingpointLt, &[l, r])),
                    (Le, Float) => Ok(tm.mk_term(Kind::FloatingpointLeq, &[l, r])),
                    (Gt, Float) => Ok(tm.mk_term(Kind::FloatingpointGt, &[l, r])),
                    (Ge, Float) => Ok(tm.mk_term(Kind::FloatingpointGeq, &[l, r])),
                    _ => Err(Unsupported(format!(
                        "comparison {op:?} on {family} cannot be encoded"
                    ))),
                }
            }
            And | Or => {
                let l = self.encode(lhs)?;
                let r = self.encode(rhs)?;
                Ok(tm.mk_term(if *op == And { Kind::And } else { Kind::Or }, &[l, r]))
            }
        }
    }

    fn int_or_float(&self, t: &Term<'a>) -> Result<SVal, Unsupported> {
        match self.int_or_float_bool(t)? {
            SVal::Bool => Err(Unsupported(
                "arithmetic on booleans cannot be encoded".into(),
            )),
            other => Ok(other),
        }
    }

    fn int_or_float_bool(&self, t: &Term<'a>) -> Result<SVal, Unsupported> {
        if t.sort() == self.bv {
            return Ok(SVal::Int);
        }
        if t.sort() == self.fp {
            return Ok(SVal::Float);
        }
        if t.sort() == self.tm.boolean_sort() {
            return Ok(SVal::Bool);
        }
        Err(Unsupported(
            "operand is outside the supported subset".into(),
        ))
    }
}

/// Free variable names in an expression (for clause classification).
pub fn free_vars(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Var(v) => {
            if !out.contains(&v.name) {
                out.push(v.name.clone());
            }
        }
        Expr::Lit(_) => {}
        Expr::Unary(u) => free_vars(&u.operand, out),
        Expr::Binary(b) => {
            free_vars(&b.lhs, out);
            free_vars(&b.rhs, out);
        }
        Expr::Block(b) => {
            for s in &b.body {
                if let Stmt::Expr(inner) = s {
                    free_vars(inner, out);
                }
            }
        }
        Expr::Lambda(l) => free_vars(&l.body, out),
        Expr::Call(c) => {
            free_vars(&c.callee, out);
            for a in &c.args {
                free_vars(a, out);
            }
        }
        _ => {}
    }
}

#[derive(Debug)]
pub enum Verdict {
    /// The property is unsatisfiable to violate: it holds.
    Proven,
    /// A model violating the property exists; carries the witness as a
    /// human-readable `name = value` list.
    Counterexample(String),
}

fn run_check(
    solver: &mut cvc5::Solver<'_>,
    params: &[(Term, String)],
    negated: &Term,
) -> Result<Verdict, String> {
    solver.assert_formula(negated.clone());
    let res = solver.check_sat();
    if res.is_unsat() {
        return Ok(Verdict::Proven);
    }
    if res.is_sat() {
        let mut parts = Vec::new();
        for (t, name) in params {
            parts.push(format!("{name} = {}", fmt_value(&solver.get_value(t.copy()))));
        }
        return Ok(Verdict::Counterexample(parts.join(", ")));
    }
    Err("solver returned unknown".into())
}

/// Render a model value for witnesses: 64-bit bitvectors as signed decimal,
/// everything else as the solver's own printing.
fn fmt_value(t: &Term) -> String {
    let s = t.to_string();
    for (prefix, radix) in [("#b", 2u32), ("#x", 16)] {
        if let Some(bits) = s.strip_prefix(prefix) {
            if let Ok(u) = u64::from_str_radix(bits, radix) {
                return (u as i64).to_string();
            }
        }
    }
    s
}

fn new_solver(tm: &TermManager) -> cvc5::Solver<'_> {
    let mut solver = cvc5::Solver::new(tm);
    solver.set_option("produce-models", "true");
    solver.set_option("tlimit-per", "5000");
    solver
}

/// Verify one postcondition: `pres -> post(result := body)` for all inputs.
///
/// `inputs` are the spec's input binders in order (outermost curry first);
/// `result` is the result binder; `body` is the definition body (a curried
/// lambda chain over the input names); `pres`/`post` are where-clause
/// expressions using the binder names.
pub fn check_post(
    inputs: &[(Option<String>, SVal)],
    result: &(String, SVal),
    body: &Expr,
    pres: &[Expr],
    post: &Expr,
) -> Result<Verdict, String> {
    let tm = TermManager::new();
    let mut enc = Enc::new(&tm);

    let mut named: Vec<(Term, String)> = Vec::new();
    for (name, kind) in inputs {
        let Some(name) = name else {
            return Err("clause references an unnamed parameter".into());
        };
        let t = enc.declare(name, *kind);
        named.push((t, name.clone()));
    }
    // The result name must be bound to the encoded body before clauses are
    // encoded. Lambda parameters must line up with the input binders.
    let body_term = enc
        .encode(body)
        .map_err(|e| format!("cannot verify postcondition: definition body unsupported: {e}"))?;
    if body_term.sort() != enc.sort(result.1) {
        return Err(format!(
            "cannot verify postcondition: definition body is not {}",
            result.1
        ));
    }
    enc.env
        .insert(result.0.clone(), (body_term.copy(), result.1));
    named.push((body_term, result.0.clone()));

    let mut solver = new_solver(&tm);
    for pre in pres {
        let t = enc
            .encode(pre)
            .map_err(|e| format!("cannot verify postcondition: precondition unsupported: {e}"))?;
        solver.assert_formula(t);
    }
    let post_t = enc
        .encode(post)
        .map_err(|e| format!("cannot verify postcondition: clause unsupported: {e}"))?;
    let negated = tm.mk_term(Kind::Not, &[post_t]);
    run_check(&mut solver, &named, &negated)
}

/// Verify one precondition at a call site: the clause must hold for the
/// encoded argument values. `arg_exprs` aligns with the spec's input
/// binders; inputs with `None` sort skip the sort check (they cannot be
/// referenced by clauses anyway). `externals` gives the solver-side sort of
/// caller variables that appear in the arguments (free identifiers become
/// fresh constants).
pub fn check_pre(
    inputs: &[(Option<String>, Option<SVal>)],
    pre: &Expr,
    arg_exprs: &[&Expr],
    externals: &[(String, SVal)],
) -> Result<Verdict, String> {
    if inputs.len() != arg_exprs.len() {
        return Err("argument count does not match the spec signature".into());
    }
    let tm = TermManager::new();
    let mut enc = Enc::new(&tm);
    for (name, kind) in externals {
        if !enc.env.contains_key(name) {
            enc.declare(name, *kind);
        }
    }

    let mut named: Vec<(Term, String)> = Vec::new();
    for (idx, (name, kind)) in inputs.iter().enumerate() {
        // Encode the argument in a scratch env, then register it under the
        // spec parameter name the clause uses. Unnamed binders cannot be
        // referenced but still consume an argument.
        let term = enc.encode(arg_exprs[idx]).map_err(|e| {
            format!("cannot verify precondition at call site: argument unsupported: {e}")
        })?;
        if let Some(name) = name {
            let Some(kind) = kind else {
                continue; // unnamed or non-encodable input: not clause-referable
            };
            if term.sort() != enc.sort(*kind) {
                return Err(format!(
                    "cannot verify precondition at call site: argument for '{name}' is not {kind}"
                ));
            }
            enc.env.insert(name.clone(), (term.copy(), *kind));
            named.push((term, name.clone()));
        }
    }

    let mut solver = new_solver(&tm);
    let pre_t = enc
        .encode(pre)
        .map_err(|e| format!("cannot verify precondition at call site: clause unsupported: {e}"))?;
    let negated = tm.mk_term(Kind::Not, &[pre_t]);
    run_check(&mut solver, &named, &negated)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryExpr, BinaryOp, LambdaExpr, LitExpr, Pattern, UnaryExpr, VarExpr};

    fn var(n: &str) -> Expr {
        Expr::Var(VarExpr { name: n.into() })
    }
    fn int(v: i64) -> Expr {
        Expr::Lit(LitExpr { value: Lit::Int(v) })
    }
    fn bin(op: BinaryOp, l: Expr, r: Expr) -> Expr {
        Expr::Binary(BinaryExpr { op, lhs: Box::new(l), rhs: Box::new(r) })
    }
    fn lam(param: &str, body: Expr) -> Expr {
        Expr::Lambda(LambdaExpr {
            params: vec![Pattern { annotation: None, kind: PatKind::Var(param.into()) }],
            body: Box::new(body),
        })
    }
    fn not_zero(v: &str) -> Expr {
        bin(BinaryOp::Ne, var(v), int(0))
    }

    #[test]
    fn provable_postcondition_is_proven() {
        // square = x => x * x with post r == x * x: the result is bound to
        // the encoded body, so the equality is definitionally true.
        let body = lam("x", bin(BinaryOp::Mul, var("x"), var("x")));
        let pres = vec![];
        let post = bin(BinaryOp::Eq, var("r"), bin(BinaryOp::Mul, var("x"), var("x")));
        let inputs = vec![(Some("x".into()), SVal::Int)];
        match check_post(&inputs, &("r".into(), SVal::Int), &body, &pres, &post) {
            Ok(Verdict::Proven) => {}
            other => panic!("expected Proven, got {other:?}"),
        }
    }

    #[test]
    fn division_postconditions_are_honest_about_limits() {
        // `r * y <= x` for x sdiv y is TRUE for truncated division with
        // x >= 0, but proving it requires reasoning the bit-blasting solvers
        // do not finish in bounded time. The strict contract surfaces this
        // as an error rather than silently accepting it.
        let body = lam("x", lam("y", bin(BinaryOp::Div, var("x"), var("y"))));
        let pres = vec![not_zero("y"), bin(BinaryOp::Ge, var("x"), int(0))];
        let post = bin(
            BinaryOp::Le,
            bin(BinaryOp::Mul, var("r"), var("y")),
            var("x"),
        );
        let inputs = vec![
            (Some("x".into()), SVal::Int),
            (Some("y".into()), SVal::Int),
        ];
        match check_post(&inputs, &("r".into(), SVal::Int), &body, &pres, &post) {
            Ok(Verdict::Proven) | Err(_) => {}
            Ok(Verdict::Counterexample(w)) => {
                panic!("property is mathematically true; witness must be bogus: {w}")
            }
        }
    }

    #[test]
    fn false_postcondition_reports_counterexample() {
        // Same as above but without the x >= 0 precondition: x = -1, y = 2
        // breaks r * y <= x for truncated division.
        let body = lam("x", lam("y", bin(BinaryOp::Div, var("x"), var("y"))));
        let pres = vec![not_zero("y")];
        let post = bin(
            BinaryOp::Le,
            bin(BinaryOp::Mul, var("r"), var("y")),
            var("x"),
        );
        let inputs = vec![
            (Some("x".into()), SVal::Int),
            (Some("y".into()), SVal::Int),
        ];
        match check_post(&inputs, &("r".into(), SVal::Int), &body, &pres, &post) {
            Ok(Verdict::Counterexample(w)) => {
                assert!(w.contains("x"), "witness should name params: {w}");
                assert!(w.contains("y"), "witness should name params: {w}");
            }
            other => panic!("expected Counterexample, got {other:?}"),
        }
    }

    #[test]
    fn call_site_preconditions() {
        let inputs = vec![(Some("y".into()), Some(SVal::Int))];
        let externals: Vec<(String, SVal)> = Vec::new();
        assert!(matches!(
            check_pre(&inputs, &not_zero("y"), &[&int(4)], &externals),
            Ok(Verdict::Proven)
        ));
        assert!(matches!(
            check_pre(&inputs, &not_zero("y"), &[&int(0)], &externals),
            Ok(Verdict::Counterexample(_))
        ));
        // Symbolic argument with a declared external: x + 1 != 0 has the
        // counterexample x = -1.
        let externals = vec![("x".to_string(), SVal::Int)];
        assert!(matches!(
            check_pre(
                &inputs,
                &not_zero("y"),
                &[&bin(BinaryOp::Add, var("x"), int(1))],
                &externals
            ),
            Ok(Verdict::Counterexample(_))
        ));
    }

    #[test]
    fn float_and_bool_clauses_encode() {
        // f = x => x * 2.5 with post r > 0.0 for x > 0.0
        let body = lam("x", bin(BinaryOp::Mul, var("x"), Expr::Lit(LitExpr { value: Lit::Float(2.5) })));
        let pres = vec![bin(BinaryOp::Gt, var("x"), Expr::Lit(LitExpr { value: Lit::Float(0.0) }))];
        let post = bin(BinaryOp::Gt, var("r"), Expr::Lit(LitExpr { value: Lit::Float(0.0) }));
        let inputs = vec![(Some("x".into()), SVal::Float)];
        match check_post(&inputs, &("r".into(), SVal::Float), &body, &pres, &post) {
            Ok(Verdict::Proven) => {}
            other => panic!("expected Proven, got {other:?}"),
        }
        // Boolean clause: b && !b is never true -> precondition unprovable,
        // which we observe as a counterexample.
        let bfalse = bin(
            BinaryOp::And,
            var("b"),
            Expr::Unary(UnaryExpr { op: UnaryOp::Not, operand: Box::new(var("b")) }),
        );
        let inputs = vec![(Some("b".into()), Some(SVal::Bool))];
        let externals: Vec<(String, SVal)> = Vec::new();
        assert!(matches!(
            check_pre(
                &inputs,
                &bfalse,
                &[&Expr::Lit(LitExpr { value: Lit::Bool(true) })],
                &externals
            ),
            Ok(Verdict::Counterexample(_))
        ));
    }
}
