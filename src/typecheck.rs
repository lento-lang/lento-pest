// Hindley–Milner type inference for Lento.
//
// The checker runs on the *desugared* program (fn clauses are already
// lambdas + match), so the core language is: literals, variables, lambdas,
// calls, tuples, lists, records, member access, indexing, unary/binary
// operators, match, blocks, let, assignment, and ref.
//
// Extensions over vanilla HM:
// - generative user datatypes (`type Option a = [Some a | None]`) with
//   constructor applications and constructor patterns,
// - hybrid sums with implicit bare-member injection (`type X = [int | str]`
//   and `let x: X = 5` / `match x { (n: int) => ... }`),
// - record types with a row variable for field access on unknown records,
// - builtin constraint classes (`Num`, `Ord`, `Eq`, `Add`, `Concat`, `Seq`,
//   `Len`, `Haystack`) modeling the overloaded intrinsics and operators,
// - `spec` declarations checked against their definitions (skolemized),
// - a value restriction on let-generalization (soundness with ref/mut).

use std::collections::{HashMap, HashSet};

use crate::ast::{
    BinaryOp, Decl, Expr, Lit, PatKind, Pattern, Program, Stmt, SumAlt, Ty, UnaryOp,
};
use crate::ty::{
    Class, Con, Constraint, RecordType, Scheme, SolveResult, Subst, SumType, Type, TypeAlt, VarId,
};

pub type TypeResult<T> = Result<T, String>;

#[derive(Clone)]
struct CtorDecl {
    type_name: String,
    payload: Option<Ty>,
}

#[derive(Clone)]
struct TypeDeclInfo {
    decl_id: u32,
    name: String,
    params: Vec<String>,
    ty: Ty,
}

#[derive(Clone)]
struct EnvEntry {
    scheme: Scheme,
    mutable: bool,
}

pub struct Checker {
    subst: Subst,
    next_decl: u32,
    /// Block nesting depth: duplicate type/constructor declarations are an
    /// error at the top level but may shadow in nested block scopes.
    scope_depth: usize,
    vars: HashMap<String, EnvEntry>,
    ctors: HashMap<String, CtorDecl>,
    types: HashMap<String, TypeDeclInfo>,
    specs: HashMap<String, Vec<crate::ast::SpecDecl>>,
    pending: Vec<Constraint>,
    span: crate::ast::Span,
}

/// Check a desugared program. Returns a human-readable type error on failure.
pub fn check_program(program: &Program) -> TypeResult<()> {
    let mut checker = Checker {
        subst: Subst::new(),
        next_decl: 0,
        scope_depth: 0,
        vars: HashMap::new(),
        ctors: HashMap::new(),
        types: HashMap::new(),
        specs: HashMap::new(),
        pending: Vec::new(),
        span: crate::ast::Span { line: 0, col: 0 },
    };
    checker.install_intrinsics();
    for (i, stmt) in program.statements.iter().enumerate() {
        checker.span = program
            .spans
            .get(i)
            .copied()
            .unwrap_or(crate::ast::Span { line: 0, col: 0 });
        checker.check_stmt(stmt)?;
    }
    checker.solve_pending()?;
    // Orphan-spec sweep: `check_specs_for` only fires when the definition's
    // let is processed, so a spec declared after its definition would never
    // be verified, and a spec with no matching definition would pass
    // silently. Verify every recorded spec here.
    let spec_names: Vec<String> = checker.specs.keys().cloned().collect();
    for name in spec_names {
        if !checker.vars.contains_key(&name) {
            return Err(checker
                .err(format!("spec for '{name}' has no matching definition")));
        }
        checker.check_specs_for(&name)?;
    }
    Ok(())
}

impl Checker {
    fn err(&self, msg: impl std::fmt::Display) -> String {
        if self.span.line == 0 {
            format!("type error: {msg}")
        } else {
            format!(
                "type error: {} (line {}, col {})",
                msg, self.span.line, self.span.col
            )
        }
    }

    fn fresh(&mut self) -> VarId {
        self.subst.fresh()
    }

    fn var_ty(&mut self) -> Type {
        Type::Var(self.fresh())
    }

    fn con(&self, c: Con) -> Type {
        Type::Con(c)
    }

    // -- builtin environment ------------------------------------------------

    fn install_intrinsics(&mut self) {
        let unit = || Type::Con(Con::Unit);
        let int = || Type::Con(Con::Int);
        let bool_ = || Type::Con(Con::Bool);
        let str_ = || Type::Con(Con::Str);
        let list = |t: Type| Type::List(Box::new(t));
        let arrow = |a: Type, b: Type| Type::Arrow(Box::new(a), Box::new(b));
        let var = |v: VarId| Type::Var(v);
        let class_con = |class: Class, v: VarId| Constraint { class, args: vec![var(v)] };

        let add = |this: &mut Checker, name: &str, scheme: Scheme| {
            this.vars.insert(name.to_string(), EnvEntry { scheme, mutable: false });
        };

        add(self, "print", Scheme { vars: vec![0], constraints: vec![], ty: arrow(var(0), unit()) });
        add(self, "println", Scheme { vars: vec![0], constraints: vec![], ty: arrow(var(0), unit()) });
        add(self, "assert", Scheme::monomorphic(arrow(bool_(), unit())));
        add(self, "len", Scheme {
            vars: vec![0],
            constraints: vec![class_con(Class::Len, 0)],
            ty: arrow(var(0), int()),
        });
        add(self, "concat", Scheme {
            vars: vec![0],
            constraints: vec![class_con(Class::Concat, 0)],
            ty: arrow(var(0), arrow(var(0), var(0))),
        });
        add(self, "head", Scheme { vars: vec![0], constraints: vec![], ty: arrow(list(var(0)), var(0)) });
        add(self, "tail", Scheme { vars: vec![0], constraints: vec![], ty: arrow(list(var(0)), list(var(0))) });
        add(self, "is_empty", Scheme { vars: vec![0], constraints: vec![], ty: arrow(list(var(0)), bool_()) });
        add(self, "abs", Scheme {
            vars: vec![0],
            constraints: vec![class_con(Class::Num, 0)],
            ty: arrow(var(0), var(0)),
        });
        for name in ["min", "max"] {
            add(self, name, Scheme {
                vars: vec![0],
                constraints: vec![class_con(Class::Ord, 0)],
                ty: arrow(var(0), arrow(var(0), var(0))),
            });
        }
        add(self, "to_string", Scheme { vars: vec![0], constraints: vec![], ty: arrow(var(0), str_()) });
        add(self, "parse_int", Scheme::monomorphic(arrow(str_(), int())));
        add(self, "contains", Scheme {
            vars: vec![0, 1],
            constraints: vec![Constraint { class: Class::Haystack, args: vec![var(0), var(1)] }],
            ty: arrow(var(0), arrow(var(1), bool_())),
        });
        for name in ["take", "drop"] {
            add(self, name, Scheme {
                vars: vec![0],
                constraints: vec![class_con(Class::Seq, 0)],
                ty: arrow(int(), arrow(var(0), var(0))),
            });
        }
        add(self, "reverse", Scheme {
            vars: vec![0],
            constraints: vec![class_con(Class::Seq, 0)],
            ty: arrow(var(0), var(0)),
        });
        add(self, "slice", Scheme {
            vars: vec![0],
            constraints: vec![class_con(Class::Seq, 0)],
            ty: arrow(int(), arrow(int(), arrow(var(0), var(0)))),
        });
        add(self, "join", Scheme::monomorphic(arrow(str_(), arrow(list(str_()), str_()))));
        add(self, "split", Scheme::monomorphic(arrow(str_(), arrow(str_(), list(str_())))));
        add(self, "map", Scheme { vars: vec![0, 1], constraints: vec![], ty: arrow(
            arrow(var(0), var(1)),
            arrow(list(var(0)), list(var(1))),
        ) });
        add(self, "filter", Scheme { vars: vec![0], constraints: vec![], ty: arrow(
            arrow(var(0), bool_()),
            arrow(list(var(0)), list(var(0))),
        ) });
        add(self, "foldl", Scheme { vars: vec![0, 1], constraints: vec![], ty: arrow(
            arrow(var(0), arrow(var(1), var(0))),
            arrow(var(0), arrow(list(var(1)), var(0))),
        ) });
        for name in ["any", "all"] {
            add(self, name, Scheme { vars: vec![0], constraints: vec![], ty: arrow(
                arrow(var(0), bool_()),
                arrow(list(var(0)), bool_()),
            ) });
        }
        add(self, "range", Scheme::monomorphic(arrow(int(), arrow(int(), list(int())))));
    }

    // -- statements ---------------------------------------------------------

    fn check_stmt(&mut self, stmt: &Stmt) -> TypeResult<()> {
        match stmt {
            Stmt::Decl(decl) => self.check_decl(decl)?,
            Stmt::Expr(expr) => {
                self.infer(expr)?;
            }
        }
        self.solve_pending()
    }

    fn check_decl(&mut self, decl: &Decl) -> TypeResult<()> {
        match decl {
            Decl::Type(t) => self.register_type(t),
            Decl::Spec(s) => {
                self.specs.entry(s.name.clone()).or_default().push(s.clone());
                Ok(())
            }
            Decl::Let(let_decl) => self.check_let(let_decl),
            Decl::Fn(_) => Err(self.err("unexpected fn declaration; desugar first")),
        }
    }

    fn register_type(&mut self, t: &crate::ast::TypeDecl) -> TypeResult<()> {
        if self.scope_depth == 0 && self.types.contains_key(&t.name) {
            return Err(self.err(format!("duplicate type declaration '{}'", t.name)));
        }
        let decl_id = match &t.ty {
            Ty::Sum(_) => {
                let id = self.fresh_decl();
                for alt in sum_alts(&t.ty) {
                    if let SumAlt::Ctor { name, payload } = alt {
                        if self.scope_depth == 0 && self.ctors.contains_key(name) {
                            return Err(self.err(format!("duplicate constructor '{name}'")));
                        }
                        self.ctors.insert(
                            name.clone(),
                            CtorDecl {
                                type_name: t.name.clone(),
                                payload: payload.clone(),
                            },
                        );
                    }
                }
                Some(id)
            }
            _ => None,
        };
        self.types.insert(
            t.name.clone(),
            TypeDeclInfo {
                decl_id: decl_id.unwrap_or(0),
                name: t.name.clone(),
                params: t.params.clone(),
                ty: t.ty.clone(),
            },
        );
        Ok(())
    }

    fn fresh_decl(&mut self) -> u32 {
        self.next_decl += 1;
        self.next_decl
    }

    fn check_let(&mut self, let_decl: &crate::ast::LetDecl) -> TypeResult<()> {
        let annotation = match &let_decl.annotation {
            Some(ty) => Some(self.resolve_ty(ty)?),
            None => None,
        };

        // Recursive bindings: pre-bind the name to a fresh variable.
        let name = match &let_decl.pattern.kind {
            PatKind::Var(n) => Some(n.clone()),
            _ => None,
        };
        let rec_var = name.as_ref().map(|_| self.var_ty());
        if let (Some(n), Some(rv)) = (&name, &rec_var) {
            self.vars.insert(
                n.clone(),
                EnvEntry { scheme: Scheme::monomorphic(rv.clone()), mutable: let_decl.mutable },
            );
        }

        let value_ty = self.infer(&let_decl.value)?;

        // Solve what can be solved now; var-dependent constraints remain.
        self.solve_pending()?;

        let binding_ty = match &annotation {
            Some(ann) => {
                // Annotation side first, so bare sum-member injection applies.
                self.subst.unify(ann, &value_ty).map_err(|e| self.err(e))?;
                if let Some(rv) = &rec_var {
                    self.subst.unify(rv, ann).map_err(|e| self.err(e))?;
                }
                ann.clone()
            }
            None => {
                if let Some(rv) = &rec_var {
                    self.subst.unify(rv, &value_ty).map_err(|e| self.err(e))?;
                    rv.clone()
                } else {
                    value_ty.clone()
                }
            }
        };

        // The annotation (or recursive) unifies above may have bound the last
        // free variable of a pending constraint. Solve those now; otherwise
        // `generalize` sees a fully-concrete constraint with no free vars and
        // silently drops it unverified.
        self.solve_pending()?;

        if let Some(n) = &name {
            let generalized = !let_decl.mutable && is_value(&let_decl.value);
            if generalized {
                let (scheme, deferred) = self.generalize(binding_ty.clone(), Some(n));
                self.pending = deferred;
                self.vars
                    .insert(n.clone(), EnvEntry { scheme, mutable: let_decl.mutable });
            } else {
                self.vars.insert(
                    n.clone(),
                    EnvEntry {
                        scheme: Scheme::monomorphic(binding_ty.clone()),
                        mutable: let_decl.mutable,
                    },
                );
            }
        } else {
            // Destructuring let: bind the pattern against the value type.
            let binds = self.pattern_type(&let_decl.pattern)?;
            self.subst
                .unify(&binds.ty, &binding_ty)
                .map_err(|e| self.err(e))?;
            for (n, t) in binds.bindings {
                self.vars.insert(
                    n,
                    EnvEntry { scheme: Scheme::monomorphic(t), mutable: let_decl.mutable },
                );
            }
        }
        if let Some(n) = &name {
            self.check_specs_for(n)?;
        }
        Ok(())
    }

    /// Verify definitions against their `spec` declarations. Spec type
    /// variables are skolemized, so a definition must be at least as
    /// polymorphic as its spec.
    fn check_specs_for(&mut self, name: &str) -> TypeResult<()> {
        let specs = match self.specs.get(name) {
            Some(specs) => specs.clone(),
            None => return Ok(()),
        };
        let entry = self.vars.get(name).cloned();
        let Some(entry) = entry else {
            return Ok(()); // spec without definition: nothing to check yet
        };
        for spec in specs {
            let (declared, spec_constraints) = self.spec_scheme(&spec)?;
            // Conformance runs on a snapshot: the definition type unifies
            // with the skolemized spec, then all bindings roll back so the
            // rigid spec variables never leak into the definition's scheme.
            let snapshot = self.subst.snapshot();
            let conformance = self
                .subst
                .unify(&entry.scheme.ty, &declared.ty)
                .map_err(|e| {
                    self.err(format!(
                        "definition of '{name}' does not match its spec: {e}"
                    ))
                });
            if let Err(e) = conformance {
                self.subst.restore(snapshot);
                return Err(e);
            }
            // Every spec constraint must be provided by the definition.
            for con in &spec_constraints {
                if !self.constraint_covered(con, &entry.scheme) {
                    self.subst.restore(snapshot);
                    return Err(self.err(format!(
                        "definition of '{name}' does not satisfy constraint {con}"
                    )));
                }
            }
            self.subst.restore(snapshot);
        }
        Ok(())
    }

    /// Build the declared type of a spec. Quantified variables are marked
    /// rigid so the definition cannot silently narrow them. Also returns the
    /// spec's `::` constraints for a coverage check against the definition.
    fn spec_scheme(
        &mut self,
        spec: &crate::ast::SpecDecl,
    ) -> TypeResult<(Scheme, Vec<Constraint>)> {
        let mut mapping: HashMap<String, Type> = HashMap::new();
        for quant in &spec.ty.quantifiers {
            for var in &quant.vars {
                let t = self.var_ty();
                self.subst.mark_rigid(match &t {
                    Type::Var(v) => *v,
                    _ => unreachable!(),
                });
                mapping.insert(var.clone(), t);
            }
        }
        let mut spec_constraints = Vec::new();
        for quant in &spec.ty.quantifiers {
            let quant_var_tys: Vec<Type> = quant
                .vars
                .iter()
                .map(|v| mapping.get(v).cloned().expect("quantified var mapped"))
                .collect();
            for c in &quant.constraints {
                let class = builtin_class(&c.name).ok_or_else(|| {
                    self.err(format!("unknown constraint class '{}'", c.name))
                })?;
                // `all a :: Num.` attaches the constraint to the quantified
                // variables implicitly; explicit args are resolved normally.
                let args = if c.args.is_empty() {
                    quant_var_tys.clone()
                } else {
                    c.args
                        .iter()
                        .map(|a| match mapping.get(&ty_var_name(a)) {
                            Some(t) => Ok(t.clone()),
                            None => self.resolve_ty(a),
                        })
                        .collect::<TypeResult<Vec<_>>>()?
                };
                spec_constraints.push(Constraint { class, args });
            }
        }
        let ty = self.resolve_ty_scoped(&spec.ty.ty, &mapping)?;
        Ok((Scheme { vars: Vec::new(), constraints: Vec::new(), ty }, spec_constraints))
    }

    /// Does the definition's scheme provide a constraint of the same class
    /// whose arguments unify with the spec constraint's (pruned) arguments?
    fn constraint_covered(&self, con: &Constraint, def_scheme: &Scheme) -> bool {
        for d in &def_scheme.constraints {
            if d.class != con.class || d.args.len() != con.args.len() {
                continue;
            }
            let mut ok = true;
            for (a, b) in d.args.iter().zip(con.args.iter()) {
                if self.subst.prune(a) != self.subst.prune(b) {
                    // Structural equality after pruning; unbound variables on
                    // the definition side count as covered only when they are
                    // the same variable the spec var was bound to.
                    ok = false;
                    break;
                }
            }
            if ok {
                return true;
            }
        }
        false
    }

    // -- inference ----------------------------------------------------------

    fn infer(&mut self, expr: &Expr) -> TypeResult<Type> {
        match expr {
            Expr::Lit(lit) => Ok(self.lit_ty(&lit.value)),
            Expr::Var(var) => self.infer_var(&var.name),
            Expr::Ref(refexpr) => match refexpr.inner.as_ref() {
                Expr::Var(var) => {
                    let t = self.infer_var(&var.name)?;
                    Ok(Type::Ref(Box::new(t)))
                }
                _ => Err(self.err("ref supports only variable places")),
            },
            Expr::Assign(assign) => {
                let Expr::Var(var) = assign.place.as_ref() else {
                    return Err(self.err("assignment supports only variable places"));
                };
                let entry = self
                    .vars
                    .get(&var.name)
                    .cloned()
                    .ok_or_else(|| self.err(format!("undefined variable '{}'", var.name)))?;
                if !entry.mutable {
                    return Err(self.err(format!(
                        "cannot assign to immutable binding '{}'",
                        var.name
                    )));
                }
                let value_ty = self.infer(&assign.value)?;
                // Mutable lets are monomorphic (value restriction), so the
                // binding's current type is fully known: the assigned value
                // must unify with it, or the invariant carried by the
                // binding's original annotation is silently violated.
                self.subst
                    .unify(&entry.scheme.ty, &value_ty)
                    .map_err(|e| self.err(e))?;
                Ok(self.con(Con::Unit))
            }
            Expr::Lambda(lambda) => {
                let vars = self.vars.clone();
                let result = (|| -> TypeResult<Type> {
                    let mut param_tys = Vec::new();
                    for param in &lambda.params {
                        let binds = self.pattern_type(param)?;
                        for (n, t) in binds.bindings {
                            self.vars.insert(
                                n,
                                EnvEntry {
                                    scheme: Scheme::monomorphic(t.clone()),
                                    mutable: true,
                                },
                            );
                        }
                        param_tys.push(binds.ty);
                    }
                    let body_ty = self.infer(&lambda.body)?;
                    let mut full = body_ty;
                    for param_ty in param_tys.iter().rev() {
                        full = Type::Arrow(Box::new(param_ty.clone()), Box::new(full));
                    }
                    Ok(full)
                })();
                self.vars = vars;
                result
            }
            Expr::Call(call) => self.infer_call(call),
            Expr::Member(member) => self.infer_member(member),
            Expr::Index(index) => self.infer_index(index),
            Expr::Unary(unary) => match unary.op {
                UnaryOp::Not => {
                    let t = self.infer(&unary.operand)?;
                    self.subst
                        .unify(&t, &self.con(Con::Bool))
                        .map_err(|e| self.err(e))?;
                    Ok(self.con(Con::Bool))
                }
                UnaryOp::Neg => {
                    let t = self.infer(&unary.operand)?;
                    self.pending
                        .push(Constraint { class: Class::Num, args: vec![t.clone()] });
                    self.solve_pending()?;
                    Ok(t)
                }
            },
            Expr::Binary(binary) => self.infer_binary(binary),
            Expr::Tuple(tuple) => {
                let mut tys = Vec::with_capacity(tuple.items.len());
                for item in &tuple.items {
                    tys.push(self.infer(item)?);
                }
                Ok(Type::Tuple(tys))
            }
            Expr::List(list) => {
                let heads = list_heads(list);
                let elem = self.var_ty();
                for head in &heads {
                    let t = self.infer(head)?;
                    self.subst.unify(&elem, &t).map_err(|e| self.err(e))?;
                }
                Ok(Type::List(Box::new(elem)))
            }
            Expr::Record(record) => self.infer_record(record),
            Expr::Block(block) => self.infer_block(block),
            Expr::Match(match_expr) => self.infer_match(match_expr),
        }
    }

    fn lit_ty(&self, lit: &Lit) -> Type {
        match lit {
            Lit::Bool(_) => self.con(Con::Bool),
            Lit::Int(_) => self.con(Con::Int),
            Lit::Float(_) => self.con(Con::Float),
            Lit::Str(_) => self.con(Con::Str),
        }
    }

    fn infer_var(&mut self, name: &str) -> TypeResult<Type> {
        if let Some(ctor) = self.ctors.get(name).cloned() {
            if ctor.payload.is_some() {
                return Err(self.err(format!("constructor '{name}' expects one argument")));
            }
            let (_, sum) = self.ctor_instance(name)?;
            return Ok(sum);
        }
        match self.vars.get(name).cloned() {
            Some(entry) => {
                let instantiated = self.instantiate(&entry.scheme);
                for con in instantiated.constraints {
                    self.pending.push(con);
                }
                Ok(instantiated.ty)
            }
            None => Err(self.err(format!("undefined variable '{name}'"))),
        }
    }

    /// Instantiate a constructor: fresh variables for the datatype's type
    /// parameters, shared between the payload type and the resulting sum.
    fn ctor_instance(&mut self, name: &str) -> TypeResult<(Type, Type)> {
        let ctor = self.ctors.get(name).expect("ctor exists").clone();
        let info = self
            .types
            .get(&ctor.type_name)
            .cloned()
            .ok_or_else(|| self.err(format!("unknown type '{}'", ctor.type_name)))?;
        let args: Vec<Type> = info.params.iter().map(|_| self.var_ty()).collect();
        let sum = self.sum_type_from_decl(&info, &args)?;
        let payload = match &ctor.payload {
            Some(p) => {
                let mapping: HashMap<String, Type> = info
                    .params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                self.resolve_ty_scoped(p, &mapping)?
            }
            None => self.con(Con::Unit),
        };
        Ok((payload, sum))
    }

    /// Build the resolved sum type for a datatype declaration given argument
    /// types for its parameters.
    fn sum_type_from_decl(&mut self, info: &TypeDeclInfo, args: &[Type]) -> TypeResult<Type> {
        let mapping: HashMap<String, Type> = info
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let alts = match &info.ty {
            Ty::Sum(alts) => alts,
            _ => return Err(self.err(format!("'{}' is not a sum type", info.name))),
        };
        let mut out = Vec::with_capacity(alts.len());
        for alt in alts {
            out.push(match alt {
                SumAlt::Ctor { name, payload } => TypeAlt::Ctor {
                    name: name.clone(),
                    payload: match payload {
                        Some(p) => self.resolve_ty_scoped(p, &mapping)?,
                        None => self.con(Con::Unit),
                    },
                },
                SumAlt::Bare(ty) => TypeAlt::Bare(self.resolve_ty_scoped(ty, &mapping)?),
            });
        }
        Ok(Type::Sum(SumType {
            id: info.decl_id,
            name: info.name.clone(),
            args: args.to_vec(),
            alts: out,
        }))
    }

    fn infer_call(&mut self, call: &crate::ast::CallExpr) -> TypeResult<Type> {
        // Constructor application: `Some 5`.
        if let Expr::Var(var) = call.callee.as_ref() {
            if let Some(ctor) = self.ctors.get(&var.name).cloned() {
                if ctor.payload.is_some() {
                    if call.args.len() != 1 {
                        return Err(self.err(format!(
                            "constructor '{}' expects 1 argument, got {}",
                            var.name,
                            call.args.len()
                        )));
                    }
                    let (payload, sum) = self.ctor_instance(&var.name)?;
                    let arg_ty = self.infer(&call.args[0])?;
                    self.subst.unify(&payload, &arg_ty).map_err(|e| self.err(e))?;
                    return Ok(sum);
                }
            }
        }
        let mut callee_ty = self.infer(&call.callee)?;
        for arg in &call.args {
            let arg_ty = self.infer(arg)?;
            if matches!(self.subst.prune(&callee_ty), Type::Sum(_)) {
                return Err(self.err("cannot call a sum value (constructor already applied)"));
            }
            let result = self.var_ty();
            self.subst
                .unify(
                    &callee_ty,
                    &Type::Arrow(Box::new(arg_ty), Box::new(result.clone())),
                )
                .map_err(|e| self.err(e))?;
            callee_ty = result;
        }
        Ok(callee_ty)
    }

    fn infer_member(&mut self, member: &crate::ast::MemberExpr) -> TypeResult<Type> {
        let obj_infer = self.infer(&member.obj)?;
        let obj_ty = self.subst.prune(&obj_infer);
        let field_ty = self.var_ty();
        match &obj_ty {
            Type::Record(rec) => {
                if let Some((_, t)) = rec.fields.iter().find(|(n, _)| *n == member.field) {
                    let t = t.clone();
                    self.subst.unify(&t, &field_ty).map_err(|e| self.err(e))?;
                    return Ok(field_ty);
                }
                if rec.rest.is_some() {
                    // Extend the open record with the demanded field.
                    let extension = Type::Record(RecordType {
                        fields: rec.fields.clone(),
                        rest: rec.rest,
                    });
                    let _ = &extension;
                    let grown = Type::Record(RecordType {
                        fields: {
                            let mut fs = rec.fields.clone();
                            fs.push((member.field.clone(), field_ty.clone()));
                            fs
                        },
                        rest: Some(self.fresh()),
                    });
                    self.subst
                        .unify(&obj_ty, &grown)
                        .map_err(|e| self.err(e))?;
                    return Ok(field_ty);
                }
                Err(self.err(format!(
                    "record {} has no field '{}'",
                    obj_ty, member.field
                )))
            }
            Type::Con(Con::Int) | Type::Con(Con::Float) | Type::Con(Con::Str)
                if member.field == "len" =>
            {
                Ok(self.con(Con::Int))
            }
            // `.len` on tuples and lists: concrete types with a Len
            // instance, matching both the len intrinsic and the runtime
            // member access.
            Type::Tuple(_) | Type::List(_) if member.field == "len" => {
                Ok(self.con(Con::Int))
            }
            Type::Var(_) => {
                if member.field == "len" {
                    // `.len` on an unknown type resolves like the len
                    // intrinsic: int, with the container constraint deferred.
                    self.pending
                        .push(Constraint { class: Class::Len, args: vec![obj_ty.clone()] });
                    return Ok(self.con(Con::Int));
                }
                let extension = Type::Record(RecordType {
                    fields: vec![(member.field.clone(), field_ty.clone())],
                    rest: Some(self.fresh()),
                });
                self.subst.unify(&obj_ty, &extension).map_err(|e| self.err(e))?;
                Ok(field_ty)
            }
            other => Err(self.err(format!(
                "cannot access field '{}' on {}",
                member.field, other
            ))),
        }
    }

    fn infer_index(&mut self, index: &crate::ast::IndexExpr) -> TypeResult<Type> {
        let obj_infer = self.infer(&index.obj)?;
        let obj_ty = self.subst.prune(&obj_infer);
        let idx_ty = self.infer(&index.index)?;
        match &obj_ty {
            Type::List(elem) => {
                self.subst
                    .unify(&idx_ty, &self.con(Con::Int))
                    .map_err(|e| self.err(e))?;
                Ok((**elem).clone())
            }
            Type::Con(Con::Str) => {
                self.subst
                    .unify(&idx_ty, &self.con(Con::Int))
                    .map_err(|e| self.err(e))?;
                Ok(self.con(Con::Str))
            }
            Type::Tuple(items) => {
                self.subst
                    .unify(&idx_ty, &self.con(Con::Int))
                    .map_err(|e| self.err(e))?;
                if let Expr::Lit(lit) = index.index.as_ref() {
                    if let Lit::Int(i) = lit.value {
                        return items
                            .get(i as usize)
                            .cloned()
                            .ok_or_else(|| self.err("tuple index out of bounds"));
                    }
                }
                Err(self.err("tuple index must be an integer literal"))
            }
            other => Err(self.err(format!("cannot index {}", other))),
        }
    }

    fn infer_binary(&mut self, binary: &crate::ast::BinaryExpr) -> TypeResult<Type> {
        use BinaryOp::*;
        let op = binary.op.clone();
        if matches!(op, And | Or) {
            let lt = self.infer(&binary.lhs)?;
            let rt = self.infer(&binary.rhs)?;
            self.subst.unify(&lt, &self.con(Con::Bool)).map_err(|e| self.err(e))?;
            self.subst.unify(&rt, &self.con(Con::Bool)).map_err(|e| self.err(e))?;
            return Ok(self.con(Con::Bool));
        }
        let lt = self.infer(&binary.lhs)?;
        let rt = self.infer(&binary.rhs)?;
        self.subst.unify(&lt, &rt).map_err(|e| self.err(e))?;
        let bool_ty = self.con(Con::Bool);
        match op {
            Add => {
                self.pending
                    .push(Constraint { class: Class::Add, args: vec![lt.clone()] });
                self.solve_pending()?;
                Ok(lt)
            }
            Sub | Mul | Div => {
                self.pending
                    .push(Constraint { class: Class::Num, args: vec![lt.clone()] });
                self.solve_pending()?;
                Ok(lt)
            }
            Mod => {
                self.subst.unify(&lt, &self.con(Con::Int)).map_err(|e| self.err(e))?;
                Ok(self.con(Con::Int))
            }
            Eq | Ne => {
                self.pending
                    .push(Constraint { class: Class::Eq, args: vec![lt.clone()] });
                self.solve_pending()?;
                Ok(bool_ty)
            }
            Lt | Gt | Le | Ge => {
                self.pending
                    .push(Constraint { class: Class::Ord, args: vec![lt.clone()] });
                self.solve_pending()?;
                Ok(bool_ty)
            }
            And | Or => unreachable!(),
        }
    }

    fn infer_record(&mut self, record: &crate::ast::RecordValueExpr) -> TypeResult<Type> {
        // Field accumulation in source order: a spread merges the known
        // fields of its operand (unknown fields are opaque and land in the
        // result's row variable); later entries override earlier ones.
        let mut fields: Vec<(String, Type)> = Vec::new();
        // Record literals are closed; only an opaque spread (unknown record
        // operand) keeps the result open via that spread's row variable.
        let mut opaque_rest: Option<VarId> = None;
        for entry in &record.entries {
            match entry {
                crate::ast::RecordValueEntry::Field(name, value) => {
                    let t = self.infer(value)?;
                    if let Some(slot) = fields.iter_mut().find(|(n, _)| *n == *name) {
                        slot.1 = t;
                    } else {
                        fields.push((name.clone(), t));
                    }
                }
                crate::ast::RecordValueEntry::Spread(source) => {
                    let spread_infer = self.infer(source)?;
                    let t = self.subst.prune(&spread_infer);
                    match t {
                        Type::Record(rec) => {
                            let flat = self.subst.flatten_record(&rec);
                            for (name, ft) in flat.fields {
                                if let Some(slot) = fields.iter_mut().find(|(n, _)| *n == name) {
                                    slot.1 = ft;
                                } else {
                                    fields.push((name, ft));
                                }
                            }
                        }
                        Type::Var(_) => {
                            // Unknown record: constrain it to be a record and
                            // keep its row as the result's open rest.
                            let row = self.fresh();
                            let rec = Type::Record(RecordType {
                                fields: Vec::new(),
                                rest: Some(row),
                            });
                            self.subst.unify(&t, &rec).map_err(|e| self.err(e))?;
                            if opaque_rest.is_none() {
                                opaque_rest = Some(row);
                            }
                        }
                        other => {
                            return Err(self.err(format!(
                                "record spread expects a record, got {other}"
                            )));
                        }
                    }
                }
            }
        }
        Ok(Type::Record(RecordType { fields, rest: opaque_rest }))
    }

    fn infer_block(&mut self, block: &crate::ast::BlockExpr) -> TypeResult<Type> {
        let vars = self.vars.clone();
        let ctors = self.ctors.clone();
        let types = self.types.clone();
        let specs = self.specs.clone();
        self.scope_depth += 1;
        let result = (|| -> TypeResult<Type> {
            let mut last = self.con(Con::Unit);
            for stmt in &block.body {
                match stmt {
                    Stmt::Decl(decl) => {
                        self.check_decl(decl)?;
                        last = self.con(Con::Unit);
                    }
                    Stmt::Expr(expr) => {
                        last = self.infer(expr)?;
                    }
                }
            }
            Ok(last)
        })();
        self.scope_depth -= 1;
        self.vars = vars;
        self.ctors = ctors;
        self.types = types;
        self.specs = specs;
        result
    }

    fn infer_match(&mut self, match_expr: &crate::ast::MatchExpr) -> TypeResult<Type> {
        let scrutinee_ty = self.infer(&match_expr.scrutinee)?;
        // A scrutinee that is literally a constructor application pins the
        // tag; arms naming any other constructor can never match.
        let known_tag = scrutinee_ctor_tag(&match_expr.scrutinee, &self.ctors);
        let mut result: Option<Type> = None;
        for arm in &match_expr.arms {
            if let (Some(tag), PatKind::Constructor { name, .. }) =
                (&known_tag, &arm.pattern.kind)
            {
                if name != tag {
                    return Err(self.err(format!(
                        "constructor '{name}' never matches a scrutinee of tag '{tag}'"
                    )));
                }
            }
            let vars = self.vars.clone();
            let ctors = self.ctors.clone();
            let types = self.types.clone();
            let arm_result = (|| -> TypeResult<Type> {
                let binds = self.pattern_type(&arm.pattern)?;
                self.check_pattern_against(&binds.ty, &scrutinee_ty)?;
                for (n, t) in binds.bindings {
                    self.vars
                        .insert(n, EnvEntry { scheme: Scheme::monomorphic(t), mutable: false });
                }
                if let Some(guard) = &arm.guard {
                    let g = self.infer(guard)?;
                    self.subst.unify(&g, &self.con(Con::Bool)).map_err(|e| self.err(e))?;
                }
                self.infer(&arm.body)
            })();
            self.vars = vars;
            self.ctors = ctors;
            self.types = types;
            let body_ty = arm_result?;
            match &result {
                Some(prev) => {
                    let prev = prev.clone();
                    self.subst.unify(&prev, &body_ty).map_err(|e| self.err(e))?;
                    result = Some(prev);
                }
                None => result = Some(body_ty),
            }
        }
        result.ok_or_else(|| self.err("match must have at least one arm"))
    }

    /// Relate an arm pattern's type to the scrutinee type. A concrete
    /// non-sum pattern against an unknown scrutinee defers via `Member`, so
    /// several typed arms can jointly describe a sum (`(n: int)` and
    /// `(s: str)` arms infer the scrutinee as their sum at the call site).
    fn check_pattern_against(&mut self, pattern_ty: &Type, scrutinee_ty: &Type) -> TypeResult<()> {
        let pat = self.subst.prune(pattern_ty);
        let scrut = self.subst.prune(scrutinee_ty);
        let concrete_non_sum = !matches!(pat, Type::Var(_) | Type::Sum(_));
        if concrete_non_sum && matches!(scrut, Type::Var(_)) {
            self.pending.push(Constraint {
                class: Class::Member,
                args: vec![scrut.clone(), pat],
            });
            return Ok(());
        }
        self.subst.unify(pattern_ty, scrutinee_ty).map_err(|e| self.err(e))
    }

    // -- patterns -----------------------------------------------------------

    fn pattern_type(&mut self, pattern: &Pattern) -> TypeResult<PatternBinds> {
        let mut binds = self.pattern_type_inner(pattern)?;
        if let Some(ann) = &pattern.annotation {
            let ann_ty = self.resolve_ty(ann)?;
            self.subst.unify(&binds.ty, &ann_ty).map_err(|e| self.err(e))?;
            binds.ty = ann_ty;
        }
        Ok(binds)
    }

    fn pattern_type_inner(&mut self, pattern: &Pattern) -> TypeResult<PatternBinds> {
        match &pattern.kind {
            PatKind::Var(name) => {
                // A bare uppercase identifier is a constructor pattern.
                if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                    if let Some(ctor) = self.ctors.get(name).cloned() {
                        if ctor.payload.is_none() {
                            let (_, sum) = self.ctor_instance(name)?;
                            return Ok(PatternBinds { ty: sum, bindings: Vec::new() });
                        }
                        return Err(self.err(format!(
                            "constructor '{name}' expects a payload pattern"
                        )));
                    }
                    return Err(self.err(format!("unknown constructor '{name}'")));
                }
                let t = self.var_ty();
                Ok(PatternBinds { ty: t.clone(), bindings: vec![(name.clone(), t)] })
            }
            PatKind::Wildcard => Ok(PatternBinds { ty: self.var_ty(), bindings: Vec::new() }),
            PatKind::Lit(lit) => Ok(PatternBinds { ty: self.lit_ty(lit), bindings: Vec::new() }),
            PatKind::Tuple(items) => {
                let mut tys = Vec::with_capacity(items.len());
                let mut bindings = Vec::new();
                for item in items {
                    let b = self.pattern_type(item)?;
                    tys.push(b.ty);
                    bindings.extend(b.bindings);
                }
                Ok(PatternBinds { ty: Type::Tuple(tys), bindings })
            }
            PatKind::List(items) => {
                let elem = self.var_ty();
                let mut bindings = Vec::new();
                for item in items {
                    match &item.kind {
                        PatKind::Spread(name) => {
                            bindings.push((
                                name.clone(),
                                Type::List(Box::new(elem.clone())),
                            ));
                        }
                        _ => {
                            let b = self.pattern_type(item)?;
                            self.subst.unify(&b.ty, &elem).map_err(|e| self.err(e))?;
                            bindings.extend(b.bindings);
                        }
                    }
                }
                Ok(PatternBinds { ty: Type::List(Box::new(elem)), bindings })
            }
            PatKind::Spread(name) => {
                let elem = self.var_ty();
                let t = Type::List(Box::new(elem.clone()));
                Ok(PatternBinds { ty: t, bindings: vec![(name.clone(), Type::List(Box::new(elem)))] })
            }
            PatKind::Record { fields, rest } => {
                let mut tys = Vec::new();
                let mut bindings = Vec::new();
                for field in fields {
                    let b = self.pattern_type(&field.pattern)?;
                    tys.push((field.name.clone(), b.ty));
                    bindings.extend(b.bindings);
                }
                let row = self.fresh();
                if let Some(name) = rest {
                    bindings.push((
                        name.clone(),
                        Type::Record(RecordType { fields: Vec::new(), rest: Some(row) }),
                    ));
                }
                Ok(PatternBinds {
                    ty: Type::Record(RecordType { fields: tys, rest: Some(row) }),
                    bindings,
                })
            }
            PatKind::Constructor { name, payload } => {
                let ctor = self
                    .ctors
                    .get(name)
                    .cloned()
                    .ok_or_else(|| self.err(format!("unknown constructor '{name}'")))?;
                let (payload_ty, sum) = self.ctor_instance(name)?;
                let mut bindings = Vec::new();
                match (&ctor.payload, payload) {
                    (Some(_), Some(pat)) => {
                        let b = self.pattern_type(pat)?;
                        self.subst.unify(&b.ty, &payload_ty).map_err(|e| self.err(e))?;
                        bindings.extend(b.bindings);
                    }
                    (None, None) => {}
                    (Some(_), None) => {
                        return Err(self.err(format!(
                            "constructor '{name}' expects a payload pattern"
                        )));
                    }
                    (None, Some(_)) => {
                        return Err(self.err(format!("constructor '{name}' takes no payload")));
                    }
                }
                Ok(PatternBinds { ty: sum, bindings })
            }
        }
    }

    // -- types --------------------------------------------------------------

    /// Resolve a syntactic type into a checker type with a fresh type-variable
    /// scope (lowercase unknown identifiers become type variables).
    fn resolve_ty(&mut self, ty: &Ty) -> TypeResult<Type> {
        self.resolve_ty_scoped(ty, &HashMap::new())
    }

    fn resolve_ty_scoped(
        &mut self,
        ty: &Ty,
        scope: &HashMap<String, Type>,
    ) -> TypeResult<Type> {
        match ty {
            Ty::Named { name, args } => {
                if let Some(t) = scope.get(name) {
                    if args.is_empty() {
                        return Ok(t.clone());
                    }
                    return Err(self.err(format!("type variable '{name}' cannot take arguments")));
                }
                match name.as_str() {
                    "int" | "Int" => return Ok(self.con(Con::Int)),
                    "float" | "Float" => return Ok(self.con(Con::Float)),
                    "bool" | "Bool" => return Ok(self.con(Con::Bool)),
                    "str" | "Str" | "string" | "String" => return Ok(self.con(Con::Str)),
                    "usize" | "isize" => return Ok(self.con(Con::Int)),
                    "unit" | "Unit" => return Ok(self.con(Con::Unit)),
                    _ => {}
                }
                if let Some(info) = self.types.get(name).cloned() {
                    if args.len() != info.params.len() {
                        return Err(self.err(format!(
                            "type '{}' expects {} argument(s), got {}",
                            name,
                            info.params.len(),
                            args.len()
                        )));
                    }
                    let arg_types = args
                        .iter()
                        .map(|a| self.resolve_ty_scoped(a, scope))
                        .collect::<TypeResult<Vec<_>>>()?;
                    if matches!(info.ty, Ty::Sum(_)) {
                        return self.sum_type_from_decl(&info, &arg_types);
                    }
                    // Synonym: expand in place with the supplied arguments
                    // bound to the synonym's parameters, so that two uses of
                    // the same parameterized synonym share constraints.
                    let mapping: HashMap<String, Type> = info
                        .params
                        .iter()
                        .cloned()
                        .zip(arg_types.iter().cloned())
                        .collect();
                    return self.resolve_ty_scoped(&info.ty, &mapping);
                }
                if name.chars().next().map(|c| c.is_ascii_lowercase()).unwrap_or(false) {
                    return Ok(self.var_ty());
                }
                Err(self.err(format!("unknown type '{name}'")))
            }
            Ty::Tuple(tys) => {
                if tys.is_empty() {
                    return Ok(self.con(Con::Unit)); // `()` is unit
                }
                let mut out = Vec::with_capacity(tys.len());
                for t in tys {
                    out.push(self.resolve_ty_scoped(t, scope)?);
                }
                Ok(Type::Tuple(out))
            }
            Ty::List(inner) => Ok(Type::List(Box::new(self.resolve_ty_scoped(inner, scope)?))),
            Ty::Arrow { from, to } => Ok(Type::Arrow(
                Box::new(self.resolve_ty_scoped(from, scope)?),
                Box::new(self.resolve_ty_scoped(to, scope)?),
            )),
            Ty::Ref(inner) => Ok(Type::Ref(Box::new(self.resolve_ty_scoped(inner, scope)?))),
            Ty::Mut(inner) => Ok(Type::Mut(Box::new(self.resolve_ty_scoped(inner, scope)?))),
            Ty::NamedBinder { ty, .. } => self.resolve_ty_scoped(ty, scope),
            Ty::Sum(alts) => {
                // An inline (anonymous) sum type: generative per occurrence.
                let id = self.fresh_decl();
                let mut out = Vec::with_capacity(alts.len());
                for alt in alts {
                    out.push(match alt {
                        SumAlt::Ctor { name, payload } => TypeAlt::Ctor {
                            name: name.clone(),
                            payload: match payload {
                                Some(p) => self.resolve_ty_scoped(p, scope)?,
                                None => self.con(Con::Unit),
                            },
                        },
                        SumAlt::Bare(t) => TypeAlt::Bare(self.resolve_ty_scoped(t, scope)?),
                    });
                }
                Ok(Type::Sum(SumType {
                    id,
                    name: format!("@anon{id}"),
                    args: Vec::new(),
                    alts: out,
                }))
            }
            Ty::RecordType(fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for (name, t) in fields {
                    out.push((name.clone(), self.resolve_ty_scoped(t, scope)?));
                }
                Ok(Type::Record(RecordType { fields: out, rest: None }))
            }
        }
    }

    // -- instantiation, generalization, constraints --------------------------

    /// Instantiate a scheme: fresh variables for quantified ones, constraints
    /// re-attached with the fresh substitutions.
    fn instantiate(&mut self, scheme: &Scheme) -> Scheme {
        let mapping: HashMap<VarId, Type> =
            scheme.vars.iter().map(|v| (*v, self.var_ty())).collect();
        let ty = self.substitute(&scheme.ty, &mapping);
        let constraints = scheme
            .constraints
            .iter()
            .map(|c| Constraint {
                class: c.class,
                args: c.args.iter().map(|a| self.substitute(a, &mapping)).collect(),
            })
            .collect();
        Scheme { vars: Vec::new(), constraints, ty }
    }

    fn substitute(&self, t: &Type, mapping: &HashMap<VarId, Type>) -> Type {
        match self.subst.prune(t) {
            Type::Var(v) => mapping.get(&v).cloned().unwrap_or(Type::Var(v)),
            Type::Con(c) => Type::Con(c),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.substitute(&a, mapping)),
                Box::new(self.substitute(&b, mapping)),
            ),
            Type::Tuple(items) => {
                Type::Tuple(items.iter().map(|t| self.substitute(t, mapping)).collect())
            }
            Type::List(inner) => Type::List(Box::new(self.substitute(&inner, mapping))),
            Type::Ref(inner) => Type::Ref(Box::new(self.substitute(&inner, mapping))),
            Type::Mut(inner) => Type::Mut(Box::new(self.substitute(&inner, mapping))),
            Type::Sum(mut sum) => {
                sum.args = sum.args.iter().map(|a| self.substitute(a, mapping)).collect();
                sum.alts = sum
                    .alts
                    .into_iter()
                    .map(|alt| match alt {
                        TypeAlt::Ctor { name, payload } => TypeAlt::Ctor {
                            name,
                            payload: self.substitute(&payload, mapping),
                        },
                        TypeAlt::Bare(t) => TypeAlt::Bare(self.substitute(&t, mapping)),
                    })
                    .collect();
                Type::Sum(sum)
            }
            Type::Record(mut rec) => {
                rec.fields = rec
                    .fields
                    .into_iter()
                    .map(|(n, t)| (n, self.substitute(&t, mapping)))
                    .collect();
                if let Some(r) = rec.rest {
                    if let Some(Type::Var(replacement)) = mapping.get(&r) {
                        rec.rest = Some(*replacement);
                    }
                }
                Type::Record(rec)
            }
        }
    }

    /// Generalize the free variables of `ty` that are not free in the term
    /// environment. Constraints attached to those variables travel with the
    /// scheme; the rest are returned to remain pending.
    fn generalize(&self, ty: Type, exclude: Option<&str>) -> (Scheme, Vec<Constraint>) {
        // Generalize over the pruned type so redirect variables (recursive
        // bindings) do not obscure the real free variables.
        let ty = self.subst.prune(&ty);
        let mut free = HashSet::new();
        self.subst.free_vars(&ty, &mut free);
        for (env_name, entry) in &self.vars {
            if exclude.map(|n| n == env_name).unwrap_or(false) {
                continue;
            }
            let mut env_free = HashSet::new();
            self.subst.free_vars(&entry.scheme.ty, &mut env_free);
            for c in &entry.scheme.constraints {
                for a in &c.args {
                    self.subst.free_vars(a, &mut env_free);
                }
            }
            free.retain(|v| !env_free.contains(v));
        }
        let vars: Vec<VarId> = free.into_iter().collect();
        let mut kept = Vec::new();
        let mut deferred = Vec::new();
        for c in &self.pending {
            let mut cfree = HashSet::new();
            for a in &c.args {
                self.subst.free_vars(a, &mut cfree);
            }
            if cfree.is_empty() {
                continue;
            }
            if cfree.iter().any(|v| vars.contains(v)) {
                kept.push(c.clone());
            } else {
                deferred.push(c.clone());
            }
        }
        (Scheme { vars, constraints: kept, ty }, deferred)
    }

    /// Attempt to solve all pending constraints; solved ones are dropped,
    /// deferred ones stay, failures become type errors.
    fn solve_pending(&mut self) -> TypeResult<()> {
        let mut remaining = Vec::new();
        let cons = std::mem::take(&mut self.pending);
        for con in cons {
            match crate::ty::solve_constraint(&mut self.subst, &con) {
                SolveResult::Solved => {}
                SolveResult::Deferred => remaining.push(con),
                SolveResult::Failed(e) => return Err(self.err(e)),
            }
        }
        self.pending = remaining;
        Ok(())
    }
}

struct PatternBinds {
    ty: Type,
    bindings: Vec<(String, Type)>,
}

fn sum_alts(ty: &Ty) -> &[SumAlt] {
    match ty {
        Ty::Sum(alts) => alts,
        _ => &[],
    }
}

/// If a match scrutinee is literally a constructor application, return its
/// tag: `None` for a nullary constructor variable, `Some` for
/// `Some expr`.
fn scrutinee_ctor_tag(
    expr: &Expr,
    ctors: &HashMap<String, CtorDecl>,
) -> Option<String> {
    match expr {
        Expr::Var(var) => ctors
            .get(&var.name)
            .filter(|c| c.payload.is_none())
            .map(|_| var.name.clone()),
        Expr::Call(call) => match call.callee.as_ref() {
            Expr::Var(var) => ctors
                .get(&var.name)
                .filter(|c| c.payload.is_some())
                .map(|_| var.name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn list_heads(list: &crate::ast::ListExpr) -> Vec<&Expr> {
    let mut out = Vec::new();
    let mut cur = list;
    while let crate::ast::ListExpr::Cells(cons) = cur {
        out.push(cons.head.as_ref());
        cur = cons.tail.as_ref();
    }
    out
}

/// The ML value restriction: generalize only syntactic values.
fn is_value(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(_) | Expr::Var(_) | Expr::Lambda(_) => true,
        Expr::Tuple(tuple) => tuple.items.iter().all(is_value),
        Expr::List(list) => list_heads(list).iter().all(|e| is_value(e)),
        Expr::Record(record) => record.entries.iter().all(|entry| match entry {
            crate::ast::RecordValueEntry::Field(_, value) => is_value(value),
            crate::ast::RecordValueEntry::Spread(source) => is_value(source),
        }),
        _ => false,
    }
}

fn builtin_class(name: &str) -> Option<Class> {
    match name {
        "Num" => Some(Class::Num),
        "Ord" => Some(Class::Ord),
        "Eq" => Some(Class::Eq),
        "Add" => Some(Class::Add),
        "Concat" => Some(Class::Concat),
        "Seq" => Some(Class::Seq),
        "Len" => Some(Class::Len),
        "Haystack" => Some(Class::Haystack),
        "Member" => Some(Class::Member),
        _ => None,
    }
}

fn ty_var_name(ty: &Ty) -> String {
    match ty {
        Ty::Named { name, .. } => name.clone(),
        _ => String::new(),
    }
}
