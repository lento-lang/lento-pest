//! Canonical semantic analysis pipeline.
//!
//! This is the integration seam between the lossless WIP AST and master's
//! phase-oriented compiler architecture. WIP remains the behavioral authority
//! for diagnostics and feature semantics; master's semantic IR owns ordering
//! and data flow.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{Decl, Expr, PatKind, Program, Stmt, SumAlt, Ty};
use crate::infer::{base_env, check_pattern, infer_expr, InferCtx};
use crate::patterns::{analyze_specialization, DiagnosticKind, Severity};
use crate::semantics::{collect_function_groups, FunctionGroup};
use crate::specialize::{partition, OverloadSet};
use crate::specs::associate_specs;
use crate::types::{generalize, lower_ty, MonoType, TypeEnv, TypeScheme};

/// Resolved declaration metadata shared by analysis, lowering, and runtime.
/// This is the canonical identity for user-defined types; the evaluator may
/// retain source AST details, but later phases must not rediscover constructors
/// by reparsing declarations.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeMetadata {
    pub name: String,
    pub parameters: Vec<String>,
    pub constructors: Vec<ConstructorMetadata>,
    pub fields: Vec<(String, MonoType)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorMetadata {
    pub name: String,
    pub payload: Option<MonoType>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct DeclarationMetadata {
    pub types: Vec<TypeMetadata>,
    pub classes: Vec<ClassMetadata>,
    pub instances: Vec<InstanceMetadata>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassMetadata {
    pub name: String,
    pub parameters: Vec<String>,
    pub methods: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstanceMetadata {
    pub class: String,
    pub target: Vec<MonoType>,
    pub methods: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RefinementMetadata {
    pub function: String,
    pub arity: usize,
    pub has_precondition: bool,
}


/// The result of canonical analysis. Later lowering phases consume the
/// overload sets; declarations not yet represented in the semantic IR remain
/// in the source program until their dedicated lowering is complete.
#[derive(Debug)]
pub struct Analysis {
    pub overloads: Vec<OverloadSet>,
    pub declarations: DeclarationMetadata,
    pub refinements: Vec<RefinementMetadata>,
}

/// Analyze a program using the unified master/WIP pipeline.
///
/// WIP-preferred policy:
/// - non-exhaustive and duplicate pattern clauses are errors;
/// - constructor patterns and nominal type declarations are retained;
/// - class/instance declarations are preserved for the dedicated class
///   lowering phase instead of being silently desugared away.
pub fn analyze_program(program: &Program) -> Result<Analysis, String> {
    let collected = collect_function_groups(program)
        .map_err(|error| format!("declaration collection failed: {error}"))?;
    validate_advanced_declarations(program)?;

    let mut ctx = InferCtx::new();
    let mut env = base_env(&mut ctx.supply);

    let declarations = resolve_declarations(program, &mut ctx);
    install_type_declarations(&mut env, &mut ctx, program);
    validate_spec_refinements(program, &mut ctx, &env)?;
    let refinements = collect_refinement_metadata(&collected.function_groups);
    validate_refinement_calls(program, &collected.function_groups)?;

    // Seed every function before inferring any body. This preserves WIP's
    // recursive and mutually recursive definitions while the master pipeline
    // computes their principal schemes.
    for group in &collected.function_groups {
        env.entry(group.name.clone())
            .or_insert_with(|| TypeScheme::mono(seed_function_type(&mut ctx, group)));
    }

    let mut overloads = Vec::new();
    for group in &collected.function_groups {
        let set = partition(&mut ctx, group, &env)
            .map_err(|error| format!("type inference failed for '{}': {error}", group.name))?;

        for specialization in &set.specializations {
            for diagnostic in analyze_specialization(specialization) {
                match diagnostic.kind {
                    DiagnosticKind::DuplicateClause { .. } => {
                        return Err(format!("pattern error in '{}': {diagnostic}", group.name));
                    }
                    // Master originally classified this as a warning. WIP's
                    // checker rejects it, and that behavior is retained.
                    DiagnosticKind::NonExhaustive { .. } => {
                        return Err(format!("pattern error in '{}': {diagnostic}", group.name));
                    }
                    DiagnosticKind::UnreachableClause { .. } => {
                        // Preserve master’s warning severity for unreachable
                        // clauses; warnings do not change program validity.
                        debug_assert_eq!(diagnostic.severity, Severity::Warning);
                    }
                }
            }
        }

        for clause in &group.raw_clauses {
            validate_nested_matches(&clause.body, &group.name)?;
        }

        associate_specs(&mut ctx.supply, group, &set)
            .map_err(|error| format!("specification failed for '{}': {error}", group.name))?;

        // The inferred specialization is now the canonical environment entry
        // for subsequent groups. Calls already being inferred can still use
        // the seed above, which is what permits recursion.
        if let Some(first) = set.specializations.first() {
            env.insert(group.name.clone(), first.scheme.clone());
        }
        overloads.push(set);
    }

    // Check ordinary top-level expressions and lets against the same
    // environment. Type/class/instance declarations are intentionally kept in
    // the AST for their dedicated semantic lowering; they are not ignored by
    // evaluation.
    for statement in &collected.statements {
        match statement {
            Stmt::Decl(Decl::Let(binding)) => {
                let value_ty = infer_expr(&mut ctx, &binding.value, &mut env)
                    .map_err(|error| format!("top-level let inference failed: {error}"))?;
                check_pattern(&mut ctx, &binding.pattern, &value_ty, &mut env)
                    .map_err(|error| format!("top-level binding failed: {error}"))?;
                if let PatKind::Var(name) = &binding.pattern.kind {
                    let resolved = ctx.resolve(&value_ty);
                    let scheme = generalize(&env, &resolved, ctx.constraints.clone());
                    env.insert(name.clone(), scheme);
                }
            }
            Stmt::Expr(expression) => {
                validate_nested_matches(expression, "top-level")?;
                infer_expr(&mut ctx, expression, &mut env)
                    .map_err(|error| format!("top-level expression inference failed: {error}"))?;
            }
            Stmt::Decl(Decl::Type(_))
            | Stmt::Decl(Decl::Class(_))
            | Stmt::Decl(Decl::Impl(_))
            | Stmt::Decl(Decl::Spec(_))
            | Stmt::Decl(Decl::Fn(_)) => {}
        }
    }

    Ok(Analysis {
        overloads,
        declarations,
        refinements,
    })
}

fn validate_spec_refinements(
    program: &Program,
    ctx: &mut InferCtx,
    ambient: &TypeEnv,
) -> Result<(), String> {
    for statement in &program.statements {
        let Stmt::Decl(Decl::Spec(spec)) = statement else {
            continue;
        };
        let mut env = ambient.clone();
        let mut binders = BTreeMap::new();
        collect_named_binders(&spec.ty.ty, &mut binders);
        for (name, ty) in binders {
            env.insert(name, TypeScheme::mono(lower_ty(&ty, &BTreeMap::new())));
        }

        let Some(clauses) = &spec.ty.where_ else {
            continue;
        };
        for clause in clauses {
            let clause_ty = infer_expr(ctx, clause, &mut env).map_err(|error| {
                format!(
                    "where refinement for spec '{}' failed to type-check: {error}",
                    spec.name
                )
            })?;
            crate::types::unify(
                &mut ctx.subst,
                &clause_ty,
                &crate::infer::ctor::bool(),
            )
                .map_err(|error| {
                    format!(
                        "where refinement for spec '{}' must be boolean: {error}",
                        spec.name
                    )
                })?;
        }
    }
    Ok(())
}

fn collect_named_binders(ty: &Ty, binders: &mut BTreeMap<String, Ty>) {
    match ty {
        Ty::NamedBinder { name, ty } => {
            binders.insert(name.clone(), (**ty).clone());
            collect_named_binders(ty, binders);
        }
        Ty::Arrow { from, to } => {
            collect_named_binders(from, binders);
            collect_named_binders(to, binders);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_named_binders(item, binders);
            }
        }
        Ty::List(inner) | Ty::Ref(inner) | Ty::Mut(inner) => {
            collect_named_binders(inner, binders)
        }
        Ty::Named { args, .. } => {
            for arg in args {
                collect_named_binders(arg, binders);
            }
        }
        Ty::Sum(alts) => {
            for alt in alts {
                match alt {
                    SumAlt::Ctor { payload, .. } => {
                        if let Some(payload) = payload {
                            collect_named_binders(payload, binders);
                        }
                    }
                    SumAlt::Bare(ty) => collect_named_binders(ty, binders),
                }
            }
        }
        Ty::RecordType(fields) => {
            for (_, ty) in fields {
                collect_named_binders(ty, binders);
            }
        }
    }
}


fn collect_refinement_metadata(groups: &[FunctionGroup]) -> Vec<RefinementMetadata> {
    let mut metadata = Vec::new();
    for group in groups {
        for parsed in &group.explicit_specs {
            let Some(clauses) = &parsed.decl.ty.where_ else {
                continue;
            };
            let mut binders = Vec::new();
            collect_signature_binders(&parsed.decl.ty.ty, &mut binders);
            let result_name = binders.last().and_then(|(name, _)| name.clone());
            let arity = binders.len().saturating_sub(1);
            let has_precondition = clauses.iter().any(|clause| {
                let mut names = BTreeSet::new();
                collect_expr_names(clause, &mut names);
                result_name
                    .as_ref()
                    .map(|result| !names.contains(result))
                    .unwrap_or(true)
            });
            metadata.push(RefinementMetadata {
                function: group.name.clone(),
                arity,
                has_precondition,
            });
        }
    }
    metadata
}


fn validate_refinement_calls(
    program: &Program,
    groups: &[FunctionGroup],
) -> Result<(), String> {
    let mut obligations = BTreeMap::<String, usize>::new();
    for group in groups {
        for parsed in &group.explicit_specs {
            let Some(clauses) = &parsed.decl.ty.where_ else {
                continue;
            };
            let mut binders = Vec::new();
            collect_signature_binders(&parsed.decl.ty.ty, &mut binders);
            let result_name = binders.last().and_then(|(name, _)| name.clone());
            let arity = binders.len().saturating_sub(1);
            let has_precondition = clauses.iter().any(|clause| {
                let mut names = BTreeSet::new();
                collect_expr_names(clause, &mut names);
                result_name
                    .as_ref()
                    .map(|result| !names.contains(result))
                    .unwrap_or(true)
            });
            if has_precondition {
                obligations.insert(group.name.clone(), arity);
            }
        }
    }

    for group in groups {
        for clause in &group.raw_clauses {
            validate_refinement_calls_in_expr(&clause.body, &obligations)?;
        }
    }
    for statement in &program.statements {
        match statement {
            Stmt::Expr(expression) => {
                validate_refinement_calls_in_expr(expression, &obligations)?;
            }
            Stmt::Decl(Decl::Let(binding)) => {
                validate_refinement_calls_in_expr(&binding.value, &obligations)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_refinement_calls_in_expr(
    expression: &Expr,
    obligations: &BTreeMap<String, usize>,
) -> Result<(), String> {
    fn walk(
        expression: &Expr,
        obligations: &BTreeMap<String, usize>,
        nested_callee: bool,
    ) -> Result<(), String> {
        match expression {
            Expr::Call(call) => {
                if !nested_callee {
                    let (base, args) = flatten_call(call);
                    if let Expr::Var(variable) = base {
                        if let Some(arity) = obligations.get(&variable.name) {
                            if args.len() < *arity {
                                return Err(format!(
                                    "partial application of '{}' escapes its where-preconditions; call it with all {} argument(s) at once",
                                    variable.name, arity
                                ));
                            }
                        }
                    }
                }
                walk(&call.callee, obligations, true)?;
                for argument in &call.args {
                    walk(argument, obligations, false)?;
                }
            }
            Expr::Lambda(lambda) => walk(&lambda.body, obligations, false)?,
            Expr::Member(member) => walk(&member.obj, obligations, false)?,
            Expr::Index(index) => {
                walk(&index.obj, obligations, false)?;
                walk(&index.index, obligations, false)?;
            }
            Expr::Unary(unary) => walk(&unary.operand, obligations, false)?,
            Expr::Binary(binary) => {
                walk(&binary.lhs, obligations, false)?;
                walk(&binary.rhs, obligations, false)?;
            }
            Expr::Tuple(tuple) => {
                for item in &tuple.items {
                    walk(item, obligations, false)?;
                }
            }
            Expr::List(list) => {
                let mut current = list;
                loop {
                    match current {
                        crate::ast::ListExpr::Empty => break,
                        crate::ast::ListExpr::Cells(cell) => {
                            walk(&cell.head, obligations, false)?;
                            current = &cell.tail;
                        }
                    }
                }
            }
            Expr::Record(record) => {
                for entry in &record.entries {
                    let value = match entry {
                        crate::ast::RecordValueEntry::Field(_, value)
                        | crate::ast::RecordValueEntry::Spread(value) => value,
                    };
                    walk(value, obligations, false)?;
                }
            }
            Expr::Block(block) => {
                for statement in &block.body {
                    match statement {
                        Stmt::Expr(expression) => walk(expression, obligations, false)?,
                        Stmt::Decl(Decl::Let(binding)) => {
                            walk(&binding.value, obligations, false)?
                        }
                        _ => {}
                    }
                }
            }
            Expr::Ref(reference) => walk(&reference.inner, obligations, false)?,
            Expr::Assign(assign) => {
                walk(&assign.place, obligations, false)?;
                walk(&assign.value, obligations, false)?;
            }
            Expr::Match(matched) => {
                walk(&matched.scrutinee, obligations, false)?;
                for arm in &matched.arms {
                    if let Some(guard) = &arm.guard {
                        walk(guard, obligations, false)?;
                    }
                    walk(&arm.body, obligations, false)?;
                }
            }
            Expr::Var(variable) => {
                if !nested_callee && obligations.contains_key(&variable.name) {
                    let arity = obligations[&variable.name];
                    return Err(format!(
                        "partial application of '{}' escapes its where-preconditions; call it with all {} argument(s) at once",
                        variable.name, arity
                    ));
                }
            }
            Expr::Lit(_) => {}
        }
        Ok(())
    }

    walk(expression, obligations, false)
}

fn flatten_call<'a>(call: &'a crate::ast::CallExpr) -> (&'a Expr, Vec<&'a Expr>) {
    let mut args = call.args.iter().collect::<Vec<_>>();
    let mut base = call.callee.as_ref();
    while let Expr::Call(inner) = base {
        args.splice(0..0, inner.args.iter().collect::<Vec<_>>());
        base = inner.callee.as_ref();
    }
    (base, args)
}

fn collect_signature_binders(ty: &Ty, binders: &mut Vec<(Option<String>, Ty)>) {
    match ty {
        Ty::Arrow { from, to } => {
            binders.push(signature_binder(from));
            collect_signature_binders(to, binders);
        }
        other => binders.push(signature_binder(other)),
    }
}

fn signature_binder(ty: &Ty) -> (Option<String>, Ty) {
    match ty {
        Ty::NamedBinder { name, ty } => (Some(name.clone()), (**ty).clone()),
        other => (None, other.clone()),
    }
}

fn collect_expr_names(expression: &Expr, names: &mut BTreeSet<String>) {
    match expression {
        Expr::Var(variable) => {
            names.insert(variable.name.clone());
        }
        Expr::Call(call) => {
            collect_expr_names(&call.callee, names);
            for argument in &call.args {
                collect_expr_names(argument, names);
            }
        }
        Expr::Lambda(lambda) => collect_expr_names(&lambda.body, names),
        Expr::Member(member) => collect_expr_names(&member.obj, names),
        Expr::Index(index) => {
            collect_expr_names(&index.obj, names);
            collect_expr_names(&index.index, names);
        }
        Expr::Unary(unary) => collect_expr_names(&unary.operand, names),
        Expr::Binary(binary) => {
            collect_expr_names(&binary.lhs, names);
            collect_expr_names(&binary.rhs, names);
        }
        Expr::Tuple(tuple) => {
            for item in &tuple.items {
                collect_expr_names(item, names);
            }
        }
        Expr::List(list) => {
            let mut current = list;
            loop {
                match current {
                    crate::ast::ListExpr::Empty => break,
                    crate::ast::ListExpr::Cells(cell) => {
                        collect_expr_names(&cell.head, names);
                        current = &cell.tail;
                    }
                }
            }
        }
        Expr::Record(record) => {
            for entry in &record.entries {
                let value = match entry {
                    crate::ast::RecordValueEntry::Field(_, value)
                    | crate::ast::RecordValueEntry::Spread(value) => value,
                };
                collect_expr_names(value, names);
            }
        }
        Expr::Block(block) => {
            for statement in &block.body {
                match statement {
                    Stmt::Expr(expression) => collect_expr_names(expression, names),
                    Stmt::Decl(Decl::Let(binding)) => {
                        collect_expr_names(&binding.value, names)
                    }
                    _ => {}
                }
            }
        }
        Expr::Ref(reference) => collect_expr_names(&reference.inner, names),
        Expr::Assign(assign) => {
            collect_expr_names(&assign.place, names);
            collect_expr_names(&assign.value, names);
        }
        Expr::Match(matched) => {
            collect_expr_names(&matched.scrutinee, names);
            for arm in &matched.arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_names(guard, names);
                }
                collect_expr_names(&arm.body, names);
            }
        }
        Expr::Lit(_) => {}
    }
}


fn seed_function_type(ctx: &mut InferCtx, group: &FunctionGroup) -> MonoType {
    let arity = group
        .raw_clauses
        .first()
        .map(|clause| clause.params.len())
        .unwrap_or(0);
    let mut ty = ctx.supply.fresh();
    for _ in (0..arity).rev() {
        ty = MonoType::Function(Box::new(ctx.supply.fresh()), Box::new(ty));
    }
    ty
}


fn resolve_declarations(program: &Program, ctx: &mut InferCtx) -> DeclarationMetadata {
    let mut declarations = DeclarationMetadata::default();
    for statement in &program.statements {
        let Stmt::Decl(Decl::Type(declaration)) = statement else {
            continue;
        };
        let mut binders = BTreeMap::new();
        for parameter in &declaration.params {
            binders.insert(parameter.clone(), ctx.supply.fresh());
        }
        let mut metadata = TypeMetadata {
            name: declaration.name.clone(),
            parameters: declaration.params.clone(),
            constructors: Vec::new(),
            fields: Vec::new(),
        };
        match &declaration.ty {
            Ty::Sum(alternatives) => {
                for alternative in alternatives {
                    match alternative {
                        SumAlt::Ctor { name, payload } => metadata.constructors.push(
                            ConstructorMetadata {
                                name: name.clone(),
                                payload: payload
                                    .as_ref()
                                    .map(|payload| lower_ty(payload, &binders)),
                            },
                        ),
                        SumAlt::Bare(ty) => metadata.fields.push((
                            format!("member{}", metadata.fields.len()),
                            lower_ty(ty, &binders),
                        )),
                    }
                }
            }
            Ty::RecordType(fields) => {
                metadata.fields = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), lower_ty(ty, &binders)))
                    .collect();
            }
            ty => metadata.fields.push((
                "value".to_string(),
                lower_ty(ty, &binders),
            )),
        }
        declarations.types.push(metadata);
    }

    for statement in &program.statements {
        match statement {
            Stmt::Decl(Decl::Class(class)) => {
                declarations.classes.push(ClassMetadata {
                    name: class.name.clone(),
                    parameters: class.params.clone(),
                    methods: class.specs.iter().map(|spec| spec.name.clone()).collect(),
                });
            }
            Stmt::Decl(Decl::Impl(implementation)) => {
                declarations.instances.push(InstanceMetadata {
                    class: implementation.class.clone(),
                    target: implementation
                        .target
                        .iter()
                        .map(|ty| lower_ty(ty, &BTreeMap::new()))
                        .collect(),
                    methods: implementation
                        .methods
                        .iter()
                        .map(|method| method.name.clone())
                        .collect(),
                });
            }
            _ => {}
        }
    }
    declarations
}


fn install_type_declarations(env: &mut TypeEnv, ctx: &mut InferCtx, program: &Program) {
    for statement in &program.statements {
        let Stmt::Decl(Decl::Type(declaration)) = statement else {
            continue;
        };
        let Ty::Sum(alternatives) = &declaration.ty else {
            continue;
        };

        let mut binders = std::collections::BTreeMap::new();
        let mut quantified = Vec::new();
        for parameter in &declaration.params {
            let id = ctx.supply.fresh_id();
            quantified.push(id);
            binders.insert(parameter.clone(), MonoType::Var(id));
        }
        let result = MonoType::Constructor(
            declaration.name.clone(),
            declaration
                .params
                .iter()
                .map(|parameter| binders[parameter].clone())
                .collect(),
        );

        for alternative in alternatives {
            let SumAlt::Ctor { name, payload } = alternative else {
                continue;
            };
            let body = match payload {
                Some(payload) => MonoType::Function(
                    Box::new(lower_ty(payload, &binders)),
                    Box::new(result.clone()),
                ),
                None => result.clone(),
            };
            env.insert(
                name.clone(),
                TypeScheme {
                    quantified: quantified.clone(),
                    constraints: Vec::new(),
                    body,
                },
            );
        }
    }
}


fn validate_nested_matches(expression: &Expr, owner: &str) -> Result<(), String> {
    match expression {
        Expr::Match(m) => {
            let specialization = crate::specialize::Specialization {
                id: 0,
                scheme: TypeScheme::mono(MonoType::Var(0)),
                declared_domain: Vec::new(),
                clauses: m
                    .arms
                    .iter()
                    .enumerate()
                    .map(|(index, arm)| crate::specialize::SpecializedClause {
                        ty: MonoType::Var(0),
                        patterns: vec![arm.pattern.clone()],
                        source_index: index,
                        declared_domain: Vec::new(),
                    })
                    .collect(),
            };
            for diagnostic in analyze_specialization(&specialization) {
                match diagnostic.kind {
                    DiagnosticKind::DuplicateClause { .. }
                    | DiagnosticKind::NonExhaustive { .. } => {
                        return Err(format!("pattern error in '{owner}': {diagnostic}"));
                    }
                    DiagnosticKind::UnreachableClause { .. } => {}
                }
            }
            validate_nested_matches(&m.scrutinee, owner)?;
            for arm in &m.arms {
                if let Some(guard) = &arm.guard {
                    validate_nested_matches(guard, owner)?;
                }
                validate_nested_matches(&arm.body, owner)?;
            }
        }
        Expr::Lambda(lambda) => validate_nested_matches(&lambda.body, owner)?,
        Expr::Call(call) => {
            validate_nested_matches(&call.callee, owner)?;
            for argument in &call.args {
                validate_nested_matches(argument, owner)?;
            }
        }
        Expr::Member(member) => validate_nested_matches(&member.obj, owner)?,
        Expr::Index(index) => {
            validate_nested_matches(&index.obj, owner)?;
            validate_nested_matches(&index.index, owner)?;
        }
        Expr::Unary(unary) => validate_nested_matches(&unary.operand, owner)?,
        Expr::Binary(binary) => {
            validate_nested_matches(&binary.lhs, owner)?;
            validate_nested_matches(&binary.rhs, owner)?;
        }
        Expr::Tuple(tuple) => {
            for item in &tuple.items {
                validate_nested_matches(item, owner)?;
            }
        }
        Expr::List(list) => {
            let mut current = list;
            loop {
                match current {
                    crate::ast::ListExpr::Empty => break,
                    crate::ast::ListExpr::Cells(cell) => {
                        validate_nested_matches(&cell.head, owner)?;
                        current = &cell.tail;
                    }
                }
            }
        }
        Expr::Record(record) => {
            for entry in &record.entries {
                match entry {
                    crate::ast::RecordValueEntry::Field(_, value)
                    | crate::ast::RecordValueEntry::Spread(value) => {
                        validate_nested_matches(value, owner)?;
                    }
                }
            }
        }
        Expr::Block(block) => {
            for statement in &block.body {
                match statement {
                    Stmt::Expr(expression) => validate_nested_matches(expression, owner)?,
                    Stmt::Decl(Decl::Let(binding)) => {
                        validate_nested_matches(&binding.value, owner)?
                    }
                    _ => {}
                }
            }
        }
        Expr::Ref(reference) => validate_nested_matches(&reference.inner, owner)?,
        Expr::Assign(assign) => {
            validate_nested_matches(&assign.place, owner)?;
            validate_nested_matches(&assign.value, owner)?;
        }
        Expr::Lit(_) | Expr::Var(_) => {}
    }
    Ok(())
}


fn validate_advanced_declarations(program: &Program) -> Result<(), String> {
    let mut type_names = BTreeSet::new();
    let mut constructor_names = BTreeSet::new();
    let mut classes = BTreeMap::<String, (usize, BTreeSet<String>)>::new();
    let mut instances = BTreeSet::new();

    for statement in &program.statements {
        match statement {
            Stmt::Decl(Decl::Type(declaration)) => {
                if !type_names.insert(declaration.name.clone()) {
                    return Err(format!(
                        "duplicate type declaration '{}'",
                        declaration.name
                    ));
                }
                if let Ty::Sum(alternatives) = &declaration.ty {
                    for alternative in alternatives {
                        if let SumAlt::Ctor { name, .. } = alternative {
                            if !constructor_names.insert(name.clone()) {
                                return Err(format!("duplicate constructor '{name}'"));
                            }
                        }
                    }
                }
            }
            Stmt::Decl(Decl::Class(class)) => {
                if classes.contains_key(&class.name) {
                    return Err(format!("duplicate class declaration '{}'", class.name));
                }
                let mut methods = BTreeSet::new();
                for spec in &class.specs {
                    if !methods.insert(spec.name.clone()) {
                        return Err(format!(
                            "duplicate method spec '{}' in class '{}'",
                            spec.name, class.name
                        ));
                    }
                }
                if methods.is_empty() {
                    return Err(format!("class '{}' requires at least one method", class.name));
                }
                classes.insert(class.name.clone(), (class.params.len(), methods));
            }
            Stmt::Decl(Decl::Impl(implementation)) => {
                let (parameter_count, required) = classes.get(&implementation.class).ok_or_else(|| {
                    format!("unknown class '{}'", implementation.class)
                })?;
                if implementation.target.len() != *parameter_count {
                    return Err(format!(
                        "class '{}' expects {} implementation type argument(s), got {}",
                        implementation.class,
                        parameter_count,
                        implementation.target.len()
                    ));
                }
                let key = format!(
                    "{} {}",
                    implementation.class,
                    implementation
                        .target
                        .iter()
                        .map(|target| format!("{target:?}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                if !instances.insert(key) {
                    return Err(format!(
                        "overlapping implementation of '{}'",
                        implementation.class
                    ));
                }

                let mut provided = BTreeSet::new();
                for method in &implementation.methods {
                    if !provided.insert(method.name.clone()) {
                        return Err(format!("duplicate method '{}' in impl", method.name));
                    }
                    if !required.contains(&method.name) {
                        return Err(format!(
                            "method '{}' is not required by class '{}'",
                            method.name, implementation.class
                        ));
                    }
                }
                if let Some(missing) = required.difference(&provided).next() {
                    return Err(format!(
                        "impl '{}' is missing required method '{}'",
                        implementation.class, missing
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}
