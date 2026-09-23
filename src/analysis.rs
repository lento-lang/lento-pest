//! Canonical semantic analysis pipeline.
//!
//! This is the integration seam between the lossless WIP AST and master's
//! phase-oriented compiler architecture. WIP remains the behavioral authority
//! for diagnostics and feature semantics; master's semantic IR owns ordering
//! and data flow.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{Decl, Expr, PatKind, Program, Stmt, SumAlt, Ty};
use crate::infer::{base_env, check_pattern, infer_expr, infer_typed_expr, InferCtx};
use crate::patterns::{analyze_specialization, DiagnosticKind, Severity};
use crate::semantics::{
    collect_function_groups, FunctionGroup, SpecOrigin, TypedExpr, TypedExprKind,
    TypedLet, TypedOverloadSet, TypedPatternClause, TypedProgram, TypedSpecialization,
};
use crate::specialize::{partition, OverloadSet};
use crate::specs::associate_specs;
use crate::types::{
    generalize, instantiate, lower_ty, unify, MonoType, Substitution, TypeEnv, TypeScheme,
    TypeVarSupply,
};

/// Resolved declaration metadata shared by analysis, lowering, and runtime.
/// This is the canonical identity for user-defined types; the evaluator may
/// retain source AST details, but later phases must not rediscover constructors
/// by reparsing declarations.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeMetadata {
    pub name: String,
    pub parameters: Vec<String>,
    pub source: Ty,
    pub parameter_ids: Vec<u32>,
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
    pub typed: TypedProgram,
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
    install_type_declarations(&mut env, &declarations);
    install_class_methods(&mut env, &mut ctx, program);
    validate_spec_refinements(program, &mut ctx, &env)?;
    let refinements = collect_refinement_metadata(&collected.function_groups);
    validate_refinement_calls(program, &collected.function_groups)?;
    #[cfg(feature = "canonical-smt")]
    verify_canonical_smt(program, &collected.function_groups)?;

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
    // environment, retaining their recursive type annotations.
    let mut typed_lets = Vec::new();
    let mut typed_exprs = Vec::new();
    let mut typed_expr_source_indices = Vec::new();
    for (source_index, statement) in program.statements.iter().enumerate() {
        match statement {
            Stmt::Decl(Decl::Let(binding)) => {
                let value = infer_typed_expr(&mut ctx, &binding.value, &mut env)
                    .map_err(|error| format!("top-level let inference failed: {error}"))?;
                check_pattern(&mut ctx, &binding.pattern, &value.ty, &mut env)
                    .map_err(|error| format!("top-level binding failed: {error}"))?;
                if let PatKind::Var(name) = &binding.pattern.kind {
                    let resolved = ctx.resolve(&value.ty);
                    let scheme = generalize(&env, &resolved, ctx.constraints.clone());
                    env.insert(name.clone(), scheme);
                }
                typed_lets.push(TypedLet {
                    source_index,
                    mutable: binding.mutable,
                    pattern: binding.pattern.clone(),
                    annotation: binding.annotation.clone(),
                    value,
                });
            }
            Stmt::Expr(expression) => {
                validate_nested_matches(expression, "top-level")?;
                typed_exprs.push(
                    infer_typed_expr(&mut ctx, expression, &mut env)
                        .map_err(|error| format!("top-level expression inference failed: {error}"))?,
                );
                typed_expr_source_indices.push(source_index);
            }
            Stmt::Decl(Decl::Type(_))
            | Stmt::Decl(Decl::Class(_))
            | Stmt::Decl(Decl::Impl(_))
            | Stmt::Decl(Decl::Spec(_))
            | Stmt::Decl(Decl::Fn(_)) => {}
        }
    }

    validate_class_constraints(&ctx, &declarations)?;
    for binding in &mut typed_lets {
        crate::infer::resolve_typed_expr(&ctx, &mut binding.value);
    }
    for expression in &mut typed_exprs {
        crate::infer::resolve_typed_expr(&ctx, expression);
    }
    let mut typed = build_typed_program(
        &collected.function_groups,
        &overloads,
        typed_lets,
        typed_exprs,
        typed_expr_source_indices,
    )?;
    resolve_typed_program_calls(&mut typed, &overloads, &declarations)?;

    Ok(Analysis {
        overloads,
        declarations,
        refinements,
        typed,
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


#[cfg(feature = "canonical-smt")]
#[derive(Clone)]
struct SmtRefinement {
    inputs: Vec<(Option<String>, Option<crate::smt::SVal>)>,
    preconditions: Vec<Expr>,
    postconditions: Vec<Expr>,
    arity: usize,
}

#[cfg(feature = "canonical-smt")]
fn verify_canonical_smt(
    program: &Program,
    groups: &[FunctionGroup],
) -> Result<(), String> {
    let mut refinements = BTreeMap::<String, SmtRefinement>::new();

    for group in groups {
        let refined_specs = group
            .explicit_specs
            .iter()
            .filter(|parsed| parsed.decl.ty.where_.is_some())
            .collect::<Vec<_>>();
        if refined_specs.len() > 1 {
            return Err(format!(
                "cannot verify refinements for '{}': multiple refined specifications need overload-aware proof selection",
                group.name
            ));
        }
        for parsed in &group.explicit_specs {
            let Some(clauses) = &parsed.decl.ty.where_ else {
                continue;
            };
            let mut binders = Vec::new();
            collect_signature_binders(&parsed.decl.ty.ty, &mut binders);
            if binders.is_empty() {
                return Err(format!(
                    "cannot verify refinement for '{}': empty signature",
                    group.name
                ));
            }
            let result = binders.last().cloned().unwrap();
            let inputs = &binders[..binders.len() - 1];
            let input_sorts = inputs
                .iter()
                .map(|(name, ty)| (name.clone(), crate::smt::sort_of_ty(ty)))
                .collect::<Vec<_>>();
            let result_name = result.0.clone();
            let mut preconditions = Vec::new();
            let mut postconditions = Vec::new();
            for clause in clauses {
                let mut names = BTreeSet::new();
                collect_expr_names(clause, &mut names);
                if result_name
                    .as_ref()
                    .map(|name| names.contains(name))
                    .unwrap_or(false)
                {
                    postconditions.push(clause.clone());
                } else {
                    preconditions.push(clause.clone());
                }
            }
            refinements.insert(
                group.name.clone(),
                SmtRefinement {
                    inputs: input_sorts,
                    preconditions,
                    postconditions,
                    arity: inputs.len(),
                },
            );
        }
    }

    verify_canonical_smt_calls(program, &refinements)?;

    for group in groups {
        let Some(refinement) = refinements.get(&group.name) else {
            continue;
        };
        if refinement.postconditions.is_empty() {
            continue;
        }
        let parsed = group
            .explicit_specs
            .iter()
            .find(|spec| spec.decl.ty.where_.is_some())
            .expect("refinement metadata has a source spec");
        let mut binders = Vec::new();
        collect_signature_binders(&parsed.decl.ty.ty, &mut binders);
        let (result_name, result_ty) = binders.last().cloned().unwrap();
        let Some(result_name) = result_name else {
            return Err(format!(
                "cannot verify postcondition for '{}': result binder must be named",
                group.name
            ));
        };
        let Some(result_sort) = crate::smt::sort_of_ty(&result_ty) else {
            return Err(format!(
                "cannot verify postcondition for '{}': result type is not solver-supported",
                group.name
            ));
        };
        let inputs = refinement
            .inputs
            .iter()
            .map(|(name, sort)| {
                sort.map(|sort| (name.clone(), sort)).ok_or_else(|| {
                    format!(
                        "cannot verify postcondition for '{}': input type is not solver-supported",
                        group.name
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if group.raw_clauses.len() != 1 {
            return Err(format!(
                "cannot verify postcondition for '{}': multi-clause function bodies need branch-aware proof lowering",
                group.name
            ));
        }
        let body = curry_function_clause(&group.raw_clauses[0]);
        for post in &refinement.postconditions {
            match crate::smt::check_post(
                &inputs,
                &(result_name.clone(), result_sort),
                &body,
                &refinement.preconditions,
                post,
            )
            .map_err(|error| format!("postcondition for '{}': {error}", group.name))?
            {
                crate::smt::Verdict::Proven => {}
                crate::smt::Verdict::Counterexample(witness) => {
                    return Err(format!(
                        "postcondition for '{}' is false: {witness}",
                        group.name
                    ));
                }
            }
        }
    }
    Ok(())
}

#[cfg(feature = "canonical-smt")]
fn verify_canonical_smt_calls(
    program: &Program,
    refinements: &BTreeMap<String, SmtRefinement>,
) -> Result<(), String> {
    fn walk(
        expression: &Expr,
        refinements: &BTreeMap<String, SmtRefinement>,
        nested_callee: bool,
    ) -> Result<(), String> {
        match expression {
            Expr::Call(call) => {
                if !nested_callee {
                    let (base, args) = flatten_call(call);
                    if let Expr::Var(variable) = base {
                        if let Some(refinement) = refinements.get(&variable.name) {
                            if args.len() != refinement.arity {
                                return Err(format!(
                                    "cannot verify call to '{}': expected {} arguments, got {}",
                                    variable.name, refinement.arity, args.len()
                                ));
                            }
                            for argument in &args {
                                let mut names = BTreeSet::new();
                                collect_expr_names(argument, &mut names);
                                if !names.is_empty() {
                                    return Err(format!(
                                        "cannot verify call to '{}': symbolic arguments require canonical type-to-SMT lowering",
                                        variable.name
                                    ));
                                }
                            }
                            for pre in &refinement.preconditions {
                                match crate::smt::check_pre(
                                    &refinement.inputs,
                                    pre,
                                    &args,
                                    &[],
                                )
                                .map_err(|error| {
                                    format!("precondition for '{}': {error}", variable.name)
                                })? {
                                    crate::smt::Verdict::Proven => {}
                                    crate::smt::Verdict::Counterexample(witness) => {
                                        return Err(format!(
                                            "precondition for '{}' is false: {witness}",
                                            variable.name
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                walk(&call.callee, refinements, true)?;
                for argument in &call.args {
                    walk(argument, refinements, false)?;
                }
            }
            Expr::Lambda(lambda) => walk(&lambda.body, refinements, false)?,
            Expr::Member(member) => walk(&member.obj, refinements, false)?,
            Expr::Index(index) => {
                walk(&index.obj, refinements, false)?;
                walk(&index.index, refinements, false)?;
            }
            Expr::Unary(unary) => walk(&unary.operand, refinements, false)?,
            Expr::Binary(binary) => {
                walk(&binary.lhs, refinements, false)?;
                walk(&binary.rhs, refinements, false)?;
            }
            Expr::Tuple(tuple) => {
                for item in &tuple.items {
                    walk(item, refinements, false)?;
                }
            }
            Expr::List(list) => {
                let mut current = list;
                loop {
                    match current {
                        crate::ast::ListExpr::Empty => break,
                        crate::ast::ListExpr::Cells(cell) => {
                            walk(&cell.head, refinements, false)?;
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
                    walk(value, refinements, false)?;
                }
            }
            Expr::Block(block) => {
                for statement in &block.body {
                    match statement {
                        Stmt::Expr(expression) => walk(expression, refinements, false)?,
                        Stmt::Decl(Decl::Let(binding)) => {
                            walk(&binding.value, refinements, false)?
                        }
                        _ => {}
                    }
                }
            }
            Expr::Ref(reference) => walk(&reference.inner, refinements, false)?,
            Expr::Assign(assign) => {
                walk(&assign.place, refinements, false)?;
                walk(&assign.value, refinements, false)?;
            }
            Expr::Match(matched) => {
                walk(&matched.scrutinee, refinements, false)?;
                for arm in &matched.arms {
                    if let Some(guard) = &arm.guard {
                        walk(guard, refinements, false)?;
                    }
                    walk(&arm.body, refinements, false)?;
                }
            }
            Expr::Var(_) | Expr::Lit(_) => {}
        }
        Ok(())
    }

    for statement in &program.statements {
        match statement {
            Stmt::Expr(expression) => walk(expression, refinements, false)?,
            Stmt::Decl(Decl::Let(binding)) => {
                walk(&binding.value, refinements, false)?
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(feature = "canonical-smt")]
fn curry_function_clause(clause: &crate::ast::FnDecl) -> Expr {
    let mut body = clause.body.clone();
    for parameter in clause.params.iter().rev() {
        body = Expr::Lambda(crate::ast::LambdaExpr {
            params: vec![parameter.clone()],
            body: Box::new(body),
        });
    }
    body
}




fn resolve_typed_program_calls(
    program: &mut TypedProgram,
    overloads: &[OverloadSet],
    declarations: &DeclarationMetadata,
) -> Result<(), String> {
    for set in &mut program.overloads {
        for specialization in &mut set.specializations {
            for clause in &mut specialization.clauses {
                resolve_typed_expr_calls(&mut clause.body, overloads, declarations)?;
            }
        }
    }
    for binding in &mut program.lets {
        resolve_typed_expr_calls(&mut binding.value, overloads, declarations)?;
    }
    for expression in &mut program.exprs {
        resolve_typed_expr_calls(expression, overloads, declarations)?;
    }
    Ok(())
}

fn resolve_typed_expr_calls(
    expression: &mut TypedExpr,
    overloads: &[OverloadSet],
    declarations: &DeclarationMetadata,
) -> Result<(), String> {
    match &mut expression.kind {
        TypedExprKind::Call {
            callee,
            args,
            specialization,
        } => {
            resolve_typed_expr_calls(callee, overloads, declarations)?;
            for argument in args.iter_mut() {
                resolve_typed_expr_calls(argument, overloads, declarations)?;
            }
            let TypedExprKind::Var(name) = &callee.kind else {
                return Ok(());
            };
            let Some(set) = overloads.iter().find(|set| set.name == *name) else {
                return Ok(());
            };
            let mut applied_type = expression.ty.clone();
            for argument in args.iter().rev() {
                applied_type = MonoType::Function(
                    Box::new(argument.ty.clone()),
                    Box::new(applied_type),
                );
            }
            if contains_type_variable(&applied_type) {
                return Ok(());
            }

            let mut matches = Vec::new();
            for candidate in &set.specializations {
                if callable_arity(&candidate.scheme.body) != args.len() {
                    continue;
                }
                let mut supply = TypeVarSupply::new();
                let (candidate_type, constraints) = instantiate(&mut supply, &candidate.scheme);
                let mut substitution = Substitution::new();
                if unify(&mut substitution, &candidate_type, &applied_type).is_ok()
                    && constraints.iter().all(|constraint| {
                        let args = constraint
                            .args
                            .iter()
                            .map(|argument| substitution.apply(argument))
                            .collect::<Vec<_>>();
                        !args.iter().any(contains_type_variable)
                            && declarations.instances.iter().any(|instance| {
                                instance.class == constraint.name
                                    && instance.target == args
                            })
                    })
                {
                    matches.push((candidate_specificity(candidate), candidate.id));
                }
            }
            matches.sort_by(|(left_score, left_id), (right_score, right_id)| {
                right_score
                    .cmp(left_score)
                    .then_with(|| left_id.cmp(right_id))
            });
            match matches.as_slice() {
                [] => {
                    return Err(format!(
                        "no specialization of '{name}' accepts the fully typed call"
                    ));
                }
                [(_, id)] => *specialization = Some(*id),
                [(best_score, _id), (next_score, _), ..] if best_score == next_score => {
                    return Err(format!(
                        "ambiguous overload call to '{name}' for fully typed arguments"
                    ));
                }
                [(_, id), ..] => *specialization = Some(*id),
            }
        }
        TypedExprKind::Lambda { body, .. } => resolve_typed_expr_calls(body, overloads)?,
        TypedExprKind::Match { scrutinee, arms } => {
            resolve_typed_expr_calls(scrutinee, overloads, declarations)?;
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    resolve_typed_expr_calls(guard, overloads, declarations)?;
                }
                resolve_typed_expr_calls(&mut arm.body, overloads, declarations)?;
            }
        }
        TypedExprKind::Composite { children, .. } => {
            for child in children {
                resolve_typed_expr_calls(child, overloads, declarations)?;
            }
        }
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) | TypedExprKind::Unresolved(_) => {}
    }
    Ok(())
}

fn callable_arity(ty: &MonoType) -> usize {
    match ty {
        MonoType::Function(_, result) => 1 + callable_arity(result),
        _ => 0,
    }
}

fn contains_type_variable(ty: &MonoType) -> bool {
    match ty {
        MonoType::Var(_) => true,
        MonoType::Constructor(_, args) | MonoType::Tuple(args) => {
            args.iter().any(contains_type_variable)
        }
        MonoType::Function(from, to) => {
            contains_type_variable(from) || contains_type_variable(to)
        }
        MonoType::List(inner) | MonoType::Ref(inner) | MonoType::Mut(inner) => {
            contains_type_variable(inner)
        }
    }
}

fn candidate_specificity(candidate: &crate::specialize::Specialization) -> (usize, usize) {
    candidate
        .declared_domain
        .iter()
        .flatten()
        .map(|ty| {
            fn size(ty: &MonoType) -> usize {
                match ty {
                    MonoType::Var(_) => 0,
                    MonoType::Constructor(_, args) | MonoType::Tuple(args) => {
                        1 + args.iter().map(size).sum::<usize>()
                    }
                    MonoType::Function(from, to) => 1 + size(from) + size(to),
                    MonoType::List(inner) | MonoType::Ref(inner) | MonoType::Mut(inner) => {
                        1 + size(inner)
                    }
                }
            }
            (usize::from(!contains_type_variable(ty)), size(ty))
        })
        .fold((0, 0), |(count, total), (concrete, size)| {
            (count + concrete, total + size)
        })
}

fn build_typed_program(
    groups: &[FunctionGroup],
    overloads: &[OverloadSet],
    lets: Vec<TypedLet>,
    exprs: Vec<TypedExpr>,
    expr_source_indices: Vec<usize>,
) -> Result<TypedProgram, String> {
    let mut typed_sets = Vec::new();
    for set in overloads {
        let group = groups
            .iter()
            .find(|group| group.name == set.name)
            .ok_or_else(|| format!("missing source group for '{}'", set.name))?;
        let mut typed_specializations = Vec::new();
        for specialization in &set.specializations {
            let mut typed_clauses = Vec::new();
            for clause in &specialization.clauses {
                let source_position = group
                    .source_indices
                    .iter()
                    .position(|index| *index == clause.source_index)
                    .ok_or_else(|| {
                        format!(
                            "missing source clause {} for '{}'",
                            clause.source_index, group.name
                        )
                    })?;
                let _source = &group.raw_clauses[source_position];
                typed_clauses.push(TypedPatternClause {
                    patterns: clause.patterns.clone(),
                    clause_ty: clause.ty.clone(),
                    body: clause.body.clone(),
                    source_index: clause.source_index,
                });
            }
            typed_specializations.push(TypedSpecialization {
                id: specialization.id,
                scheme: specialization.scheme.clone(),
                origin: SpecOrigin::Inferred(vec![group.source_span]),
                clauses: typed_clauses,
            });
        }
        typed_sets.push(TypedOverloadSet {
            name: set.name.clone(),
            source_index: group.source_indices.first().copied().unwrap_or(group.source_span.0),
            specializations: typed_specializations,
        });
    }
    Ok(TypedProgram {
        overloads: typed_sets,
        lets,
        exprs,
        expr_source_indices,
    })
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



fn install_class_methods(env: &mut TypeEnv, ctx: &mut InferCtx, program: &Program) {
    for statement in &program.statements {
        let Stmt::Decl(Decl::Class(class)) = statement else {
            continue;
        };
        let mut binders = BTreeMap::new();
        let mut quantified = Vec::new();
        for parameter in &class.params {
            let id = ctx.supply.fresh_id();
            quantified.push(id);
            binders.insert(parameter.clone(), MonoType::Var(id));
        }
        for spec in &class.specs {
            let mut method_binders = binders.clone();
            let mut method_quantified = quantified.clone();
            for quantifier in &spec.ty.quantifiers {
                for name in &quantifier.vars {
                    if !method_binders.contains_key(name) {
                        let id = ctx.supply.fresh_id();
                        method_quantified.push(id);
                        method_binders.insert(name.clone(), MonoType::Var(id));
                    }
                }
            }
            let mut constraints = vec![crate::types::SchemeConstraint {
                name: class.name.clone(),
                args: class
                    .params
                    .iter()
                    .map(|parameter| method_binders[parameter].clone())
                    .collect(),
            }];
            for quantifier in &spec.ty.quantifiers {
                for constraint in &quantifier.constraints {
                    constraints.push(crate::types::lower_constraint(
                        constraint,
                        &method_binders,
                    ));
                }
            }
            let body = lower_ty(&spec.ty.ty, &method_binders);
            env.insert(
                spec.name.clone(),
                TypeScheme {
                    quantified: method_quantified,
                    constraints,
                    body,
                },
            );
        }
    }
}

fn validate_class_constraints(
    ctx: &InferCtx,
    declarations: &DeclarationMetadata,
) -> Result<(), String> {
    for constraint in &ctx.constraints {
        let args = constraint
            .args
            .iter()
            .map(|argument| ctx.resolve(argument))
            .collect::<Vec<_>>();
        if args.iter().any(|argument| matches!(argument, MonoType::Var(_))) {
            continue;
        }
        let Some(class) = declarations
            .classes
            .iter()
            .find(|class| class.name == constraint.name)
        else {
            return Err(format!("unknown class constraint '{}'", constraint.name));
        };
        let implemented = declarations.instances.iter().any(|instance| {
            instance.class == class.name
                && instance.target.len() == args.len()
                && instance
                    .target
                    .iter()
                    .zip(&args)
                    .all(|(target, argument)| target == argument)
        });
        if !implemented {
            return Err(format!(
                "no instance of '{}' satisfies {:?}",
                constraint.name, args
            ));
        }
    }
    Ok(())
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
            source: declaration.ty.clone(),
            parameter_ids: declaration
                .params
                .iter()
                .map(|parameter| match &binders[parameter] {
                    MonoType::Var(id) => *id,
                    _ => unreachable!(),
                })
                .collect(),
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


fn install_type_declarations(
    env: &mut TypeEnv,
    declarations: &DeclarationMetadata,
) {
    for declaration in &declarations.types {
        let result = MonoType::Constructor(
            declaration.name.clone(),
            declaration
                .parameter_ids
                .iter()
                .copied()
                .map(MonoType::Var)
                .collect(),
        );
        for constructor in &declaration.constructors {
            let body = match &constructor.payload {
                Some(payload) => MonoType::Function(
                    Box::new(payload.clone()),
                    Box::new(result.clone()),
                ),
                None => result.clone(),
            };
            env.insert(
                constructor.name.clone(),
                TypeScheme {
                    quantified: declaration.parameter_ids.clone(),
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
                        body: TypedExpr {
                            ty: MonoType::Var(0),
                            kind: TypedExprKind::Unresolved(arm.body.clone()),
                        },
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
    let mut method_owners = BTreeMap::<String, String>::new();
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
                    if let Some(owner) = method_owners.get(&spec.name) {
                        return Err(format!(
                            "class method '{}' is declared by both '{}' and '{}';                              global method overload resolution is not available yet",
                            spec.name, owner, class.name
                        ));
                    }
                    method_owners.insert(spec.name.clone(), class.name.clone());
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
