// Semantic declaration collection and the typed semantic IR.
//
// The parser AST (`ast`) is lossless: every `fn` clause and every `spec` is a
// statement in source order. This module adds the semantic layer on top:
//
//   1. `collect_function_groups` walks a parsed program once and gathers every
//      `spec` and `fn` declaration into `FunctionGroup`s keyed by name. Grouping
//      is purely lexical (same name, same scope): clauses may be separated by
//      specs, type declarations, or unrelated declarations, and adjacency never
//      defines semantic grouping. Source order survives only as metadata
//      (`source_indices`/`source_span`) for diagnostics and for pattern-clause
//      order during pattern dispatch.
//   2. Collisions between a function group and an incompatible non-function
//      binding (`let`, `type`) in the same namespace are rejected.
//   3. The typed semantic AST (`TypedProgram` … `TypedPatternClause`) is defined
//      here so later phases (type inference, specialization, overload
//      resolution) have a stable IR to fill in. `FnDecl` is never rewritten
//      into `LetDecl` to encode overloading; the typed IR replaces the
//      `grouped_fn`/`desugar_program` path after typing.

use std::fmt;

use crate::ast::{
    Decl, Expr, FnDecl, LetDecl, Lit, MatchArm, PatKind, Pattern, Program, SpecDecl, Stmt, Ty,
    TypeDecl,
};

/// A source span as 0-based byte offsets into the program source.
pub type Span = (usize, usize);

/// An explicit `spec name : S` declaration collected into a function group.
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedSpec {
    pub decl: SpecDecl,
    /// Index of the spec statement within the program's statement list.
    pub index: usize,
}

/// Every `spec` and `fn` declaration for one name in one lexical scope,
/// collected independently of statement adjacency.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionGroup {
    pub name: String,
    /// Explicit specs for this name, in source order.
    pub explicit_specs: Vec<ParsedSpec>,
    /// The raw clauses, in source order. Order is metadata only: it drives
    /// pattern-clause dispatch and diagnostics, never semantic grouping.
    pub raw_clauses: Vec<FnDecl>,
    /// First-to-last declaration span of the group, as statement indices.
    pub source_span: Span,
    /// Statement indices of the clauses, parallel to `raw_clauses`.
    pub source_indices: Vec<usize>,
}

/// A declaration that cannot share a name with a function group.
#[derive(Debug, Clone, PartialEq)]
pub enum ConflictingDecl {
    Let(LetDecl),
    Type(TypeDecl),
}

impl ConflictingDecl {
    fn keyword(&self) -> &'static str {
        match self {
            ConflictingDecl::Let(_) => "let",
            ConflictingDecl::Type(_) => "type",
        }
    }
}

/// An error raised while collecting function groups.
#[derive(Debug, Clone, PartialEq)]
pub struct CollectError {
    pub kind: CollectErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CollectErrorKind {
    /// A `fn` group and a non-function binding use the same name in one scope.
    Conflict {
        name: String,
        /// `let` or `type`.
        other_kind: &'static str,
        /// Statement indices of the conflicting declarations.
        spans: Vec<usize>,
    },
    /// A `spec` exists for a name that is bound by an incompatible
    /// non-function declaration, with no clauses to attach it to.
    SpecOnNonFunction {
        name: String,
        other_kind: &'static str,
        spans: Vec<usize>,
    },
}

impl fmt::Display for CollectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            CollectErrorKind::Conflict {
                name,
                other_kind,
                spans,
            } => write!(
                f,
                "declaration collision: function `{name}` conflicts with a `{other_kind}` \
                 binding of the same name in the same scope (statements {spans:?})"
            ),
            CollectErrorKind::SpecOnNonFunction {
                name,
                other_kind,
                spans,
            } => write!(
                f,
                "declaration collision: `spec {name}` has no function clauses and `{name}` is \
                 already bound by a `{other_kind}` declaration (statements {spans:?})"
            ),
        }
    }
}

impl std::error::Error for CollectError {}

/// The result of collecting one scope: function groups plus the statements
/// that are not part of any function group.
#[derive(Debug, Clone, PartialEq)]
pub struct CollectedProgram {
    /// Function groups keyed by name, ordered by first declaration.
    pub function_groups: Vec<FunctionGroup>,
    /// Statements that carry no function/spec declarations, in source order:
    /// lets, type synonyms, and bare expressions.
    pub statements: Vec<Stmt>,
}

/// Collect every `spec` and `fn` declaration by lexical scope and name.
///
/// Clauses may be separated by specs, type declarations, or unrelated
/// declarations: all same-name clauses in the statement list land in one
/// group regardless of position. Source order is kept only as
/// `source_indices`/`source_span` metadata.
///
/// Rejects collisions between a function group and an incompatible
/// non-function binding (`let`, `type`) in the same namespace.
pub fn collect_function_groups(program: &Program) -> Result<CollectedProgram, CollectError> {
    // Preserve first-declaration order for deterministic diagnostics.
    let mut order: Vec<String> = Vec::new();
    let mut groups: Vec<FunctionGroup> = Vec::new();
    // (statement index, declaration) for non-function named bindings.
    let mut non_fn_bindings: Vec<(usize, ConflictingDecl)> = Vec::new();
    let mut statements: Vec<Stmt> = Vec::new();

    for (index, stmt) in program.statements.iter().enumerate() {
        match stmt {
            Stmt::Decl(Decl::Fn(f)) => {
                let group = group_mut(&mut order, &mut groups, &f.name, index);
                group.raw_clauses.push(f.clone());
                group.source_indices.push(index);
                group.source_span.1 = index;
            }
            Stmt::Decl(Decl::Spec(s)) => {
                let group = group_mut(&mut order, &mut groups, &s.name, index);
                group.explicit_specs.push(ParsedSpec {
                    decl: s.clone(),
                    index,
                });
                group.source_span.1 = index;
            }
            Stmt::Decl(Decl::Let(l)) => {
                if let PatKind::Var(name) = &l.pattern.kind {
                    non_fn_bindings.push((index, ConflictingDecl::Let(l.clone())));
                    let _ = name;
                }
                statements.push(stmt.clone());
            }
            Stmt::Decl(Decl::Type(t)) => {
                non_fn_bindings.push((index, ConflictingDecl::Type(t.clone())));
                statements.push(stmt.clone());
            }
            _ => statements.push(stmt.clone()),
        }
    }

    // Collision check, reported in declaration order for determinism.
    let mut collisions: Vec<(usize, CollectError)> = Vec::new();
    for (index, decl) in &non_fn_bindings {
        let (name, other_kind) = match decl {
            ConflictingDecl::Let(l) => match &l.pattern.kind {
                PatKind::Var(n) => (n.clone(), decl.keyword()),
                _ => continue,
            },
            ConflictingDecl::Type(t) => (t.name.clone(), decl.keyword()),
        };
        if let Some(group) = groups.iter().find(|g| g.name == name) {
            let mut spans = vec![*index];
            spans.extend(group.source_indices.iter().copied());
            spans.extend(group.explicit_specs.iter().map(|s| s.index));
            spans.sort_unstable();
            let kind = if group.raw_clauses.is_empty() {
                CollectErrorKind::SpecOnNonFunction {
                    name,
                    other_kind,
                    spans,
                }
            } else {
                CollectErrorKind::Conflict {
                    name,
                    other_kind,
                    spans,
                }
            };
            collisions.push((*index, CollectError { kind }));
        }
    }
    collisions.sort_by_key(|(index, _)| *index);
    if let Some((_, err)) = collisions.into_iter().next() {
        return Err(err);
    }

    Ok(CollectedProgram {
        function_groups: groups,
        statements,
    })
}

fn group_mut<'a>(
    order: &mut Vec<String>,
    groups: &'a mut Vec<FunctionGroup>,
    name: &str,
    index: usize,
) -> &'a mut FunctionGroup {
    if !order.iter().any(|n| n == name) {
        order.push(name.to_string());
        groups.push(FunctionGroup {
            name: name.to_string(),
            explicit_specs: Vec::new(),
            raw_clauses: Vec::new(),
            source_span: (index, index),
            source_indices: Vec::new(),
        });
    }
    groups.iter_mut().find(|g| g.name == name).unwrap()
}

// --------------------------------------------------------------------------
// Typed semantic IR
// --------------------------------------------------------------------------
//
// The typed IR is what later phases produce and lowering consumes:
//
//   ParsedFnClause / ParsedSpec            (parser AST, lossless)
//       |
//       v
//   FunctionGroup                          (declaration collection, above)
//       |
//       v
//   TypedOverloadSet
//       +-- TypedSpecialization            (one principal scheme)
//             +-- TypedPatternClause       (pattern dispatch within a
//                                           specialization, source-ordered)
//
// Overloading is represented explicitly here; it is never encoded by
// rewriting `FnDecl` into `LetDecl`.

/// Where a specialization's spec came from.
#[derive(Debug, Clone, PartialEq)]
pub enum SpecOrigin {
    /// An explicit `spec f : S` in the source, with its statement span.
    Explicit(Span),
    /// Synthesized from the clauses that implement it.
    Inferred(Vec<Span>),
}

/// A callable type scheme. Quantified variables are `TypeVarId`s over a
/// `MonoType` body (the internal inference representation from `types`);
/// the legacy `ast::Ty`-bodied `TypeScheme` below is retained only until the
/// inference pipeline switches the typed IR over.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub quantified: Vec<String>,
    pub constraints: Vec<crate::ast::Constraint>,
    pub body: Ty,
}

/// One clause after type checking: its patterns plus the inferred type.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedPatternClause {
    /// The patterns as written (value dispatch), in parameter order.
    pub patterns: Vec<Pattern>,
    /// The curried clause type `P1 -> ... -> Pn -> R` (type dispatch).
    /// Pattern dispatch and type dispatch are separate stages, so both are
    /// retained.
    pub clause_ty: Ty,
    pub body: TypedExpr,
    /// Statement index of the source clause, for diagnostics.
    pub source_index: usize,
}

/// One specialization of an overloaded function: clauses sharing one
/// principal callable scheme.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedSpecialization {
    /// Stable identity, recorded in typed call expressions so lowering never
    /// repeats overload resolution.
    pub id: usize,
    pub scheme: TypeScheme,
    pub origin: SpecOrigin,
    /// Clauses in source (pattern-dispatch) order.
    pub clauses: Vec<TypedPatternClause>,
}

/// All specializations of one function name.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedOverloadSet {
    pub name: String,
    pub specializations: Vec<TypedSpecialization>,
}

/// An expression annotated with its type; call expressions additionally
/// record the overload resolution result.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub ty: Ty,
    pub kind: TypedExprKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedExprKind {
    Lit(Lit),
    Var(String),
    /// A call whose overload has been resolved: `specialization` is the id of
    /// the selected `TypedSpecialization` when the callee names an overload
    /// set, so lowering never repeats resolution.
    Call {
        callee: Box<TypedExpr>,
        args: Vec<TypedExpr>,
        specialization: Option<usize>,
    },
    Lambda {
        params: Vec<Pattern>,
        body: Box<TypedExpr>,
    },
    Match {
        scrutinee: Box<TypedExpr>,
        arms: Vec<TypedMatchArm>,
    },
    /// A construct not yet lowered into the typed IR; carries the parsed
    /// expression until its typed form is defined.
    Unresolved(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedMatchArm {
    pub pattern: Pattern,
    pub guard: Option<TypedExpr>,
    pub body: TypedExpr,
}

/// A typed `let` binding.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedLet {
    pub mutable: bool,
    pub pattern: Pattern,
    pub annotation: Option<Ty>,
    pub value: TypedExpr,
}

/// A fully typed program, ready for lowering.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedProgram {
    pub overloads: Vec<TypedOverloadSet>,
    pub lets: Vec<TypedLet>,
    /// Top-level expressions, in source order relative to `lets`.
    pub exprs: Vec<TypedExpr>,
}

/// Lower a typed program back into the parsed AST shape the evaluator
/// understands: each overload set becomes one curried `let` whose body
/// pattern-matches on its specialization's clauses.
///
/// This is the typed replacement for `ast::grouped_fn`/`desugar_program`:
/// grouping decisions come from type checking (one `TypedOverloadSet` per
/// function, one match per specialization), not from name/arity adjacency
/// while walking statements.
pub fn lower_typed_program(program: &TypedProgram) -> Program {
    let mut statements = Vec::new();
    for set in &program.overloads {
        statements.push(Stmt::Decl(Decl::Let(lower_overload_set(set))));
    }
    for l in &program.lets {
        statements.push(Stmt::Decl(Decl::Let(lower_typed_let(l))));
    }
    for e in &program.exprs {
        statements.push(Stmt::Expr(lower_typed_expr(e)));
    }
    let spans = statements
        .iter()
        .map(|_| crate::ast::Span { line: 0, col: 0 })
        .collect();
    Program { statements, spans }
}

fn lower_overload_set(set: &TypedOverloadSet) -> LetDecl {
    // Until multiple specializations share a runtime representation, each
    // specialization lowers independently and a single-specialization set is
    // just that specialization's dispatcher.
    let value = match set.specializations.as_slice() {
        [spec] => lower_specialization(&set.name, spec),
        _ => unimplemented!("multi-specialization lowering arrives with overload resolution"),
    };
    LetDecl {
        mutable: false,
        pattern: Pattern {
            annotation: None,
            kind: PatKind::Var(set.name.clone()),
        },
        annotation: None,
        value,
    }
}

/// Lower one specialization to `v1 => ... => vk => match (v1, ..., vk) { ... }`,
/// preserving pattern-clause source order.
fn lower_specialization(name: &str, spec: &TypedSpecialization) -> Expr {
    let arity = spec.clauses.first().map(|c| c.patterns.len()).unwrap_or(0);
    let bind: Vec<String> = (0..arity)
        .map(|i| match spec.clauses.first().map(|c| &c.patterns[i].kind) {
            Some(PatKind::Var(n)) => n.clone(),
            _ => format!("__l{name}{i}"),
        })
        .collect();

    let scrutinee = if arity == 1 {
        Expr::Var(crate::ast::VarExpr {
            name: bind[0].clone(),
        })
    } else {
        Expr::Tuple(crate::ast::TupleExpr {
            items: bind
                .iter()
                .map(|b| Expr::Var(crate::ast::VarExpr { name: b.clone() }))
                .collect(),
        })
    };

    let arms: Vec<MatchArm> = spec
        .clauses
        .iter()
        .map(|clause| {
            let pattern = if clause.patterns.len() == 1 {
                clause.patterns[0].clone()
            } else {
                Pattern {
                    annotation: None,
                    kind: PatKind::Tuple(clause.patterns.clone()),
                }
            };
            MatchArm {
                pattern,
                guard: None,
                body: Box::new(lower_typed_expr(&clause.body)),
            }
        })
        .collect();

    let mut value = Expr::Match(crate::ast::MatchExpr {
        scrutinee: Box::new(scrutinee),
        arms,
    });
    for b in bind.iter().rev() {
        value = Expr::Lambda(crate::ast::LambdaExpr {
            params: vec![Pattern {
                annotation: None,
                kind: PatKind::Var(b.clone()),
            }],
            body: Box::new(value),
        });
    }
    value
}

fn lower_typed_let(l: &TypedLet) -> LetDecl {
    LetDecl {
        mutable: l.mutable,
        pattern: l.pattern.clone(),
        annotation: l.annotation.clone(),
        value: lower_typed_expr(&l.value),
    }
}

fn lower_typed_expr(e: &TypedExpr) -> Expr {
    match &e.kind {
        TypedExprKind::Lit(lit) => Expr::Lit(crate::ast::LitExpr { value: lit.clone() }),
        TypedExprKind::Var(name) => Expr::Var(crate::ast::VarExpr { name: name.clone() }),
        TypedExprKind::Call { callee, args, .. } => Expr::Call(crate::ast::CallExpr {
            callee: Box::new(lower_typed_expr(callee)),
            args: args.iter().map(lower_typed_expr).collect(),
        }),
        TypedExprKind::Lambda { params, body } => Expr::Lambda(crate::ast::LambdaExpr {
            params: params.clone(),
            body: Box::new(lower_typed_expr(body)),
        }),
        TypedExprKind::Match { scrutinee, arms } => Expr::Match(crate::ast::MatchExpr {
            scrutinee: Box::new(lower_typed_expr(scrutinee)),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm.guard.as_ref().map(lower_typed_expr),
                    body: Box::new(lower_typed_expr(&arm.body)),
                })
                .collect(),
        }),
        TypedExprKind::Unresolved(expr) => (**expr).clone(),
    }
}
