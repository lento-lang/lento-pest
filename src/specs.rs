// Associating `spec` declarations with specializations.
//
// Each explicit `spec f : S` is a declared member of `f`'s overload set. This
// module builds the many-to-many compatibility graph between specs and the
// inferred specializations, and checks:
//
//   - every explicit spec has at least one implementing specialization
//     (unless it is an abstract declaration with no clauses at all);
//   - an implementing specialization's scheme is an instance of the spec's
//     skolemized body (the implementation refines the contract);
//   - each specialization either matches at least one explicit spec or gets a
//     synthesized implicit spec with `SpecOrigin::Inferred` — an omitted spec
//     never creates a weaker checking path;
//   - a clause matching zero specs or multiple *incomparable* specs is
//     diagnosed.
//
// Provenance is recorded per specialization: `SpecOrigin::Explicit(span)` or
// `SpecOrigin::Inferred(clause_spans)`.

use std::collections::BTreeMap;
use std::fmt;

use crate::ast::{Quantifier, SpecType};
use crate::semantics::{FunctionGroup, ParsedSpec, SpecOrigin, Span};
use crate::specialize::OverloadSet;
use crate::types::{
    is_permissive_instance, lower_constraint, lower_ty, MonoType, SchemeConstraint, TypeScheme,
    TypeVarId, TypeVarSupply,
};

/// A spec lowered to the internal representation: its scheme plus provenance.
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredSpec {
    pub scheme: TypeScheme,
    pub origin: SpecOrigin,
    /// The source spec statement index, for diagnostics.
    pub index: usize,
}

/// The result of associating specs with one overload set.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecAssociation {
    pub name: String,
    /// Every specialization paired with the spec it satisfies. A
    /// specialization with no explicit spec carries a synthesized implicit
    /// spec (identical checking, different provenance).
    pub bindings: Vec<SpecBinding>,
    /// Specs that no specialization implements (non-abstract: an error).
    pub unsatisfied: Vec<LoweredSpec>,
}

/// One specialization bound to its spec.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecBinding {
    pub specialization_id: usize,
    pub spec: TypeScheme,
    pub origin: SpecOrigin,
}

/// Errors from spec association.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecError {
    pub kind: SpecErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpecErrorKind {
    /// An explicit spec has no implementing specialization.
    UnsatisfiedSpec { name: String, span: Span },
    /// A specialization matches zero explicit specs and no implicit spec
    /// could be synthesized for it (should not happen — the implicit spec is
    /// the specialization's own scheme). Kept for forward compatibility.
    OrphanSpecialization { name: String, specialization: usize },
    /// A specialization matches multiple explicit specs that are mutually
    /// incomparable (neither is an instance of the other).
    AmbiguousSpec {
        name: String,
        specialization: usize,
        specs: Vec<usize>,
    },
}

impl fmt::Display for SpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            SpecErrorKind::UnsatisfiedSpec { name, span } => write!(
                f,
                "spec `{name}` (statement {span:?}) has no implementing specialization"
            ),
            SpecErrorKind::OrphanSpecialization { name, specialization } => write!(
                f,
                "specialization {specialization} of `{name}` matches no spec"
            ),
            SpecErrorKind::AmbiguousSpec {
                name,
                specialization,
                specs,
            } => write!(
                f,
                "specialization {specialization} of `{name}` matches multiple incomparable specs {specs:?}"
            ),
        }
    }
}

impl std::error::Error for SpecError {}

/// Lower a surface `SpecType` to a `TypeScheme`.
///
/// `all a b :: Ord.` quantifiers become quantified variables (fresh ids from
/// `supply`); constraint arguments lower through the same binder environment.
pub fn lower_spec(supply: &mut TypeVarSupply, spec: &SpecType) -> TypeScheme {
    // Map quantifier variable names to fresh type-variable ids.
    let mut binders: BTreeMap<String, MonoType> = BTreeMap::new();
    let mut quantified: Vec<TypeVarId> = Vec::new();
    for Quantifier { vars, .. } in &spec.quantifiers {
        for v in vars {
            let id = supply.fresh_id();
            binders.insert(v.clone(), MonoType::Var(id));
            quantified.push(id);
        }
    }
    // Constraints from every quantifier clause.
    let mut constraints: Vec<SchemeConstraint> = Vec::new();
    for q in &spec.quantifiers {
        for c in &q.constraints {
            constraints.push(lower_constraint(c, &binders));
        }
    }
    let body = lower_ty(&spec.ty, &binders);
    TypeScheme {
        quantified,
        constraints,
        body,
    }
}

/// Associate every explicit spec of a function group with the group's
/// specializations, synthesizing implicit specs where none apply.
///
/// `set` is the partitioned overload set for `group`. Matching is by
/// subsumption: a specialization implements a spec when the specialization's
/// scheme is an instance of the spec's (skolemized) scheme — i.e. the
/// implementation is at least as specific as the contract.
pub fn associate_specs(
    supply: &mut TypeVarSupply,
    group: &FunctionGroup,
    set: &OverloadSet,
) -> Result<SpecAssociation, SpecError> {
    // Lower every explicit spec.
    let lowered: Vec<LoweredSpec> = group
        .explicit_specs
        .iter()
        .map(|ParsedSpec { decl, index }| LoweredSpec {
            scheme: lower_spec(supply, &decl.ty),
            origin: SpecOrigin::Explicit((group.source_span.0, *index)),
            index: *index,
        })
        .collect();

    let mut bindings: Vec<SpecBinding> = Vec::new();
    let mut satisfied: Vec<bool> = vec![false; lowered.len()];

    for spec in &set.specializations {
        // Which explicit specs does this specialization implement?
        let mut matching: Vec<usize> = Vec::new();
        for (i, ls) in lowered.iter().enumerate() {
            let mut probe = TypeVarSupply::new();
            if is_permissive_instance(&mut probe, &ls.scheme, &spec.scheme) {
                matching.push(i);
            }
        }

        match matching.as_slice() {
            [] => {
                // No explicit spec applies: synthesize an implicit spec from
                // the specialization's own principal scheme. The checking path
                // is identical; only the provenance differs. Generalize the
                // scheme's free variables so the implicit spec is quantified
                // exactly like an explicit one.
                let spans: Vec<Span> = spec
                    .clauses
                    .iter()
                    .map(|c| (c.source_index, c.source_index))
                    .collect();
                let implicit = TypeScheme {
                    quantified: spec.scheme.body.free_vars(),
                    constraints: spec.scheme.constraints.clone(),
                    body: spec.scheme.body.clone(),
                };
                bindings.push(SpecBinding {
                    specialization_id: spec.id,
                    spec: implicit,
                    origin: SpecOrigin::Inferred(spans),
                });
            }
            [single] => {
                satisfied[*single] = true;
                bindings.push(SpecBinding {
                    specialization_id: spec.id,
                    spec: lowered[*single].scheme.clone(),
                    origin: lowered[*single].origin.clone(),
                });
            }
            many => {
                // Multiple specs match: they must be comparable (one dominates).
                // If any two are incomparable, the binding is ambiguous.
                if !all_comparable(supply, many.iter().map(|i| &lowered[*i].scheme)) {
                    return Err(SpecError {
                        kind: SpecErrorKind::AmbiguousSpec {
                            name: group.name.clone(),
                            specialization: spec.id,
                            specs: many.to_vec(),
                        },
                    });
                }
                // Comparable: bind to the most specific spec (the one all
                // others are instances of).
                let most = most_specific(supply, many, &lowered);
                satisfied[most] = true;
                bindings.push(SpecBinding {
                    specialization_id: spec.id,
                    spec: lowered[most].scheme.clone(),
                    origin: lowered[most].origin.clone(),
                });
            }
        }
    }

    // Every non-abstract explicit spec needs at least one implementation.
    // A spec-only group (no clauses at all) is an abstract declaration and is
    // allowed to have unsatisfied specs.
    let mut unsatisfied = Vec::new();
    if !set.specializations.is_empty() {
        for (i, ls) in lowered.iter().enumerate() {
            if !satisfied[i] {
                unsatisfied.push(ls.clone());
            }
        }
    }
    // Hard error on the first unsatisfied spec when the group has clauses.
    if !unsatisfied.is_empty() && !group.raw_clauses.is_empty() {
        let first = &unsatisfied[0];
        return Err(SpecError {
            kind: SpecErrorKind::UnsatisfiedSpec {
                name: group.name.clone(),
                span: (first.index, first.index),
            },
        });
    }

    Ok(SpecAssociation {
        name: group.name.clone(),
        bindings,
        unsatisfied,
    })
}

/// Are all schemes mutually comparable (for every pair, one is an instance of
/// the other)?
fn all_comparable<'a>(
    supply: &mut TypeVarSupply,
    schemes: impl Iterator<Item = &'a TypeScheme>,
) -> bool {
    let schemes: Vec<&TypeScheme> = schemes.collect();
    for i in 0..schemes.len() {
        for j in (i + 1)..schemes.len() {
            let ij = is_permissive_instance(supply, schemes[i], schemes[j]);
            let ji = is_permissive_instance(supply, schemes[j], schemes[i]);
            if !ij && !ji {
                return false;
            }
        }
    }
    true
}

/// The index of the most specific spec among `candidates`: the one that is an
/// instance of all the others.
fn most_specific(
    supply: &mut TypeVarSupply,
    candidates: &[usize],
    lowered: &[LoweredSpec],
) -> usize {
    for &c in candidates {
        if candidates.iter().all(|&other| {
            c == other || is_permissive_instance(supply, &lowered[other].scheme, &lowered[c].scheme)
        }) {
            return c;
        }
    }
    candidates[0]
}
