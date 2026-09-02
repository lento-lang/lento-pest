// Associating `spec` declarations with implementations.
//
// Corrected semantic model:
//
//   - **Satisfaction is directional subsumption.** An implementation `I`
//     satisfies a spec `S` iff `Instances(S) ⊆ Instances(I)`: the
//     implementation is AT LEAST AS GENERAL as the contract. `fn f x = x`
//     satisfies `spec f : int -> int`; `fn f (x : int) = x` does NOT satisfy
//     `spec f : all a. a -> a`. See `types::satisfies`.
//
//   - **Specs are optional obligations, implementations are not.** A function
//     or `let` with no spec is simply unchecked-by-contract; it gets an
//     *inferred signature* describing it, which is NOT a spec obligation.
//     Implementations matching zero explicit specs are valid. Only an
//     *unsatisfied spec* (no covering implementation) is an error.
//
//   - **One specialization covers an entire spec.** A spec is satisfied when
//     a SINGLE specialization subsumes it. Multiple value-pattern clauses may
//     collectively satisfy it via exhaustiveness (they live in one
//     specialization). Multiple TYPE specializations never collectively
//     satisfy a spec (that would require closed-world reasoning over the
//     domain — deferred).
//
//   - **`let` can satisfy a spec.** A named `let` contributes one irrefutable
//     implementation with no pattern-dispatch matrix beyond its lambda
//     parameters. Repeated `let` bindings of one name are a duplicate binding,
//     never an overload; a `let f` and `fn f` in one scope collide (rejected
//     during collection).

use std::collections::BTreeMap;
use std::fmt;

use crate::ast::{Quantifier, SpecType};
use crate::semantics::{FunctionGroup, ParsedSpec, Span};
use crate::specialize::OverloadSet;
use crate::types::{
    implementation_covers_spec, lower_constraint, lower_ty, MonoType, SchemeConstraint, TypeScheme,
    TypeVarId, TypeVarSupply,
};

/// Where a signature (the type ascribed to a specialization) came from.
///
/// An inferred signature DESCRIBES an implementation; it is not a spec
/// obligation. A spec-assisted signature records which specs constrained the
/// implementation's checking (via constraint propagation over its provisional
/// principal type) — without turning the implementation into a monomorphic
/// retype under any one spec.
#[derive(Debug, Clone, PartialEq)]
pub enum SignatureOrigin {
    /// Inferred from the implementation alone; no spec constrained it.
    Inferred,
    /// One or more specs constrained this specialization's checking. The
    /// implementation may satisfy several specs (a polymorphic impl can cover
    /// both `int -> int` and `str -> str`); all of them are recorded, in
    /// source order. Specs are obligations, not dispatch selectors.
    SpecAssisted(Vec<usize>),
}

/// A spec lowered to the internal representation.
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredSpec {
    pub scheme: TypeScheme,
    /// The source spec statement index.
    pub index: usize,
}

/// The signature ascribed to one specialization.
#[derive(Debug, Clone, PartialEq)]
pub struct Signature {
    pub specialization_id: usize,
    pub scheme: TypeScheme,
    pub origin: SignatureOrigin,
}

/// The result of associating specs with one overload set.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecAssociation {
    pub name: String,
    /// The signature of every specialization (declared or inferred).
    pub signatures: Vec<Signature>,
    /// Explicit specs with no covering specialization (each an error unless
    /// the group is abstract — has no clauses at all).
    pub unsatisfied: Vec<LoweredSpec>,
}

/// Errors from spec association.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecError {
    pub kind: SpecErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpecErrorKind {
    /// An explicit spec has no specialization that covers it.
    UnsatisfiedSpec { name: String, span: Span },
}

impl fmt::Display for SpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            SpecErrorKind::UnsatisfiedSpec { name, span } => write!(
                f,
                "spec `{name}` (statement {span:?}) is not implemented by any specialization"
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
    let mut binders: BTreeMap<String, MonoType> = BTreeMap::new();
    let mut quantified: Vec<TypeVarId> = Vec::new();
    for Quantifier { vars, .. } in &spec.quantifiers {
        for v in vars {
            let id = supply.fresh_id();
            binders.insert(v.clone(), MonoType::Var(id));
            quantified.push(id);
        }
    }
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

/// Associate a group's explicit specs with its specializations.
///
/// For each specialization, record EVERY declared spec it covers (directional
/// subsumption: the implementation is at least as general as the spec). A
/// specialization may cover several specs — that is not ambiguous, because
/// specs are obligations, not dispatch selectors. A specialization covering no
/// spec simply carries an inferred signature (specs are optional).
///
/// Each explicit spec must be covered by AT LEAST ONE specialization; an
/// uncovered spec is an error unless the group is abstract (no clauses).
pub fn associate_specs(
    supply: &mut TypeVarSupply,
    group: &FunctionGroup,
    set: &OverloadSet,
) -> Result<SpecAssociation, SpecError> {
    let lowered: Vec<LoweredSpec> = group
        .explicit_specs
        .iter()
        .map(|ParsedSpec { decl, index }| LoweredSpec {
            scheme: lower_spec(supply, &decl.ty),
            index: *index,
        })
        .collect();

    let mut signatures = Vec::new();
    let mut covered = vec![false; lowered.len()];

    for spec in &set.specializations {
        // Collect every spec this implementation covers. Covering several
        // specs is fine (a polymorphic impl covers both `int -> int` and
        // `str -> str`); it does not split the implementation.
        let mut matched: Vec<usize> = Vec::new();
        for (i, ls) in lowered.iter().enumerate() {
            let mut probe = TypeVarSupply::new();
            if implementation_covers_spec(&mut probe, &spec.scheme, &ls.scheme) {
                covered[i] = true;
                matched.push(i);
            }
        }
        if matched.is_empty() {
            // Inferred signature: the specialization's own scheme,
            // generalized over its free variables. Not an obligation.
            let inferred = TypeScheme {
                quantified: spec.scheme.body.free_vars(),
                constraints: spec.scheme.constraints.clone(),
                body: spec.scheme.body.clone(),
            };
            signatures.push(Signature {
                specialization_id: spec.id,
                scheme: inferred,
                origin: SignatureOrigin::Inferred,
            });
        } else {
            // The signature keeps the implementation's OWN (possibly more
            // general) principal scheme — spec assistance propagates expected
            // types but does not constrain the final scheme to any one spec.
            let indices: Vec<usize> = matched.iter().map(|&i| lowered[i].index).collect();
            signatures.push(Signature {
                specialization_id: spec.id,
                scheme: spec.scheme.clone(),
                origin: SignatureOrigin::SpecAssisted(indices),
            });
        }
    }

    // A spec must be covered by ONE specialization (collective type-domain
    // coverage is deferred). Spec-only (abstract) groups are exempt.
    let mut unsatisfied = Vec::new();
    if !group.raw_clauses.is_empty() {
        for (i, ls) in lowered.iter().enumerate() {
            if !covered[i] {
                unsatisfied.push(ls.clone());
            }
        }
        if let Some(first) = unsatisfied.first() {
            return Err(SpecError {
                kind: SpecErrorKind::UnsatisfiedSpec {
                    name: group.name.clone(),
                    span: (first.index, first.index),
                },
            });
        }
    }

    Ok(SpecAssociation {
        name: group.name.clone(),
        signatures,
        unsatisfied,
    })
}
