// Type-directed overload resolution at call sites.
//
// At a call `f a1 ... an` where `f` names an overload set:
//
//   1. Retrieve the `OverloadSet` for `f`.
//   2. Instantiate every specialization with fresh variables.
//   3. Check the supplied arguments against each candidate's domain
//      (bidirectionally), discarding candidates that fail arity, unification,
//      or the expected result type — each rejection is recorded with a reason.
//   4. Compare survivors by strict specificity (`dominates`): a candidate is
//      selected iff it is the unique undominated one. Declaration order is
//      NEVER a tiebreaker.
//   5. No survivors  -> a no-matching-overload diagnostic with per-candidate
//      rejection reasons. Several incomparable survivors -> an ambiguity
//      error.
//   6. The selected specialization's id is recorded so lowering never repeats
//      resolution.

use std::fmt;

use crate::specialize::OverloadSet;
use crate::types::{
    instantiate, unify, MonoType, Substitution, TypeScheme, TypeVarSupply,
};

/// Why a candidate specialization was rejected at a call site.
#[derive(Debug, Clone, PartialEq)]
pub enum RejectionReason {
    /// The candidate takes a different number of arguments than supplied.
    Arity { expected: usize, got: usize },
    /// An argument (or the result) failed to unify with the candidate's type.
    Unification { detail: String },
}

impl fmt::Display for RejectionReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RejectionReason::Arity { expected, got } => {
                write!(f, "expects {expected} argument(s), got {got}")
            }
            RejectionReason::Unification { detail } => write!(f, "type mismatch: {detail}"),
        }
    }
}

/// The outcome of resolving a call against an overload set.
#[derive(Debug, Clone, PartialEq)]
pub enum Resolution {
    /// Exactly one specialization applies; carries its id.
    Selected(usize),
    /// No specialization applies.
    NoMatch {
        /// Per-candidate rejection reasons, paired with specialization id.
        rejections: Vec<(usize, RejectionReason)>,
    },
    /// Several applicable specializations are mutually incomparable.
    Ambiguous {
        /// Ids of the surviving (undominated) candidates.
        candidates: Vec<usize>,
    },
}

/// The arity of a curried function type.
fn arity(ty: &MonoType) -> usize {
    match ty {
        MonoType::Function(_, to) => 1 + arity(to),
        _ => 0,
    }
}

/// Peel `n` argument types off a curried function type, returning the
/// parameter types and the remaining result.
fn peel(ty: &MonoType, n: usize) -> Option<(Vec<MonoType>, MonoType)> {
    let mut params = Vec::with_capacity(n);
    let mut cur = ty.clone();
    for _ in 0..n {
        match cur {
            MonoType::Function(from, to) => {
                params.push(*from);
                cur = *to;
            }
            _ => return None,
        }
    }
    Some((params, cur))
}

/// Resolve a call of `set`'s function to `arg_types`, optionally against an
/// expected result type.
///
/// `arg_types` are the inferred types of the supplied arguments (already
/// resolved in the caller's context). `expected_result` is the type the call
/// is checked against, when known; it can eliminate candidates whose result
/// does not unify.
pub fn resolve_call(
    supply: &mut TypeVarSupply,
    set: &OverloadSet,
    arg_types: &[MonoType],
    expected_result: Option<&MonoType>,
) -> Resolution {
    let n = arg_types.len();
    let mut survivors: Vec<(usize, TypeScheme)> = Vec::new();
    let mut rejections: Vec<(usize, RejectionReason)> = Vec::new();

    for spec in &set.specializations {
        // 2. Instantiate the candidate with fresh variables.
        let (body, _) = instantiate(supply, &spec.scheme);

        // 3a. Arity / application shape.
        if arity(&body) < n {
            rejections.push((
                spec.id,
                RejectionReason::Arity {
                    expected: arity(&body),
                    got: n,
                },
            ));
            continue;
        }
        let (params, result) = match peel(&body, n) {
            Some(x) => x,
            None => {
                rejections.push((
                    spec.id,
                    RejectionReason::Arity {
                        expected: arity(&body),
                        got: n,
                    },
                ));
                continue;
            }
        };

        // 3b. Unify supplied arguments with the candidate's domain.
        let mut subst = Substitution::new();
        let mut rejected = None;
        for (arg, param) in arg_types.iter().zip(params.iter()) {
            if let Err(e) = unify(&mut subst, arg, param) {
                rejected = Some(RejectionReason::Unification {
                    detail: format!("{e}"),
                });
                break;
            }
        }
        // 3c. Expected result type can eliminate candidates where sound.
        if rejected.is_none() {
            if let Some(expected) = expected_result {
                let resolved_result = subst.apply(&result);
                if unify(&mut subst, &resolved_result, expected).is_err() {
                    rejected = Some(RejectionReason::Unification {
                        detail: "result type does not match expected type".to_string(),
                    });
                }
            }
        }

        match rejected {
            Some(reason) => rejections.push((spec.id, reason)),
            None => survivors.push((spec.id, spec.scheme.clone())),
        }
    }

    // 4-6. Select the unique undominated survivor by strict specificity.
    match survivors.len() {
        0 => Resolution::NoMatch { rejections },
        1 => Resolution::Selected(survivors[0].0),
        _ => {
            // A survivor is undominated if NO other survivor strictly
            // dominates it. Specificity includes constraints: a candidate that
            // is more specific on the type but more constrained is not
            // automatically preferred.
            let undominated: Vec<usize> = survivors
                .iter()
                .filter(|(id, scheme)| {
                    !survivors.iter().any(|(other_id, other_scheme)| {
                        other_id != id && {
                            let mut probe = TypeVarSupply::new();
                            crate::types::dominates_constrained(
                                &mut probe,
                                other_scheme,
                                scheme,
                            )
                        }
                    })
                })
                .map(|(id, _)| *id)
                .collect();
            match undominated.len() {
                1 => Resolution::Selected(undominated[0]),
                _ => Resolution::Ambiguous {
                    candidates: undominated,
                },
            }
        }
    }
}

// --------------------------------------------------------------------------
// Deferred overload resolution
// --------------------------------------------------------------------------
//
// A curried call may not provide enough information to select a specialization
// at the point the callee is named (`let p = parse`, or `x => convert x`).
// Rather than forcing immediate resolution, inference records an
// `OverloadRef`: a deferred obligation to resolve `name` against an expected
// type once more information arrives (more arguments, or an expected result
// type). The obligation must be discharged before generalization/lowering;
// if it is still ambiguous at a `let` boundary, an annotation is requested.

/// A deferred obligation to resolve an overloaded name.
#[derive(Debug, Clone, PartialEq)]
pub struct OverloadRef {
    /// The overloaded function name.
    pub name: String,
    /// The type variable the resolved value must have. As arguments or an
    /// expected type constrain this variable, the set of viable
    /// specializations shrinks.
    pub expected: MonoType,
    /// The specializations still viable when the ref was created (their ids).
    pub candidates: Vec<usize>,
}

/// The result of forcing a deferred `OverloadRef` once `expected` is known.
pub fn resolve_deferred(
    supply: &mut TypeVarSupply,
    set: &OverloadSet,
    over: &OverloadRef,
    final_expected: &MonoType,
) -> Resolution {
    // Re-resolve the still-viable candidates against the final expected type.
    // The expected type is the FULL curried type of the (possibly partially
    // applied) reference, so we unify it against each candidate's whole body
    // rather than peeling arguments.
    let mut survivors: Vec<(usize, TypeScheme)> = Vec::new();
    let mut rejections = Vec::new();
    for &id in &over.candidates {
        let spec = &set.specializations[id];
        let (body, _) = instantiate(supply, &spec.scheme);
        let mut subst = Substitution::new();
        match unify(&mut subst, &body, final_expected) {
            Ok(()) => survivors.push((id, spec.scheme.clone())),
            Err(e) => rejections.push((
                id,
                RejectionReason::Unification {
                    detail: format!("{e}"),
                },
            )),
        }
    }
    match survivors.len() {
        0 => Resolution::NoMatch { rejections },
        1 => Resolution::Selected(survivors[0].0),
        _ => {
            let undominated: Vec<usize> = survivors
                .iter()
                .filter(|(id, scheme)| {
                    !survivors.iter().any(|(other_id, other_scheme)| {
                        other_id != id && {
                            let mut probe = TypeVarSupply::new();
                            crate::types::dominates_constrained(
                                &mut probe,
                                other_scheme,
                                scheme,
                            )
                        }
                    })
                })
                .map(|(id, _)| *id)
                .collect();
            match undominated.len() {
                1 => Resolution::Selected(undominated[0]),
                _ => Resolution::Ambiguous {
                    candidates: undominated,
                },
            }
        }
    }
}
