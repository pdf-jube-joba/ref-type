//! Occurrence trees are separate from hash-consed term identities.
use crate::{
    exp::Exp,
    program::{ComputationTerm, ComputationType, ValueTerm, ValueType},
};
use hir::{AstId, SourceLocation, SourceMap};
use std::{cell::RefCell, collections::HashMap};

impl Term {
    fn raw(self) -> Option<crate::traversal::Term> {
        use crate::traversal::Term as Raw;
        Some(match self {
            Self::Pts(term) => Raw::Logical(term),
            Self::ValueType(term) => Raw::ValueType(term),
            Self::ComputationType(term) => Raw::ComputationType(term),
            Self::Value(term) => Raw::Value(term),
            Self::Computation(term) => Raw::Computation(term),
            Self::Kernel(_) => return None,
        })
    }
}

impl From<crate::traversal::Term> for Term {
    fn from(value: crate::traversal::Term) -> Self {
        use crate::traversal::Term as Raw;
        match value {
            Raw::Logical(term) => Self::Pts(term),
            Raw::ValueType(term) => Self::ValueType(term),
            Raw::ComputationType(term) => Self::ComputationType(term),
            Raw::Value(term) => Self::Value(term),
            Raw::Computation(term) => Self::Computation(term),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Term {
    Pts(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value(ValueTerm),
    Computation(ComputationTerm),
    Kernel(kernel::syntax::Expression),
}

macro_rules! term_from {
    ($($ty:ty => $variant:ident),* $(,)?) => {$(
        impl From<$ty> for Term {
            fn from(value: $ty) -> Self { Self::$variant(value) }
        }
    )*};
}
term_from! {
    Exp => Pts, ValueType => ValueType, ComputationType => ComputationType,
    ValueTerm => Value, ComputationTerm => Computation, kernel::syntax::Expression => Kernel,
}

#[derive(Debug)]
struct Occurrence {
    origin: Option<AstId>,
    parent: Option<usize>,
    terms: Vec<Term>,
    lowered: HashMap<Term, AstId>,
    generated: bool,
}

#[derive(Debug, Default)]
struct State {
    occurrences: Vec<Occurrence>,
    active: Vec<usize>,
    by_term: HashMap<Term, Vec<usize>>,
    related: HashMap<(Term, Term), usize>,
    lowered: HashMap<(Term, Term), usize>,
    error: Vec<Term>,
    checking_depth: usize,
}

#[derive(Debug, Default)]
pub struct Provenance(RefCell<State>);

impl Provenance {
    pub fn enter(&self, origin: Option<AstId>, sources: &SourceMap) -> usize {
        let mut state = self.0.borrow_mut();
        let id = state.occurrences.len();
        let parent = state.active.last().copied();
        let origin = origin.or_else(|| {
            Some(sources.generated(
                parent.and_then(|id| state.occurrences[id].origin),
                hir::GenerationReason::Elaboration,
            ))
        });
        state.occurrences.push(Occurrence {
            origin,
            parent,
            terms: Vec::new(),
            lowered: HashMap::new(),
            generated: false,
        });
        state.active.push(id);
        id
    }

    pub fn leave(
        &self,
        id: usize,
        term: Option<Term>,
        arena: &crate::exp::Arena,
        sources: &SourceMap,
    ) {
        let mut state = self.0.borrow_mut();
        assert_eq!(state.active.pop(), Some(id));
        if let Some(term) = term {
            state.occurrences[id].terms.push(term);
            state.by_term.entry(term).or_default().push(id);
            if state.active.is_empty() {
                Self::complete_generated(&mut state, id, term, arena, sources);
            }
        }
    }

    fn complete_generated(
        state: &mut State,
        root: usize,
        term: Term,
        arena: &crate::exp::Arena,
        sources: &SourceMap,
    ) {
        let mut pending = state
            .occurrences
            .iter()
            .enumerate()
            .skip(root)
            .filter(|(_, occurrence)| !occurrence.generated)
            .filter_map(|(id, occurrence)| occurrence.terms.first().map(|term| (id, *term, id)))
            .collect::<Vec<_>>();
        debug_assert!(
            pending
                .iter()
                .any(|(id, candidate, _)| *id == root && *candidate == term)
        );
        let mut explicit_terms: HashMap<Term, Vec<usize>> = HashMap::new();
        for (id, term, _) in &pending {
            explicit_terms.entry(*term).or_default().push(*id);
        }
        let mut seen = std::collections::HashSet::new();
        while let Some((parent, term, source_owner)) = pending.pop() {
            let Some(raw) = term.raw() else { continue };
            if !seen.insert((source_owner, term)) {
                continue;
            }
            let mut children = Vec::new();
            raw.visit_children(arena, |child, _| children.push(Term::from(child)));
            for child in children {
                let explicit = explicit_terms.get(&child).is_some_and(|ids| {
                    ids.iter().any(|id| {
                        if state.occurrences[*id].generated {
                            return false;
                        }
                        let mut ancestor = Some(*id);
                        while let Some(id) = ancestor {
                            if id == source_owner {
                                return true;
                            }
                            ancestor = state.occurrences[id].parent;
                        }
                        false
                    })
                });
                if explicit {
                    continue;
                }
                let origin = sources.generated(
                    state.occurrences[parent].origin,
                    hir::GenerationReason::Elaboration,
                );
                let id = state.occurrences.len();
                state.occurrences.push(Occurrence {
                    origin: Some(origin),
                    parent: Some(parent),
                    terms: vec![child],
                    lowered: HashMap::new(),
                    generated: true,
                });
                state.by_term.entry(child).or_default().push(id);
                pending.push((id, child, source_owner));
            }
        }
    }

    pub fn current_origin(&self) -> Option<AstId> {
        let state = self.0.borrow();
        state
            .active
            .iter()
            .rev()
            .find_map(|id| state.occurrences[*id].origin)
    }

    /// Zonked and lowered terms retain all occurrences of the original term.
    pub fn relate(&self, original: impl Into<Term>, result: impl Into<Term>) {
        let original = original.into();
        let result = result.into();
        if original == result {
            return;
        }
        let mut state = self.0.borrow_mut();
        let start = state.related.get(&(original, result)).copied().unwrap_or(0);
        let ids = state
            .by_term
            .get(&original)
            .map(|ids| ids[start..].to_vec())
            .unwrap_or_default();
        state.related.insert((original, result), start + ids.len());
        for id in ids {
            if !state.occurrences[id].terms.contains(&result) {
                state.occurrences[id].terms.push(result);
                state.by_term.entry(result).or_default().push(id);
            }
        }
    }

    pub fn clear_error(&self) {
        self.0.borrow_mut().error.clear();
    }

    pub fn check<T, E>(
        &self,
        term: impl Into<Term>,
        check: impl FnOnce() -> Result<T, E>,
    ) -> Result<T, E> {
        {
            let mut state = self.0.borrow_mut();
            if state.checking_depth == 0 {
                state.error.clear();
            }
            state.checking_depth += 1;
        }
        let result = check();
        let mut state = self.0.borrow_mut();
        state.checking_depth -= 1;
        if result.is_err() {
            let term = term.into();
            if state.error.last() != Some(&term) {
                state.error.push(term);
            }
        } else if state.checking_depth == 0 {
            state.error.clear();
        }
        result
    }

    pub fn lowered(
        &self,
        original: impl Into<Term>,
        result: kernel::syntax::Expression,
        sources: &SourceMap,
    ) {
        let original = original.into();
        self.relate(original, result);
        let result = Term::Kernel(result);
        let mut state = self.0.borrow_mut();
        let start = state.lowered.get(&(original, result)).copied().unwrap_or(0);
        let ids = state
            .by_term
            .get(&original)
            .map(|ids| ids[start..].to_vec())
            .unwrap_or_default();
        state.lowered.insert((original, result), start + ids.len());
        for id in ids {
            let occurrence = &mut state.occurrences[id];
            occurrence.lowered.entry(result).or_insert_with(|| {
                sources.generated(occurrence.origin, hir::GenerationReason::KernelLowering)
            });
        }
    }

    pub fn record_error(&self, path: &[Term]) {
        self.0.borrow_mut().error = path.to_vec();
    }

    /// Match the failing leaf and its checking ancestors. An ambiguous shared
    /// leaf resolves to the common source ancestor, never an arbitrary use.
    pub fn error_origin(
        &self,
        sources: &SourceMap,
        owner: Option<&SourceLocation>,
    ) -> Option<AstId> {
        let state = self.0.borrow();
        let path = &state.error;
        if path.is_empty() {
            return None;
        }
        let mut best = Vec::new();
        let mut best_score = (0, 0, std::cmp::Reverse(usize::MAX));
        for (id, occurrence) in state.occurrences.iter().enumerate() {
            let Some(location) = occurrence.origin.and_then(|id| sources.location(id)) else {
                continue;
            };
            if owner.is_some_and(|owner| {
                owner.source.id != location.source.id
                    || location.span.start < owner.span.start
                    || owner.span.end < location.span.end
            }) {
                continue;
            }
            let Some(first) = path.iter().position(|term| occurrence.terms.contains(term)) else {
                continue;
            };
            let mut score = 1;
            let mut gaps = 0;
            let mut ancestor = occurrence.parent;
            for term in &path[first + 1..] {
                if occurrence.terms.contains(term) {
                    continue;
                }
                let mut search = ancestor;
                while let Some(parent) = search {
                    let candidate = &state.occurrences[parent];
                    if candidate.terms.contains(term) {
                        score += 1;
                        ancestor = candidate.parent;
                        break;
                    }
                    gaps += 1;
                    search = candidate.parent;
                }
            }
            // Prefer the actual failing leaf over a matching outer judgement.
            let score = (path.len() - first, score, std::cmp::Reverse(gaps));
            if score > best_score {
                best.clear();
                best_score = score;
            }
            if score == best_score {
                best.push(id);
            }
        }
        let first = *best.first()?;
        let mut common = Some(first);
        while let Some(id) = common {
            if best.iter().all(|other| {
                let mut next = Some(*other);
                while let Some(candidate) = next {
                    if candidate == id {
                        return true;
                    }
                    next = state.occurrences[candidate].parent;
                }
                false
            }) {
                let occurrence = &state.occurrences[id];
                return path
                    .iter()
                    .find_map(|term| occurrence.lowered.get(term).copied())
                    .or(occurrence.origin);
            }
            common = state.occurrences[id].parent;
        }
        // Re-elaboration can create several trees for the same written occurrence.
        let origin = state.occurrences[first].origin;
        best.iter()
            .all(|id| state.occurrences[*id].origin == origin)
            .then_some(origin)
            .flatten()
    }
}
