//! Source view classification over the kernel's capture-aware child traversal.
use super::{environment::ModuleArgument, exp::*, ids::InductiveId, program::*};
use rustc_hash::FxHashMap;

pub(crate) trait Rewrite {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term>;
    fn finish(&mut self, _arena: &Arena, _term: Term, _depth: usize, result: Term) -> Term {
        result
    }
}

impl<F: FnMut(Term, usize) -> Option<Term>> Rewrite for F {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term> {
        self(term, depth)
    }
}

/// A transformation must depend only on the node and binder depth for its
/// results to be shared across paths through the same syntax DAG.
pub(crate) struct Memoized<F> {
    rewrite: F,
    results: FxHashMap<(Term, usize), Term>,
}

impl<F: Rewrite> Memoized<F> {
    pub(crate) fn new(rewrite: F) -> Self {
        Self {
            rewrite,
            results: FxHashMap::default(),
        }
    }
}

impl<F: Rewrite> Rewrite for Memoized<F> {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term> {
        if let Some(&result) = self.results.get(&(term, depth)) {
            return Some(result);
        }
        let result = self.rewrite.rewrite(term, depth)?;
        if result != term {
            self.results.insert((term, depth), result);
        }
        Some(result)
    }

    fn finish(&mut self, arena: &Arena, term: Term, depth: usize, result: Term) -> Term {
        let result = self.rewrite.finish(arena, term, depth, result);
        self.results.insert((term, depth), result);
        result
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Term {
    Logical(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value(ValueTerm),
    Computation(ComputationTerm),
}

impl Term {
    /// Visit immediate children with their local binder depths.
    pub(crate) fn visit_children(self, arena: &Arena, mut visit: impl FnMut(Term, usize)) {
        self.map_children(arena, |term, depth| {
            visit(term, depth);
            term
        });
    }

    pub(crate) fn expression(self) -> kernel::syntax::Expression {
        match self {
            Self::Logical(e) => e.0,
            Self::ValueType(e) => e.0,
            Self::ComputationType(e) => e.0,
            Self::Value(e) => e.0,
            Self::Computation(e) => e.0,
        }
    }

    fn with_expression(self, e: kernel::syntax::Expression) -> Self {
        match self {
            Self::Logical(_) => Self::Logical(Exp(e)),
            Self::ValueType(_) => Self::ValueType(ValueType(e)),
            Self::ComputationType(_) => Self::ComputationType(ComputationType(e)),
            Self::Value(_) => Self::Value(ValueTerm(e)),
            Self::Computation(_) => Self::Computation(ComputationTerm(e)),
        }
    }

    /// Only source view families are classified here. Child order and binder
    /// depths come from the kernel, including the binder in Program products.
    fn map_children(self, arena: &Arena, mut visit: impl FnMut(Term, usize) -> Term) -> Term {
        use kernel::syntax::Node as N;
        let mut expression = self.expression();
        if let N::Definition { id, arguments } = arena.core.get(expression)
            && !matches!(self, Self::Logical(_))
        {
            // Program views may expose a source template or an instantiated body.
            expression = arena.reference_view(id, arguments, true);
        }
        let node = arena.core.read(expression);
        // A reflected module parameter is one source identity.
        if matches!(&*node, N::Reflect { .. }) {
            return self.with_expression(expression);
        }
        let kinds = match (&*node, self) {
            (N::Meta { .. }, Self::Logical(_)) => None,
            (N::Meta { id, .. }, _) => match arena.atom_key(*id) {
                Atom::Meta(_, _, kinds) => Some(kinds),
                _ => None,
            },
            _ => None,
        };
        let logical = |e| Self::Logical(Exp(e));
        let value_type = |e| Self::ValueType(ValueType(e));
        let computation_type = |e| Self::ComputationType(ComputationType(e));
        let value = |e| Self::Value(ValueTerm(e));
        let computation = |e| Self::Computation(ComputationTerm(e));
        let mut index = 0;
        let result = arena
            .core
            .map_children(expression, |child, depth| {
                let i = index;
                index += 1;
                let family = match (&*node, self, i) {
                    (N::Meta { .. }, Self::Logical(_), _) => logical,
                    (N::Meta { .. }, _, _) => {
                        if kinds.as_ref().is_none_or(|k| k[i]) {
                            value_type
                        } else {
                            value
                        }
                    }
                    (N::BoxType { .. }, _, _)
                    | (N::BoxProgram { .. } | N::ForceBox { .. }, _, 0) => computation_type,
                    (N::BoxProgram { .. }, _, _) => computation,
                    (N::ForceBox { .. }, _, _) | (_, Self::Logical(_), _) => logical,
                    (N::Ascribe { .. }, Self::Value(_), 0) => value,
                    (N::Ascribe { .. }, Self::Value(_), _) => value_type,
                    (N::Ascribe { .. }, Self::Computation(_), 0) => computation,
                    (N::Ascribe { .. }, Self::Computation(_), _) => computation_type,
                    (N::Thunk { .. }, _, _) => computation_type,
                    (N::ThunkValue { .. }, _, _) => computation,
                    (
                        N::Product { .. }
                        | N::Lambda { .. }
                        | N::Sequence { .. }
                        | N::ValueLet { .. },
                        _,
                        0,
                    ) => value_type,
                    (N::Product { .. }, _, _) => computation_type,
                    (N::Lambda { .. } | N::Sequence { .. }, _, _) => computation,
                    (N::App { .. }, _, 0) => computation,
                    (N::App { .. } | N::Return { .. } | N::Force { .. }, _, _) => value,
                    (N::ReturnType { .. }, _, _) => value_type,
                    (N::ValueLet { .. }, _, 1) => value,
                    (N::ValueLet { .. }, _, _) => computation,
                    (N::ProgramContinue { .. } | N::ProgramFinish { .. }, _, 0 | 1) => value_type,
                    (N::ProgramContinue { .. } | N::ProgramFinish { .. }, _, _) => value,
                    (N::ProgramRunStep { .. } | N::Inductive { .. }, _, _) => value_type,
                    (N::InductiveConstructor { parameters, .. }, _, _) => {
                        if i < parameters.len() {
                            value_type
                        } else {
                            value
                        }
                    }
                    (N::ProgramCase { .. }, _, 0) => value,
                    (N::ProgramCase { .. }, _, _) => computation,
                    (N::ProgramStepMatch { .. } | N::Run { .. } | N::RunCase { .. }, _, 0 | 1) => {
                        value_type
                    }
                    (N::ProgramStepMatch { .. }, _, 2) => computation_type,
                    (N::ProgramStepMatch { .. }, _, 5) => value,
                    (N::ProgramStepMatch { .. }, _, _) => computation,
                    (N::Run { .. } | N::RunCase { .. }, _, 2 | 3) => value,
                    (N::RunCase { .. }, _, 4) => computation,
                    (N::Run { .. } | N::RunCase { .. }, _, _) => logical,
                    _ => unreachable!("source child family: {node:?}"),
                };
                Ok::<_, std::convert::Infallible>(visit(family(child), depth).expression())
            })
            .unwrap();
        self.with_expression(result)
    }

    pub(crate) fn walk(self, arena: &Arena, depth: usize, rewrite: &mut impl Rewrite) -> Term {
        if let Some(result) = rewrite.rewrite(self, depth) {
            return result;
        }
        let result = self.map_children(arena, |term, local_depth| {
            term.walk(arena, depth + local_depth, rewrite)
        });
        rewrite.finish(arena, self, depth, result)
    }

    pub(crate) fn shift(self, arena: &Arena, amount: usize, cutoff: usize) -> Term {
        self.with_expression(
            kernel::calculus::shift(&arena.core, self.expression(), amount, cutoff)
                .expect("valid shift"),
        )
    }
    pub(crate) fn substitute(
        self,
        arena: &Arena,
        substitutions: &[(super::ids::ModuleParamId, ModuleArgument)],
        reflected: &[(super::ids::ModuleParamId, Exp)],
    ) -> Term {
        if substitutions.is_empty() && reflected.is_empty() {
            return self;
        }
        self.walk(
            arena,
            0,
            &mut Memoized::new(|term: Term, depth| {
                let replacement = match term {
                    Term::Logical(e)
                        if matches!(
                            arena.core.get(e.0),
                            kernel::syntax::Node::Definition { .. }
                        ) =>
                    {
                        None
                    }
                    Term::Logical(e) => match arena.get(e) {
                        ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => reflected
                            .iter()
                            .find_map(|(p, e)| (*p == id).then_some(Term::Logical(*e))),
                        _ => None,
                    },
                    Term::ValueType(t) => match arena.get(t) {
                        ValueTypeNode::ModuleParam(id) => {
                            substitutions.iter().find_map(|(p, a)| match a {
                                ModuleArgument::ProgramType(t) if *p == id => {
                                    Some(Term::ValueType(*t))
                                }
                                _ => None,
                            })
                        }
                        _ => None,
                    },
                    Term::Value(v) => match arena.get(v) {
                        ValueTermNode::ModuleParam(id) => {
                            substitutions.iter().find_map(|(p, a)| match a {
                                ModuleArgument::ProgramValue(v) if *p == id => {
                                    Some(Term::Value(*v))
                                }
                                _ => None,
                            })
                        }
                        _ => None,
                    },
                    _ => None,
                };
                replacement.map(|term| term.shift(arena, depth, 0))
            }),
        )
    }
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    fn go(
        arena: &Arena,
        exp: Exp,
        target: usize,
        seen: &mut rustc_hash::FxHashSet<(Exp, usize)>,
    ) -> bool {
        let term = Term::Logical(exp);
        if arena.max_loose_bound(term).is_none_or(|max| max < target) || !seen.insert((exp, target))
        {
            return false;
        }
        if let kernel::syntax::Node::Bound(index) = arena.core.get(exp.0) {
            return index == target;
        }
        let mut found = false;
        term.visit_children(arena, |child, depth| {
            if !found && let Term::Logical(child) = child {
                found = target
                    .checked_add(depth)
                    .is_some_and(|target| go(arena, child, target, seen));
            }
        });
        found
    }
    go(arena, exp, target, &mut rustc_hash::FxHashSet::default())
}

pub fn exp_contains_inductive(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
    let mut pending = vec![exp];
    let mut seen = rustc_hash::FxHashSet::default();
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        let matches = match *arena.borrow_exp(e) {
            ExpNode::IndType { indspec, .. }
            | ExpNode::IndCtor { indspec, .. }
            | ExpNode::IndElim { indspec, .. }
            | ExpNode::IndCase { indspec, .. } => indspec == inductive,
            _ => false,
        };
        if matches {
            return true;
        }
        Term::Logical(e).visit_children(arena, |child, _| {
            if let Term::Logical(e) = child {
                pending.push(e);
            }
        });
    }
    false
}
