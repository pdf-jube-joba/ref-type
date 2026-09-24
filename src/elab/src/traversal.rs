//! Capture-aware traversal across the logical and Program syntax families.
use super::{environment::ModuleArgument, exp::*, program::*};
use rustc_hash::FxHashMap;

pub trait Rewrite {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term>;
    fn remember(&mut self, _term: Term, _depth: usize, _result: Term) {}
}

impl<F: FnMut(Term, usize) -> Option<Term>> Rewrite for F {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term> {
        self(term, depth)
    }
}

/// A transformation must depend only on the node and binder depth for its
/// results to be shared across paths through the same syntax DAG.
pub struct Memoized<F> {
    rewrite: F,
    results: FxHashMap<(Term, usize), Term>,
}

impl<F: FnMut(Term, usize) -> Option<Term>> Memoized<F> {
    pub fn new(rewrite: F) -> Self {
        Self {
            rewrite,
            results: FxHashMap::default(),
        }
    }
}

impl<F: FnMut(Term, usize) -> Option<Term>> Rewrite for Memoized<F> {
    fn rewrite(&mut self, term: Term, depth: usize) -> Option<Term> {
        if let Some(&result) = self.results.get(&(term, depth)) {
            return Some(result);
        }
        let result = (self.rewrite)(term, depth)?;
        if result != term {
            self.remember(term, depth, result);
        }
        Some(result)
    }

    fn remember(&mut self, term: Term, depth: usize, result: Term) {
        self.results.insert((term, depth), result);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Logical(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value(ValueTerm),
    Computation(ComputationTerm),
}

pub fn logical(arena: &Arena, e: Exp, depth: usize, rewrite: &mut impl Rewrite) -> Exp {
    if let Some(Term::Logical(result)) = rewrite.rewrite(Term::Logical(e), depth) {
        return result;
    }
    let result = match arena.get(e) {
        ExpNode::Prod { var, ty, body } => ExpNode::Prod {
            var,
            ty: logical(arena, ty, depth, rewrite),
            body: logical(arena, body, depth + 1, rewrite),
        },
        ExpNode::Lam { var, ty, body } => ExpNode::Lam {
            var,
            ty: logical(arena, ty, depth, rewrite),
            body: logical(arena, body, depth + 1, rewrite),
        },
        ExpNode::SubSet {
            var,
            set,
            predicate,
        } => ExpNode::SubSet {
            var,
            set: logical(arena, set, depth, rewrite),
            predicate: logical(arena, predicate, depth + 1, rewrite),
        },
        ExpNode::Prove(Prove::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        }) => ExpNode::Prove(Prove::IdElim {
            left: logical(arena, left, depth, rewrite),
            right: logical(arena, right, depth, rewrite),
            ty: logical(arena, ty, depth, rewrite),
            var,
            predicate: logical(arena, predicate, depth + 1, rewrite),
            base: logical(arena, base, depth, rewrite),
            equality: logical(arena, equality, depth, rewrite),
        }),
        ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee: logical(arena, scrutinee, depth, rewrite),
            branches: branches
                .into_iter()
                .map(|b| ReflectedProgramCaseBranch {
                    body: logical(arena, b.body, depth + b.binders.len(), rewrite),
                    binders: b.binders,
                })
                .collect(),
        },
        ExpNode::BoxType { program_ty } => ExpNode::BoxType {
            program_ty: computation_type(arena, program_ty, depth, rewrite),
        },
        ExpNode::BoxProgram {
            program_ty,
            program,
        } => ExpNode::BoxProgram {
            program_ty: computation_type(arena, program_ty, depth, rewrite),
            program: computation(arena, program, depth, rewrite),
        },
        ExpNode::ForceBox { program_ty, boxed } => ExpNode::ForceBox {
            program_ty: computation_type(arena, program_ty, depth, rewrite),
            boxed: logical(arena, boxed, depth, rewrite),
        },
        other => super::calculus::map_children(other, |e| logical(arena, e, depth, rewrite)),
    };
    let result = arena.reuse_exp(e, result);
    rewrite.remember(Term::Logical(e), depth, Term::Logical(result));
    result
}

fn program_argument(
    arena: &Arena,
    a: ProgramArgument,
    depth: usize,
    rewrite: &mut impl Rewrite,
) -> ProgramArgument {
    match a {
        ProgramArgument::ValueType(t) => {
            ProgramArgument::ValueType(value_type(arena, t, depth, rewrite))
        }
        ProgramArgument::ValueTerm(v) => {
            ProgramArgument::ValueTerm(value(arena, v, depth, rewrite))
        }
    }
}

pub fn value_type(
    arena: &Arena,
    t: ValueType,
    depth: usize,
    rewrite: &mut impl Rewrite,
) -> ValueType {
    if let Some(Term::ValueType(result)) = rewrite.rewrite(Term::ValueType(t), depth) {
        return result;
    }
    let result = match arena.get(t) {
        ValueTypeNode::Meta {
            metavariable,
            spine,
        } => ValueTypeNode::Meta {
            metavariable,
            spine: spine
                .into_iter()
                .map(|a| program_argument(arena, a, depth, rewrite))
                .collect(),
        },
        ValueTypeNode::Thunk { computation_ty } => ValueTypeNode::Thunk {
            computation_ty: computation_type(arena, computation_ty, depth, rewrite),
        },
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => ValueTypeNode::RunStep {
            state_ty: value_type(arena, state_ty, depth, rewrite),
            result_ty: value_type(arena, result_ty, depth, rewrite),
        },
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => ValueTypeNode::Inductive {
            indspec,
            parameters: parameters
                .into_iter()
                .map(|t| value_type(arena, t, depth, rewrite))
                .collect(),
        },
        other => other,
    };
    let result = arena.reuse_value_type(t, result);
    rewrite.remember(Term::ValueType(t), depth, Term::ValueType(result));
    result
}

pub fn computation_type(
    arena: &Arena,
    t: ComputationType,
    depth: usize,
    rewrite: &mut impl Rewrite,
) -> ComputationType {
    if let Some(Term::ComputationType(result)) = rewrite.rewrite(Term::ComputationType(t), depth) {
        return result;
    }
    let result = match arena.get(t) {
        ComputationTypeNode::Meta {
            metavariable,
            spine,
        } => ComputationTypeNode::Meta {
            metavariable,
            spine: spine
                .into_iter()
                .map(|a| program_argument(arena, a, depth, rewrite))
                .collect(),
        },
        ComputationTypeNode::Return { value_ty } => ComputationTypeNode::Return {
            value_ty: value_type(arena, value_ty, depth, rewrite),
        },
        ComputationTypeNode::Function { domain, codomain } => ComputationTypeNode::Function {
            domain: value_type(arena, domain, depth, rewrite),
            codomain: computation_type(arena, codomain, depth, rewrite),
        },
    };
    let result = arena.reuse_computation_type(t, result);
    rewrite.remember(
        Term::ComputationType(t),
        depth,
        Term::ComputationType(result),
    );
    result
}

pub fn value(arena: &Arena, v: ValueTerm, depth: usize, rewrite: &mut impl Rewrite) -> ValueTerm {
    if let Some(Term::Value(result)) = rewrite.rewrite(Term::Value(v), depth) {
        return result;
    }
    let result = match arena.get(v) {
        ValueTermNode::Meta {
            metavariable,
            spine,
        } => ValueTermNode::Meta {
            metavariable,
            spine: spine
                .into_iter()
                .map(|a| program_argument(arena, a, depth, rewrite))
                .collect(),
        },
        ValueTermNode::DefinitionInstance {
            definition,
            parameters,
        } => ValueTermNode::DefinitionInstance {
            definition,
            parameters: parameters
                .into_iter()
                .map(|t| value_type(arena, t, depth, rewrite))
                .collect(),
        },
        ValueTermNode::Thunk { computation: c } => ValueTermNode::Thunk {
            computation: computation(arena, c, depth, rewrite),
        },
        ValueTermNode::Continue {
            state_ty,
            result_ty,
            next,
        } => ValueTermNode::Continue {
            state_ty: value_type(arena, state_ty, depth, rewrite),
            result_ty: value_type(arena, result_ty, depth, rewrite),
            next: value(arena, next, depth, rewrite),
        },
        ValueTermNode::Finish {
            state_ty,
            result_ty,
            output,
        } => ValueTermNode::Finish {
            state_ty: value_type(arena, state_ty, depth, rewrite),
            result_ty: value_type(arena, result_ty, depth, rewrite),
            output: value(arena, output, depth, rewrite),
        },
        ValueTermNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => ValueTermNode::InductiveConstructor {
            indspec,
            parameters: parameters
                .into_iter()
                .map(|t| value_type(arena, t, depth, rewrite))
                .collect(),
            idx,
            fields: fields
                .into_iter()
                .map(|v| value(arena, v, depth, rewrite))
                .collect(),
        },
        other => other,
    };
    let result = arena.reuse_value(v, result);
    rewrite.remember(Term::Value(v), depth, Term::Value(result));
    result
}

pub fn computation(
    arena: &Arena,
    c: ComputationTerm,
    depth: usize,
    rewrite: &mut impl Rewrite,
) -> ComputationTerm {
    if let Some(Term::Computation(result)) = rewrite.rewrite(Term::Computation(c), depth) {
        return result;
    }
    let result = match arena.get(c) {
        ComputationTermNode::Meta {
            metavariable,
            spine,
        } => ComputationTermNode::Meta {
            metavariable,
            spine: spine
                .into_iter()
                .map(|a| program_argument(arena, a, depth, rewrite))
                .collect(),
        },
        ComputationTermNode::DefinitionInstance {
            definition,
            parameters,
        } => ComputationTermNode::DefinitionInstance {
            definition,
            parameters: parameters
                .into_iter()
                .map(|t| value_type(arena, t, depth, rewrite))
                .collect(),
        },
        ComputationTermNode::Return { value: v } => ComputationTermNode::Return {
            value: value(arena, v, depth, rewrite),
        },
        ComputationTermNode::Force { value: v } => ComputationTermNode::Force {
            value: value(arena, v, depth, rewrite),
        },
        ComputationTermNode::Lambda {
            var,
            value_ty,
            body,
        } => ComputationTermNode::Lambda {
            var,
            value_ty: value_type(arena, value_ty, depth, rewrite),
            body: computation(arena, body, depth + 1, rewrite),
        },
        ComputationTermNode::Application {
            computation: f,
            value: v,
        } => ComputationTermNode::Application {
            computation: computation(arena, f, depth, rewrite),
            value: value(arena, v, depth, rewrite),
        },
        ComputationTermNode::Sequence {
            computation: first,
            var,
            value_ty,
            body,
        } => ComputationTermNode::Sequence {
            computation: computation(arena, first, depth, rewrite),
            var,
            value_ty: value_type(arena, value_ty, depth, rewrite),
            body: computation(arena, body, depth + 1, rewrite),
        },
        ComputationTermNode::ValueLet {
            var,
            value_ty,
            value: v,
            body,
        } => ComputationTermNode::ValueLet {
            var,
            value_ty: value_type(arena, value_ty, depth, rewrite),
            value: value(arena, v, depth, rewrite),
            body: computation(arena, body, depth + 1, rewrite),
        },
        ComputationTermNode::Case {
            indspec,
            scrutinee,
            branches,
        } => ComputationTermNode::Case {
            indspec,
            scrutinee: value(arena, scrutinee, depth, rewrite),
            branches: branches
                .into_iter()
                .map(|b| ProgramCaseBranch {
                    body: computation(arena, b.body, depth + b.binders.len(), rewrite),
                    binders: b.binders,
                })
                .collect(),
        },
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => ComputationTermNode::Run {
            state_ty: value_type(arena, state_ty, depth, rewrite),
            result_ty: value_type(arena, result_ty, depth, rewrite),
            step: value(arena, step, depth, rewrite),
            initial: value(arena, initial, depth, rewrite),
            accessibility: logical(arena, accessibility, depth, rewrite),
        },
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => ComputationTermNode::RunCase {
            state_ty: value_type(arena, state_ty, depth, rewrite),
            result_ty: value_type(arena, result_ty, depth, rewrite),
            step: value(arena, step, depth, rewrite),
            initial: value(arena, initial, depth, rewrite),
            transition: computation(arena, transition, depth, rewrite),
            accessibility: logical(arena, accessibility, depth, rewrite),
            transition_equality: logical(arena, transition_equality, depth, rewrite),
        },
        other => other,
    };
    let result = arena.reuse_computation(c, result);
    rewrite.remember(Term::Computation(c), depth, Term::Computation(result));
    result
}

impl Term {
    /// Visit immediate children with their local binder depths.
    pub fn visit_children(self, arena: &Arena, mut visit: impl FnMut(Term, usize)) {
        let mut root = true;
        self.walk(arena, 0, &mut |term, depth| {
            if std::mem::take(&mut root) {
                return None;
            }
            visit(term, depth);
            Some(term)
        });
    }

    pub fn bound_index(self, arena: &Arena) -> Option<usize> {
        match self {
            Term::Logical(e) => match *arena.borrow_exp(e) {
                ExpNode::Bound(index) => Some(index),
                _ => None,
            },
            Term::ValueType(t) => match *arena.borrow_value_type(t) {
                ValueTypeNode::Bound(index) => Some(index),
                _ => None,
            },
            Term::Value(v) => match *arena.borrow_value(v) {
                ValueTermNode::Bound(index) => Some(index),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn walk(self, arena: &Arena, depth: usize, rewrite: &mut impl Rewrite) -> Term {
        match self {
            Term::Logical(e) => Term::Logical(logical(arena, e, depth, rewrite)),
            Term::ValueType(t) => Term::ValueType(value_type(arena, t, depth, rewrite)),
            Term::ComputationType(t) => {
                Term::ComputationType(computation_type(arena, t, depth, rewrite))
            }
            Term::Value(v) => Term::Value(value(arena, v, depth, rewrite)),
            Term::Computation(c) => Term::Computation(computation(arena, c, depth, rewrite)),
        }
    }
    pub fn shift(self, arena: &Arena, amount: usize, cutoff: usize) -> Term {
        if amount == 0 {
            return self;
        }
        self.walk(
            arena,
            0,
            &mut Memoized::new(|term: Term, depth| {
                if arena
                    .max_loose_bound(term)
                    .is_none_or(|index| index < cutoff + depth)
                {
                    return Some(term);
                }
                let index = term.bound_index(arena)?;
                if index < cutoff + depth {
                    return Some(term);
                }
                Some(match term {
                    Term::Logical(_) => Term::Logical(arena.exp_bound(index + amount)),
                    Term::ValueType(_) => Term::ValueType(arena.value_type_bound(index + amount)),
                    Term::Value(_) => Term::Value(arena.value_bound(index + amount)),
                    _ => unreachable!(),
                })
            }),
        )
    }
    pub fn substitute(
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
