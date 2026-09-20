//! Capture-aware traversal across the logical and Program syntax families.
use super::{environment::ModuleArgument, exp::*, program::*};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Term {
    Logical(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value(ValueTerm),
    Computation(ComputationTerm),
}

pub(crate) fn logical(
    arena: &Arena,
    e: Exp,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
) -> Exp {
    if let Some(Term::Logical(result)) = rewrite(Term::Logical(e.clone()), depth) {
        return result;
    }
    let result = match arena.get(e.clone()) {
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
    arena.reuse_exp(e, result)
}

fn program_argument(
    arena: &Arena,
    a: ProgramArgument,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
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

pub(crate) fn value_type(
    arena: &Arena,
    t: ValueType,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
) -> ValueType {
    if let Some(Term::ValueType(result)) = rewrite(Term::ValueType(t.clone()), depth) {
        return result;
    }
    let result = match arena.get(t.clone()) {
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
    arena.reuse_value_type(t, result)
}

pub(crate) fn computation_type(
    arena: &Arena,
    t: ComputationType,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
) -> ComputationType {
    if let Some(Term::ComputationType(result)) = rewrite(Term::ComputationType(t.clone()), depth) {
        return result;
    }
    let result = match arena.get(t.clone()) {
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
    arena.reuse_computation_type(t, result)
}

pub(crate) fn value(
    arena: &Arena,
    v: ValueTerm,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
) -> ValueTerm {
    if let Some(Term::Value(result)) = rewrite(Term::Value(v.clone()), depth) {
        return result;
    }
    let result = match arena.get(v.clone()) {
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
    arena.reuse_value(v, result)
}

pub(crate) fn computation(
    arena: &Arena,
    c: ComputationTerm,
    depth: usize,
    rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
) -> ComputationTerm {
    if let Some(Term::Computation(result)) = rewrite(Term::Computation(c.clone()), depth) {
        return result;
    }
    let result = match arena.get(c.clone()) {
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
    arena.reuse_computation(c, result)
}

impl Term {
    pub(crate) fn bound_index(self, arena: &Arena) -> Option<usize> {
        match self {
            Term::Logical(e) => match arena.get(e) {
                ExpNode::Bound(index) => Some(index),
                _ => None,
            },
            Term::ValueType(t) => match arena.borrow_value_type(t) {
                ValueTypeNode::Bound(index) => Some(index),
                _ => None,
            },
            Term::Value(v) => match arena.borrow_value(v) {
                ValueTermNode::Bound(index) => Some(index),
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn walk(
        self,
        arena: &Arena,
        depth: usize,
        rewrite: &mut impl FnMut(Term, usize) -> Option<Term>,
    ) -> Term {
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
    pub(crate) fn shift(self, arena: &Arena, amount: usize, cutoff: usize) -> Term {
        if amount == 0 {
            return self;
        }
        self.walk(arena, 0, &mut |term, depth| {
            let index = term.clone().bound_index(arena)?;
            if index < cutoff + depth {
                return Some(term);
            }
            Some(match term {
                Term::Logical(_) => Term::Logical(arena.exp_bound(index + amount)),
                Term::ValueType(_) => Term::ValueType(arena.value_type_bound(index + amount)),
                Term::Value(_) => Term::Value(arena.value_bound(index + amount)),
                _ => unreachable!(),
            })
        })
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
        self.walk(arena, 0, &mut |term, depth| {
            let replacement = match term {
                Term::Logical(e) => match arena.get(e) {
                    ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => reflected
                        .iter()
                        .find_map(|(p, e)| (*p == id).then_some(Term::Logical(e.clone()))),
                    _ => None,
                },
                Term::ValueType(t) => match arena.get(t) {
                    ValueTypeNode::ModuleParam(id) => {
                        substitutions.iter().find_map(|(p, a)| match a {
                            ModuleArgument::ProgramType(t) if *p == id => {
                                Some(Term::ValueType(t.clone()))
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
                                Some(Term::Value(v.clone()))
                            }
                            _ => None,
                        })
                    }
                    _ => None,
                },
                _ => None,
            };
            replacement.map(|term| term.shift(arena, depth, 0))
        })
    }
}
