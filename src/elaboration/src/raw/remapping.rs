//! Global name remapping over the shared logical and Program traversal.
use super::{
    exp::{Arena, ExpNode},
    ids::{DefId, InductiveId, ProgramInductiveId},
    program::{ComputationTermNode, ValueTermNode, ValueTypeNode},
    traversal::{Memoized, Rewrite, Term},
};
use std::collections::HashMap;

struct Remapping<'a> {
    definitions: &'a HashMap<DefId, DefId>,
    inductives: &'a HashMap<InductiveId, InductiveId>,
    program_inductives: &'a HashMap<ProgramInductiveId, ProgramInductiveId>,
}

impl Rewrite for Remapping<'_> {
    fn rewrite(&mut self, _term: Term, _depth: usize) -> Option<Term> {
        None
    }

    fn finish(&mut self, arena: &Arena, _term: Term, _depth: usize, result: Term) -> Term {
        match result {
            Term::Logical(e) => {
                let mut node = arena.get(e);
                match &mut node {
                    ExpNode::DefinedConstant(id) => {
                        *id = self.definitions.get(id).copied().unwrap_or(*id);
                    }
                    ExpNode::IndType { indspec, .. }
                    | ExpNode::IndCtor { indspec, .. }
                    | ExpNode::IndElim { indspec, .. }
                    | ExpNode::IndCase { indspec, .. } => {
                        *indspec = self.inductives.get(indspec).copied().unwrap_or(*indspec);
                    }
                    ExpNode::ReflectedProgramCase { indspec, .. } => {
                        *indspec = self
                            .program_inductives
                            .get(indspec)
                            .copied()
                            .unwrap_or(*indspec);
                    }
                    _ => return result,
                }
                Term::Logical(arena.reuse_exp(e, node))
            }
            Term::ValueType(t) => {
                let ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                } = arena.get(t)
                else {
                    return result;
                };
                Term::ValueType(
                    arena.reuse_value_type(
                        t,
                        ValueTypeNode::Inductive {
                            indspec: self
                                .program_inductives
                                .get(&indspec)
                                .copied()
                                .unwrap_or(indspec),
                            parameters,
                        },
                    ),
                )
            }
            Term::Value(v) => {
                let mut node = arena.get(v);
                match &mut node {
                    ValueTermNode::DefinedConstant(id)
                    | ValueTermNode::DefinitionInstance { definition: id, .. } => {
                        *id = self.definitions.get(id).copied().unwrap_or(*id);
                    }
                    ValueTermNode::InductiveConstructor { indspec, .. } => {
                        *indspec = self
                            .program_inductives
                            .get(indspec)
                            .copied()
                            .unwrap_or(*indspec);
                    }
                    _ => return result,
                }
                Term::Value(arena.reuse_value(v, node))
            }
            Term::Computation(c) => {
                let mut node = arena.get(c);
                match &mut node {
                    ComputationTermNode::DefinedConstant(id)
                    | ComputationTermNode::DefinitionInstance { definition: id, .. } => {
                        *id = self.definitions.get(id).copied().unwrap_or(*id);
                    }
                    ComputationTermNode::Case { indspec, .. } => {
                        *indspec = self
                            .program_inductives
                            .get(indspec)
                            .copied()
                            .unwrap_or(*indspec);
                    }
                    _ => return result,
                }
                Term::Computation(arena.reuse_computation(c, node))
            }
            Term::ComputationType(_) => result,
        }
    }
}

pub(crate) fn remap(
    arena: &Arena,
    term: Term,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Term {
    if definitions.is_empty() && inductives.is_empty() && program_inductives.is_empty() {
        return term;
    }
    term.walk(
        arena,
        0,
        &mut Memoized::new(Remapping {
            definitions,
            inductives,
            program_inductives,
        }),
    )
}
