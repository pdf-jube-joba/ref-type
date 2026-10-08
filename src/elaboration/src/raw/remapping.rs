//! Global name remapping over the shared logical and Program traversal.
use super::environment::ModuleArgument;
use super::{
    exp::{Arena, Exp, ExpNode},
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId},
    program::*,
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
                if matches!(arena.core.get(e.0), kernel::syntax::Node::Definition { .. }) {
                    return result;
                }
                let mut node = arena.get(e);
                match &mut node {
                    ExpNode::DefinedConstant(id)
                    | ExpNode::DefinitionInstance { definition: id, .. } => {
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

pub fn exp_subst_map(arena: &Arena, exp: Exp, substitutions: &[(ModuleParamId, Exp)]) -> Exp {
    let Term::Logical(e) = Term::Logical(exp).substitute(arena, &[], substitutions) else {
        unreachable!()
    };
    e
}

pub fn remap_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
) -> Exp {
    remap_all_global_ids(arena, exp, definitions, inductives, &HashMap::new())
}

pub fn remap_all_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Exp {
    let Term::Logical(result) = remap(
        arena,
        Term::Logical(exp),
        definitions,
        inductives,
        program_inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_value_type_global_ids(
    arena: &Arena,
    term: ValueType,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ValueType {
    let Term::ValueType(result) = remap(
        arena,
        Term::ValueType(term),
        definitions,
        &HashMap::new(),
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_computation_type_global_ids(
    arena: &Arena,
    term: ComputationType,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ComputationType {
    let Term::ComputationType(result) = remap(
        arena,
        Term::ComputationType(term),
        definitions,
        &HashMap::new(),
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_value_global_ids(
    arena: &Arena,
    term: ValueTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ValueTerm {
    let Term::Value(result) = remap(
        arena,
        Term::Value(term),
        definitions,
        logical_inductives,
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_computation_global_ids(
    arena: &Arena,
    term: ComputationTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ComputationTerm {
    let Term::Computation(result) = remap(
        arena,
        Term::Computation(term),
        definitions,
        logical_inductives,
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn subst_value_type_module_params(
    arena: &Arena,
    ty: ValueType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ValueType {
    let Term::ValueType(result) = Term::ValueType(ty).substitute(arena, substitutions, &[]) else {
        unreachable!()
    };
    result
}

pub fn subst_computation_type_module_params(
    arena: &Arena,
    ty: ComputationType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ComputationType {
    let Term::ComputationType(result) =
        Term::ComputationType(ty).substitute(arena, substitutions, &[])
    else {
        unreachable!()
    };
    result
}

pub fn subst_value_module_params(
    arena: &Arena,
    value: ValueTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
    reflected_substitutions: &[(ModuleParamId, crate::raw::exp::Exp)],
) -> ValueTerm {
    let Term::Value(result) =
        Term::Value(value).substitute(arena, substitutions, reflected_substitutions)
    else {
        unreachable!()
    };
    result
}

pub fn subst_computation_module_params(
    arena: &Arena,
    term: ComputationTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
    reflected_substitutions: &[(ModuleParamId, crate::raw::exp::Exp)],
) -> ComputationTerm {
    let Term::Computation(result) =
        Term::Computation(term).substitute(arena, substitutions, reflected_substitutions)
    else {
        unreachable!()
    };
    result
}
