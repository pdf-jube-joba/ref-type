//! Global references needed to materialize and independently check a definition.
use crate::raw::{
    self,
    exp::{Exp, ExpNode},
    ids::{DefId, InductiveId, ProgramInductiveId},
};
use std::collections::HashSet;

pub(crate) struct GlobalDependencies {
    pub definitions: Vec<DefId>,
    #[allow(dead_code)]
    pub inductives: HashSet<InductiveId>,
    #[allow(dead_code)]
    pub datatypes: HashSet<ProgramInductiveId>,
}

// Materialized modules need not store declarations in dependency order. Schedule
// the dependency graph explicitly so a long import chain does not consume the
// Rust call stack while classifying syntax.
pub(crate) fn definition_dependencies(
    raw: &raw::environment::CrateEnv,
    definition: &raw::environment::DefinedConstant,
) -> GlobalDependencies {
    use raw::program::{
        ComputationTermNode as C, ComputationTypeNode as CT, ValueTermNode as V,
        ValueTypeNode as VT,
    };
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum E {
        Set(Exp),
        Vt(raw::program::ValueType),
        Ct(raw::program::ComputationType),
        V(raw::program::ValueTerm),
        C(raw::program::ComputationTerm),
    }

    fn ty(t: raw::program::ProgramType) -> E {
        match t {
            raw::program::ProgramType::ValueType(x) => E::Vt(x),
            raw::program::ProgramType::ComputationType(x) => E::Ct(x),
        }
    }

    fn term(t: raw::program::ProgramTerm) -> E {
        match t {
            raw::program::ProgramTerm::ValueTerm(x) => E::V(x),
            raw::program::ProgramTerm::ComputationTerm(x) => E::C(x),
        }
    }
    let mut stack = match definition {
        raw::environment::DefinedConstant::Pts { ty, body } => vec![E::Set(*ty), E::Set(*body)],
        raw::environment::DefinedConstant::ProgramValue {
            ty,
            body,
            certified_reflection,
        } => {
            let mut s = vec![E::Vt(*ty), E::V(*body)];
            s.extend(certified_reflection.map(E::Set));
            s
        }
        raw::environment::DefinedConstant::ProgramComputation {
            ty,
            body,
            certified_reflection,
        } => {
            let mut s = vec![E::Ct(*ty), E::C(*body)];
            s.extend(certified_reflection.map(E::Set));
            s
        }
    };
    let mut visited = HashSet::new();
    let mut definitions = HashSet::new();
    let mut inductives = HashSet::new();
    let mut datatypes = HashSet::new();
    while let Some(e) = stack.pop() {
        if !visited.insert(e) {
            continue;
        }
        match e {
            E::Set(x) => {
                let node = raw.arena().get(x);
                match &node {
                    ExpNode::IndType { indspec, .. }
                    | ExpNode::IndCtor { indspec, .. }
                    | ExpNode::IndElim { indspec, .. } => {
                        inductives.insert(*indspec);
                    }
                    ExpNode::ReflectedProgramCase { indspec, .. } => {
                        datatypes.insert(*indspec);
                    }
                    ExpNode::DefinedConstant(id) => {
                        definitions.insert(*id);
                    }
                    ExpNode::BoxType { program_ty } | ExpNode::ForceBox { program_ty, .. } => {
                        stack.push(ty(*program_ty))
                    }
                    ExpNode::BoxProgram {
                        program_ty,
                        program,
                        ..
                    } => {
                        stack.push(ty(*program_ty));
                        stack.push(term(*program));
                    }
                    _ => {}
                }
                raw::calculus::map_children(node, |e| {
                    stack.push(E::Set(e));
                    e
                });
            }
            E::Vt(x) => match raw.arena().get(x) {
                VT::Thunk { computation_ty } => stack.push(E::Ct(computation_ty)),
                VT::RunStep {
                    state_ty,
                    result_ty,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty)]),
                VT::Inductive {
                    indspec,
                    parameters,
                } => {
                    datatypes.insert(indspec);
                    stack.extend(parameters.into_iter().map(E::Vt));
                }
                _ => {}
            },
            E::Ct(x) => match raw.arena().get(x) {
                CT::Return { value_ty } => stack.push(E::Vt(value_ty)),
                CT::Function { domain, codomain } => stack.extend([E::Vt(domain), E::Ct(codomain)]),
                _ => {}
            },
            E::V(x) => match raw.arena().get(x) {
                V::DefinitionInstance {
                    definition,
                    parameters,
                } => {
                    definitions.insert(definition);
                    stack.extend(parameters.into_iter().map(E::Vt));
                }
                V::DefinedConstant(id) => {
                    definitions.insert(id);
                }
                V::Thunk { computation } => stack.push(E::C(computation)),
                V::Continue {
                    state_ty,
                    result_ty,
                    next,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(next)]),
                V::Finish {
                    state_ty,
                    result_ty,
                    output,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(output)]),
                V::InductiveConstructor {
                    indspec,
                    parameters,
                    fields,
                    ..
                } => {
                    datatypes.insert(indspec);
                    stack.extend(parameters.into_iter().map(E::Vt));
                    stack.extend(fields.into_iter().map(E::V));
                }
                _ => {}
            },
            E::C(x) => match raw.arena().get(x) {
                C::DefinitionInstance {
                    definition,
                    parameters,
                } => {
                    definitions.insert(definition);
                    stack.extend(parameters.into_iter().map(E::Vt));
                }
                C::DefinedConstant(id) => {
                    definitions.insert(id);
                }
                C::Return { value } | C::Force { value } => stack.push(E::V(value)),
                C::Lambda { value_ty, body, .. } => stack.extend([E::Vt(value_ty), E::C(body)]),
                C::Application { computation, value } => {
                    stack.extend([E::C(computation), E::V(value)])
                }
                C::Sequence {
                    value_ty,
                    computation,
                    body,
                    ..
                } => stack.extend([E::Vt(value_ty), E::C(computation), E::C(body)]),
                C::ValueLet {
                    value_ty,
                    value,
                    body,
                    ..
                } => stack.extend([E::Vt(value_ty), E::V(value), E::C(body)]),
                C::Case {
                    indspec,
                    scrutinee,
                    branches,
                    ..
                } => {
                    datatypes.insert(indspec);
                    stack.push(E::V(scrutinee));
                    stack.extend(branches.into_iter().map(|b| E::C(b.body)));
                }
                C::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(step), E::V(initial)]),
                C::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                } => stack.extend([
                    E::Vt(state_ty),
                    E::Vt(result_ty),
                    E::V(step),
                    E::V(initial),
                    E::C(transition),
                ]),
                _ => {}
            },
        }
    }
    let mut definitions = definitions.into_iter().collect::<Vec<_>>();
    definitions.sort_by_key(|id| (id.module.0, id.index));
    GlobalDependencies {
        definitions,
        inductives,
        datatypes,
    }
}
