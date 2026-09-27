//! Source reference resolution for the common kernel reflection operation.
use crate::raw::{
    environment::{CrateEnv, DefinedConstant},
    exp::{Atom, Exp, ExpContext, ExpContextEntry},
    program::*,
};
use kernel::{
    reflection::{Reflection, Resolver},
    syntax::{Expression, Node},
};
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectionError {
    UnresolvedMetavariable,
    Invalid(String),
}
impl std::fmt::Display for ReflectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnresolvedMetavariable => {
                f.write_str("cannot reflect an unresolved metavariable")
            }
            Self::Invalid(message) => f.write_str(message),
        }
    }
}
impl std::error::Error for ReflectionError {}
struct Source<'a>(&'a CrateEnv);
impl Resolver for Source<'_> {
    fn arena(&self) -> &kernel::syntax::Arena {
        &self.0.arena().core
    }
    fn replacement(&self, term: Expression) -> Result<Option<Expression>, String> {
        let arena = self.0.arena();
        match arena.core.get(term) {
            Node::Definition { id, arguments } => {
                kernel::calculus::instantiate(&arena.core, arena.definition_body(id), &arguments)
                    .map(Some)
            }
            Node::Meta { id, arguments } => {
                let definition = match arena.atom_key(id) {
                    Atom::Definition(id) | Atom::Instance(id) => id,
                    Atom::Meta(..) => return Err("unresolved reflection metavariable".into()),
                };
                let body = match self.0.resolve_definition(definition)? {
                    DefinedConstant::ProgramValue { body, .. } => body.0,
                    DefinedConstant::ProgramComputation { body, .. } => body.0,
                    _ => return Err("reflection requires a Program definition".into()),
                };
                kernel::calculus::instantiate(&arena.core, body, &arguments).map(Some)
            }
            _ => Ok(None),
        }
    }
    fn definition(
        &self,
        _id: kernel::ids::DefinitionId,
    ) -> Result<(kernel::ids::DefinitionId, Vec<bool>), String> {
        Err("source definition was not resolved".into())
    }
    fn datatype(
        &self,
        id: kernel::ids::ProgramInductiveId,
    ) -> Result<kernel::ids::InductiveId, String> {
        let source = crate::raw::ids::ProgramInductiveId {
            module: crate::raw::ids::ModuleId((id.0 >> 32) as u32),
            index: id.0 as u32,
        };
        Ok(self.0.program_inductive(source).reflected().into())
    }
}
fn reflect(env: &CrateEnv, term: Expression) -> Result<Exp, ReflectionError> {
    Reflection::new(&Source(env))
        .reflect_bound(term)
        .map(Exp)
        .map_err(|e| {
            if e == "unresolved reflection metavariable" {
                ReflectionError::UnresolvedMetavariable
            } else {
                ReflectionError::Invalid(e)
            }
        })
}
pub fn reflect_value_type(env: &CrateEnv, ty: ValueType) -> Result<Exp, ReflectionError> {
    reflect(env, ty.0)
}
#[cfg(test)]
pub fn reflect_computation_type(
    env: &CrateEnv,
    ty: ComputationType,
) -> Result<Exp, ReflectionError> {
    reflect(env, ty.0)
}
pub fn reflect_value(env: &CrateEnv, term: ValueTerm) -> Result<Exp, ReflectionError> {
    reflect(env, term.0)
}
pub fn reflect_computation(env: &CrateEnv, term: ComputationTerm) -> Result<Exp, ReflectionError> {
    reflect(env, term.0)
}
pub fn reflect_program(env: &CrateEnv, term: ProgramTerm) -> Result<Exp, ReflectionError> {
    match term {
        ProgramTerm::ValueTerm(e) => reflect_value(env, e),
        ProgramTerm::ComputationTerm(e) => reflect_computation(env, e),
    }
}
pub fn reflect_context(
    env: &CrateEnv,
    context: &ProgramContext,
) -> Result<ExpContext, ReflectionError> {
    let mut result = Vec::with_capacity(context.len());
    for entry in context {
        match *entry {
            ProgramContextEntry::ValueType { var } => result.push(ExpContextEntry {
                var,
                ty: env.arena().sort(crate::raw::sort::Sort::Set(0)),
            }),
            ProgramContextEntry::ValueTerm { var, ty } => result.push(ExpContextEntry {
                var,
                ty: reflect_value_type(env, ty)?,
            }),
        }
    }
    Ok(result)
}
