//! Elaboration for the four disjoint Program syntactic categories.

use crate::{
    elaborator::{GlobalEnvironment, module_manager::ItemAccessResult},
    syntax::{ComputationExp, ComputationTypeExp, LocalAccess, ValueExp, ValueTypeExp},
};
use kernel::{
    environment::DefinedConstant,
    ids::SymbolId,
    program::{
        Computation, ComputationNode, ComputationType, ComputationTypeNode, ProgramContext,
        ProgramContextEntry, Value, ValueNode, ValueType, ValueTypeNode,
    },
    program_derivation::ProgramCheckSession,
};

#[derive(Debug, Clone)]
pub struct ProgramScope {
    names: Vec<SymbolId>,
    context: ProgramContext,
    value_type_bindings: Vec<(SymbolId, ValueType)>,
}

impl ProgramScope {
    pub fn from_environment(environment: &GlobalEnvironment) -> Self {
        let context = environment
            .module_manager
            .current_program_context(&environment.crate_env);
        let names = context
            .iter()
            .map(|entry| match entry {
                ProgramContextEntry::Type { var } | ProgramContextEntry::Value { var, .. } => *var,
            })
            .collect();
        Self {
            names,
            context,
            value_type_bindings: Vec::new(),
        }
    }

    pub fn context(&self) -> &ProgramContext {
        &self.context
    }

    pub fn bind_value_type_name(&mut self, name: SymbolId, ty: ValueType) {
        self.value_type_bindings.push((name, ty));
    }

    pub fn push_type(&mut self, var: SymbolId) {
        self.names.push(var);
        self.context.push(ProgramContextEntry::Type { var });
    }

    pub fn push_value(&mut self, var: SymbolId, ty: ValueType) {
        self.names.push(var);
        self.context.push(ProgramContextEntry::Value { var, ty });
    }

    pub fn truncate(&mut self, len: usize) {
        self.names.truncate(len);
        self.context.truncate(len);
    }

    fn local_index(
        &self,
        environment: &GlobalEnvironment,
        access: &LocalAccess,
    ) -> Option<(usize, ProgramContextEntry)> {
        let LocalAccess::Current { access } = access else {
            return None;
        };
        self.names
            .iter()
            .rev()
            .enumerate()
            .find_map(|(index, symbol)| {
                (environment.crate_env.symbol(*symbol) == access.as_str())
                    .then(|| (index, self.context[self.context.len() - index - 1].clone()))
            })
    }

    fn item(
        &self,
        environment: &GlobalEnvironment,
        access: &LocalAccess,
    ) -> Result<ItemAccessResult, String> {
        environment
            .module_manager
            .get_item(&environment.crate_env, access)
            .ok_or_else(|| format!("Program name was not found: {access:?}"))
    }

    pub fn elaborate_value_type(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueType, String> {
        match expression {
            ValueTypeExp::Access { access, parameters } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.elaborate_value_type(parameter, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                let arena = environment.crate_env.arena();
                if let LocalAccess::Current { access: name } = access
                    && let Some((_, ty)) =
                        self.value_type_bindings.iter().rev().find(|(symbol, _)| {
                            environment.crate_env.symbol(*symbol) == name.as_str()
                        })
                {
                    if parameters.is_empty() {
                        return Ok(*ty);
                    }
                    let ValueTypeNode::Inductive { indspec, .. } = arena.get(*ty) else {
                        return Err("only Program datatypes accept type parameters".into());
                    };
                    return Ok(arena.alloc(ValueTypeNode::Inductive {
                        indspec,
                        parameters,
                    }));
                }
                if let Some((index, entry)) = self.local_index(environment, access) {
                    if !parameters.is_empty() {
                        return Err("Program type variables do not accept parameters".into());
                    }
                    return match entry {
                        ProgramContextEntry::Type { .. } => Ok(arena.value_type_bound(index)),
                        ProgramContextEntry::Value { .. } => {
                            Err("Program value used as a value type".into())
                        }
                    };
                }
                match self.item(environment, access)? {
                    ItemAccessResult::ProgramTypeParameter(id) => {
                        if !parameters.is_empty() {
                            return Err(
                                "Program type module parameters do not accept parameters".into()
                            );
                        }
                        Ok(arena.value_type_module_param(id))
                    }
                    ItemAccessResult::ProgramInductive(item) => {
                        Ok(arena.alloc(ValueTypeNode::Inductive {
                            indspec: item.inductive,
                            parameters,
                        }))
                    }
                    _ => Err("name does not denote a Program value type".into()),
                }
            }
            ValueTypeExp::Thunk(computation_ty) => {
                let computation_ty =
                    self.elaborate_computation_type(computation_ty, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTypeNode::Thunk { computation_ty }))
            }
            ValueTypeExp::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                Ok(environment.crate_env.arena().alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
        }
    }

    pub fn elaborate_computation_type(
        &mut self,
        expression: &ComputationTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationType, String> {
        match expression {
            ComputationTypeExp::Return(value_ty) => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTypeNode::Return { value_ty }))
            }
            ComputationTypeExp::Function { domain, codomain } => {
                let domain = self.elaborate_value_type(domain, environment)?;
                let codomain = self.elaborate_computation_type(codomain, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTypeNode::Function { domain, codomain }))
            }
        }
    }

    pub fn elaborate_value(
        &mut self,
        expression: &ValueExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<Value, String> {
        let arena = environment.crate_env.arena();
        match expression {
            ValueExp::Access(access) => {
                if let Some((index, entry)) = self.local_index(environment, access) {
                    return match entry {
                        ProgramContextEntry::Value { .. } => Ok(arena.value_bound(index)),
                        ProgramContextEntry::Type { .. } => {
                            Err("Program type variable used as a value".into())
                        }
                    };
                }
                match self.item(environment, access)? {
                    ItemAccessResult::ProgramValueParameter(id) => {
                        Ok(arena.alloc(ValueNode::ModuleParam(id)))
                    }
                    ItemAccessResult::Definition(item) => {
                        match environment.crate_env.definition(item.definition) {
                            DefinedConstant::ProgramValue { .. } => {
                                Ok(arena.alloc(ValueNode::DefinedConstant(item.definition)))
                            }
                            _ => Err("definition is not a Program value".into()),
                        }
                    }
                    _ => Err("name does not denote a Program value".into()),
                }
            }
            ValueExp::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
            } => {
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("Program constructor path does not name a Program datatype".into());
                };
                let Some(idx) = item.ctor_names.iter().position(|name| name == constructor) else {
                    return Err(format!(
                        "Program constructor {} was not found",
                        constructor.as_str()
                    ));
                };
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.elaborate_value_type(parameter, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                let fields = fields
                    .iter()
                    .map(|field| self.elaborate_value(field, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueNode::InductiveConstructor {
                        indspec: item.inductive,
                        parameters,
                        idx,
                        fields,
                    }))
            }
            ValueExp::Thunk(computation) => {
                let computation = self.elaborate_computation(computation, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueNode::Thunk { computation }))
            }
            ValueExp::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let next = self.elaborate_value(next, environment)?;
                Ok(environment.crate_env.arena().alloc(ValueNode::Continue {
                    state_ty,
                    result_ty,
                    next,
                }))
            }
            ValueExp::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let output = self.elaborate_value(output, environment)?;
                Ok(environment.crate_env.arena().alloc(ValueNode::Finish {
                    state_ty,
                    result_ty,
                    output,
                }))
            }
        }
    }

    pub fn elaborate_computation(
        &mut self,
        expression: &ComputationExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<Computation, String> {
        match expression {
            ComputationExp::Access(access) => match self.item(environment, access)? {
                ItemAccessResult::Definition(item) => {
                    match environment.crate_env.definition(item.definition) {
                        DefinedConstant::ProgramComputation { .. } => Ok(environment
                            .crate_env
                            .arena()
                            .alloc(ComputationNode::DefinedConstant(item.definition))),
                        _ => Err("definition is not a Program computation".into()),
                    }
                }
                _ => Err("name does not denote a Program computation".into()),
            },
            ComputationExp::Return(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::Return { value }))
            }
            ComputationExp::Force(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::Force { value }))
            }
            ComputationExp::Lambda {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let var = environment.crate_env.intern(var.as_str());
                self.names.push(var);
                self.context
                    .push(ProgramContextEntry::Value { var, ty: value_ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::Lambda {
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationExp::Application { computation, value } => {
                let computation = self.elaborate_computation(computation, environment)?;
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::Application { computation, value }))
            }
            ComputationExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let computation = self.elaborate_computation(computation, environment)?;
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let var = environment.crate_env.intern(var.as_str());
                self.names.push(var);
                self.context
                    .push(ProgramContextEntry::Value { var, ty: value_ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::Sequence {
                        computation,
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationExp::ValueLet { var, value, body } => {
                let value = self.elaborate_value(value, environment)?;
                let ty = ProgramCheckSession::new(
                    &environment.crate_env,
                    environment.module_manager.current(),
                    &mut self.context,
                )
                .infer_value(value)
                .map_err(|error| format!("cannot infer vlet value: {error:?}"))?;
                let var = environment.crate_env.intern(var.as_str());
                self.names.push(var);
                self.context.push(ProgramContextEntry::Value { var, ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::ValueLet {
                        var,
                        value,
                        body: body?,
                    }))
            }
            ComputationExp::Case {
                datatype,
                scrutinee,
                branches,
            } => {
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("Program case path does not name a Program datatype".into());
                };
                if branches.len() != item.ctor_names.len() {
                    return Err("Program case must have one ordered branch per constructor".into());
                }
                let scrutinee = self.elaborate_value(scrutinee, environment)?;
                let mut check_context = self.context.clone();
                let scrutinee_ty = ProgramCheckSession::new(
                    &environment.crate_env,
                    environment.module_manager.current(),
                    &mut check_context,
                )
                .infer_value(scrutinee)
                .map_err(|error| format!("cannot infer Program case scrutinee: {error:?}"))?;
                let ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                } = environment.crate_env.arena().get(scrutinee_ty)
                else {
                    return Err("Program case scrutinee is not a Program datatype value".into());
                };
                if indspec != item.inductive {
                    return Err("Program case scrutinee datatype does not match its path".into());
                }
                let constructors = environment
                    .crate_env
                    .program_inductive(item.inductive)
                    .constructors()
                    .to_vec();
                let mut result = Vec::new();
                for (index, (constructor, binders, body)) in branches.iter().enumerate() {
                    if constructor != &item.ctor_names[index] {
                        return Err("Program case branches are not in constructor order".into());
                    }
                    let field_types = constructors[index]
                        .instantiated_fields(environment.crate_env.arena(), &parameters);
                    if binders.len() != field_types.len() {
                        return Err(format!(
                            "Program case branch {} has the wrong binder count",
                            constructor.as_str()
                        ));
                    }
                    let mark = self.context.len();
                    let mut binder_ids = Vec::new();
                    for (binder, (_, ty)) in binders.iter().zip(field_types) {
                        let binder = environment.crate_env.intern(binder.as_str());
                        self.push_value(binder, ty);
                        binder_ids.push(binder);
                    }
                    let body = self.elaborate_computation(body, environment)?;
                    self.truncate(mark);
                    result.push(kernel::program::ProgramCaseBranch {
                        binders: binder_ids,
                        body,
                    });
                }
                Ok(environment.crate_env.arena().alloc(ComputationNode::Case {
                    indspec: item.inductive,
                    scrutinee,
                    branches: result,
                }))
            }
            ComputationExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                Ok(environment.crate_env.arena().alloc(ComputationNode::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                }))
            }
            ComputationExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let transition = self.elaborate_computation(transition, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationNode::RunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                    }))
            }
        }
    }
}
