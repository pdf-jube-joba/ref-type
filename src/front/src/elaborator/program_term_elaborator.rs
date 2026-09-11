//! Elaboration for the four disjoint Program syntactic categories.

use crate::raw::{
    environment::DefinedConstant,
    exp::{Exp, ExpNode},
    ids::{MetaVarId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode,
        ProgramArgument, ProgramContext, ProgramContextEntry, ValueTerm, ValueTermNode, ValueType,
        ValueTypeNode,
    },
    program_calculus::strengthen_computation_type,
    program_derivation::ProgramCheckSession,
};
use crate::{
    elaborator::{
        GlobalEnvironment, module_manager::ItemAccessResult, term_elaborator::LocalScope,
    },
    syntax::{
        ComputationTermExp, ComputationTypeExp, LocalAccess, ProgramFunctionExp, SourceSpan,
        SurfaceMeta, ValueTermExp, ValueTypeExp,
    },
};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetaCategory {
    ValueType,
    ComputationType,
    ValueTerm,
    ComputationTerm,
}

#[derive(Debug, Clone, Copy)]
enum MetaSolution {
    ValueType(ValueType),
    ComputationType(ComputationType),
}

#[derive(Debug, Clone)]
struct ProgramMeta {
    flavor: SurfaceMeta,
    span: SourceSpan,
    category: MetaCategory,
    spine: Vec<ProgramArgument>,
    solution: Option<MetaSolution>,
}

#[derive(Debug, Clone)]
pub(crate) struct ProgramScope {
    names: Vec<SymbolId>,
    context: ProgramContext,
    value_type_bindings: Vec<(SymbolId, ValueType)>,
    metas: Vec<ProgramMeta>,
    named_metas: HashMap<u32, MetaVarId>,
    certificates: HashMap<ComputationTerm, Exp>,
}

impl Default for ProgramScope {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramScope {
    fn associated_arguments(
        &mut self,
        environment: &mut GlobalEnvironment,
        parameters: &[ValueTypeExp],
        expected: usize,
    ) -> Result<Vec<ValueType>, String> {
        if parameters.is_empty() && expected > 0 {
            return (0..expected)
                .map(|_| {
                    self.elaborate_value_type(
                        &ValueTypeExp::Meta {
                            kind: SurfaceMeta::Implicit,
                            span: SourceSpan { start: 0, end: 0 },
                        },
                        environment,
                    )
                })
                .collect();
        }
        if parameters.len() != expected {
            return Err(format!(
                "Program associated item expects {expected} type parameter(s), found {}",
                parameters.len()
            ));
        }
        parameters
            .iter()
            .map(|ty| self.elaborate_value_type(ty, environment))
            .collect()
    }
    pub(crate) fn new() -> Self {
        // Module parameters have stable identities and must not be captured as
        // de Bruijn locals: declarations and their uses can be nested beneath
        // different numbers of Program binders.
        Self {
            names: Vec::new(),
            context: Vec::new(),
            value_type_bindings: Vec::new(),
            metas: Vec::new(),
            named_metas: HashMap::new(),
            certificates: HashMap::new(),
        }
    }

    pub(crate) fn context(&self) -> &ProgramContext {
        &self.context
    }

    pub(crate) fn has_metas(&self) -> bool {
        !self.metas.is_empty()
    }

    pub(crate) fn has_certificates(&self) -> bool {
        !self.certificates.is_empty()
    }

    pub(crate) fn certified_computation(
        &self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
    ) -> Option<Exp> {
        let certificates = self
            .certificates
            .iter()
            .map(|(program, certificate)| {
                (self.zonk_computation(environment, *program), *certificate)
            })
            .collect::<HashMap<_, _>>();
        crate::raw::reflection::reflect_computation_with_certificates(
            &environment.crate_env,
            computation,
            &certificates,
        )
        .ok()
    }

    pub(crate) fn certified_value(
        &self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> Option<Exp> {
        let certificates = self
            .certificates
            .iter()
            .map(|(program, certificate)| {
                (self.zonk_computation(environment, *program), *certificate)
            })
            .collect::<HashMap<_, _>>();
        crate::raw::reflection::reflect_value_with_certificates(
            &environment.crate_env,
            value,
            &certificates,
        )
        .ok()
    }

    pub(crate) fn finish_metas(&self) -> Result<(), String> {
        self.finish_program_metas()
    }

    pub(crate) fn zonk_module_value_type(
        &self,
        environment: &GlobalEnvironment,
        ty: ValueType,
    ) -> ValueType {
        self.zonk_value_type(environment, ty)
    }

    pub(crate) fn zonk_module_value(
        &self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> ValueTerm {
        self.zonk_value(environment, value)
    }

    pub(crate) fn bind_value_type_name(&mut self, name: SymbolId, ty: ValueType) {
        self.value_type_bindings.push((name, ty));
    }

    pub(crate) fn push_type(&mut self, var: SymbolId) {
        self.names.push(var);
        self.context.push(ProgramContextEntry::ValueType { var });
    }

    pub(crate) fn push_value(&mut self, var: SymbolId, ty: ValueType) {
        self.names.push(var);
        self.context
            .push(ProgramContextEntry::ValueTerm { var, ty });
    }

    pub(crate) fn truncate(&mut self, len: usize) {
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

    fn meta_spine(&self, environment: &GlobalEnvironment) -> Vec<ProgramArgument> {
        self.context
            .iter()
            .rev()
            .enumerate()
            .map(|(index, entry)| match entry {
                ProgramContextEntry::ValueType { .. } => ProgramArgument::ValueType(
                    environment.crate_env.arena().value_type_bound(index),
                ),
                ProgramContextEntry::ValueTerm { .. } => {
                    ProgramArgument::ValueTerm(environment.crate_env.arena().value_bound(index))
                }
            })
            .collect()
    }

    fn fresh_meta(
        &mut self,
        environment: &GlobalEnvironment,
        flavor: SurfaceMeta,
        span: SourceSpan,
        category: MetaCategory,
    ) -> Result<(MetaVarId, Vec<ProgramArgument>), String> {
        let spine = self.meta_spine(environment);
        if let SurfaceMeta::Named(number) = flavor
            && let Some(id) = self.named_metas.get(&number).copied()
        {
            let existing = &self.metas[id.index()];
            if existing.category != category {
                return Err(format!(
                    "Program metavariable ?{number} is used in two syntactic categories"
                ));
            }
            if existing.spine != spine {
                return Err(format!(
                    "Program metavariable ?{number} is used under incompatible binders"
                ));
            }
            return Ok((id, spine));
        }
        let id = MetaVarId(
            u32::try_from(self.metas.len()).expect("Program metavariable table exceeded u32::MAX"),
        );
        self.metas.push(ProgramMeta {
            flavor,
            span,
            category,
            spine: spine.clone(),
            solution: None,
        });
        if let SurfaceMeta::Named(number) = flavor {
            self.named_metas.insert(number, id);
        }
        Ok((id, spine))
    }

    pub(crate) fn elaborate_value_type(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueType, String> {
        match expression {
            ValueTypeExp::Meta { kind, span } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *span, MetaCategory::ValueType)?;
                Ok(environment.crate_env.arena().alloc(ValueTypeNode::Meta {
                    metavariable,
                    spine,
                }))
            }
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
                        ProgramContextEntry::ValueType { .. } => Ok(arena.value_type_bound(index)),
                        ProgramContextEntry::ValueTerm { .. } => {
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

    pub(crate) fn elaborate_computation_type(
        &mut self,
        expression: &ComputationTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationType, String> {
        match expression {
            ComputationTypeExp::Meta { kind, span } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *span, MetaCategory::ComputationType)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTypeNode::Meta {
                        metavariable,
                        spine,
                    }))
            }
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

    pub(crate) fn elaborate_value(
        &mut self,
        expression: &ValueTermExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueTerm, String> {
        let arena = environment.crate_env.arena();
        match expression {
            ValueTermExp::Record {
                datatype,
                parameters,
                fields,
            } => {
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("expected Program structure type in record literal".into());
                };
                let Some(names) = &item.record_fields else {
                    return Err("expected Program structure type in record literal".into());
                };
                let parameters = self.associated_arguments(
                    environment,
                    parameters,
                    environment
                        .crate_env
                        .program_inductive(item.inductive)
                        .parameters()
                        .len(),
                )?;
                let mut supplied = HashMap::new();
                for (name, value) in fields {
                    if supplied.insert(name.as_str(), value).is_some() {
                        return Err(format!(
                            "Structure field {} was supplied more than once",
                            name.as_str()
                        ));
                    }
                    if !names.contains(name) {
                        return Err(format!("Unknown structure field {}", name.as_str()));
                    }
                }
                let fields = names
                    .iter()
                    .map(|name| {
                        let value = supplied
                            .get(name.as_str())
                            .ok_or_else(|| format!("Missing structure field {}", name.as_str()))?;
                        self.elaborate_value(value, environment)
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTermNode::InductiveConstructor {
                        indspec: item.inductive,
                        parameters,
                        idx: 0,
                        fields,
                    }))
            }
            ValueTermExp::Meta { kind, span } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *span, MetaCategory::ValueTerm)?;
                Ok(arena.alloc(ValueTermNode::Meta {
                    metavariable,
                    spine,
                }))
            }
            ValueTermExp::Access(access) => {
                if let Some((index, entry)) = self.local_index(environment, access) {
                    return match entry {
                        ProgramContextEntry::ValueTerm { .. } => Ok(arena.value_bound(index)),
                        ProgramContextEntry::ValueType { .. } => {
                            Err("Program type variable used as a value".into())
                        }
                    };
                }
                match self.item(environment, access)? {
                    ItemAccessResult::ProgramValueParameter(id) => {
                        Ok(arena.alloc(ValueTermNode::ModuleParam(id)))
                    }
                    ItemAccessResult::Definition(item) => {
                        match environment.crate_env.definition(item.definition) {
                            DefinedConstant::ProgramValue { .. } => {
                                Ok(arena.alloc(ValueTermNode::DefinedConstant(item.definition)))
                            }
                            _ => Err("definition is not a Program value".into()),
                        }
                    }
                    _ => Err("name does not denote a Program value".into()),
                }
            }
            ValueTermExp::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
            } => {
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("Program constructor path does not name a Program datatype".into());
                };
                if let Some((_, definition)) = item
                    .associated_definitions
                    .iter()
                    .find(|(name, _)| name == constructor)
                {
                    if !fields.is_empty() {
                        return Err("Program associated values do not take value arguments".into());
                    }
                    if !matches!(
                        environment.crate_env.definition(*definition),
                        DefinedConstant::ProgramValue { .. }
                    ) {
                        return Err("associated item is not a Program value".into());
                    }
                    let parameters = self.associated_arguments(
                        environment,
                        parameters,
                        environment
                            .crate_env
                            .definition_parameters(*definition)
                            .len(),
                    )?;
                    return Ok(environment.crate_env.arena().alloc(
                        ValueTermNode::DefinitionInstance {
                            definition: *definition,
                            parameters,
                        },
                    ));
                }
                if item.record_fields.is_some() {
                    return Err(format!(
                        "Program associated item {} was not found",
                        constructor.as_str()
                    ));
                }
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.elaborate_value_type(parameter, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                let fields = fields
                    .iter()
                    .map(|field| self.elaborate_value(field, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(idx) = item.ctor_names.iter().position(|name| name == constructor) else {
                    return Err(format!(
                        "Program constructor {} was not found",
                        constructor.as_str()
                    ));
                };
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTermNode::InductiveConstructor {
                        indspec: item.inductive,
                        parameters,
                        idx,
                        fields,
                    }))
            }
            ValueTermExp::Thunk(computation) => {
                let computation = self.elaborate_computation(computation, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTermNode::Thunk { computation }))
            }
            ValueTermExp::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let next = self.elaborate_value(next, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTermNode::Continue {
                        state_ty,
                        result_ty,
                        next,
                    }))
            }
            ValueTermExp::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let output = self.elaborate_value(output, environment)?;
                Ok(environment.crate_env.arena().alloc(ValueTermNode::Finish {
                    state_ty,
                    result_ty,
                    output,
                }))
            }
        }
    }

    pub(crate) fn elaborate_computation(
        &mut self,
        expression: &ComputationTermExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, String> {
        match expression {
            ComputationTermExp::Associated {
                datatype,
                item: name,
                parameters,
            } => {
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("expected Program type before associated access".into());
                };
                let (_, definition) = item
                    .associated_definitions
                    .iter()
                    .find(|(candidate, _)| candidate == name)
                    .ok_or_else(|| {
                        format!("Program associated item {} was not found", name.as_str())
                    })?;
                if !matches!(
                    environment.crate_env.definition(*definition),
                    DefinedConstant::ProgramComputation { .. }
                ) {
                    return Err("associated item is not a Program computation".into());
                }
                let parameters = self.associated_arguments(
                    environment,
                    parameters,
                    environment
                        .crate_env
                        .definition_parameters(*definition)
                        .len(),
                )?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::DefinitionInstance {
                        definition: *definition,
                        parameters,
                    }))
            }
            ComputationTermExp::Meta { kind, span } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *span, MetaCategory::ComputationTerm)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Meta {
                        metavariable,
                        spine,
                    }))
            }
            ComputationTermExp::Access(access) => match self.item(environment, access)? {
                ItemAccessResult::Definition(item) => {
                    match environment.crate_env.definition(item.definition) {
                        DefinedConstant::ProgramComputation { .. } => Ok(environment
                            .crate_env
                            .arena()
                            .alloc(ComputationTermNode::DefinedConstant(item.definition))),
                        _ => Err("definition is not a Program computation".into()),
                    }
                }
                _ => Err("name does not denote a Program computation".into()),
            },
            ComputationTermExp::Return(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Return { value }))
            }
            ComputationTermExp::Force(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Force { value }))
            }
            ComputationTermExp::Lambda {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let var = environment.crate_env.intern(var.as_str());
                self.names.push(var);
                self.context
                    .push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Lambda {
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationTermExp::Application {
                function,
                arguments,
            } => self.elaborate_application(function, arguments, environment),
            ComputationTermExp::Sequence {
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
                    .push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Sequence {
                        computation,
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationTermExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let value = self.elaborate_value(value, environment)?;
                let var = environment.crate_env.intern(var.as_str());
                self.names.push(var);
                self.context
                    .push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.elaborate_computation(body, environment);
                self.names.pop();
                self.context.pop();
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::ValueLet {
                        var,
                        value_ty,
                        value,
                        body: body?,
                    }))
            }
            ComputationTermExp::Case {
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
                let scrutinee_ty =
                    ProgramCheckSession::new(&environment.crate_env, &mut check_context)
                        .infer_value_term(scrutinee)
                        .map_err(|error| {
                            format!("cannot infer Program case scrutinee: {error:?}")
                        })?;
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
                    for (field_index, (binder, (_, ty))) in
                        binders.iter().zip(field_types).enumerate()
                    {
                        let binder = environment.crate_env.intern(binder.as_str());
                        let ty = crate::raw::program_calculus::shift_value_type_indices(
                            environment.crate_env.arena(),
                            ty,
                            field_index,
                            0,
                        );
                        self.push_value(binder, ty);
                        binder_ids.push(binder);
                    }
                    let body = self.elaborate_computation(body, environment)?;
                    self.truncate(mark);
                    result.push(crate::raw::program::ProgramCaseBranch {
                        binders: binder_ids,
                        body,
                    });
                }
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Case {
                        indspec: item.inductive,
                        scrutinee,
                        branches: result,
                    }))
            }
            ComputationTermExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let computation = environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                    });
                if let Some(accessibility) = accessibility {
                    let reflected_context = crate::raw::reflection::reflect_context(
                        &environment.crate_env,
                        &self.context,
                    )
                    .map_err(|error| error.to_string())?;
                    let proof = LocalScope::from_typing_context(reflected_context)
                        .elab_exp(accessibility, environment)?;
                    let arena = environment.crate_env.arena();
                    let certificate = arena.alloc(ExpNode::SetRun {
                        state_ty: crate::raw::reflection::reflect_value_type(
                            &environment.crate_env,
                            state_ty,
                        )
                        .map_err(|error| error.to_string())?,
                        result_ty: crate::raw::reflection::reflect_value_type(
                            &environment.crate_env,
                            result_ty,
                        )
                        .map_err(|error| error.to_string())?,
                        step: crate::raw::reflection::reflect_value_with_certificates(
                            &environment.crate_env,
                            step,
                            &self.certificates,
                        )
                        .map_err(|error| error.to_string())?,
                        initial: crate::raw::reflection::reflect_value_with_certificates(
                            &environment.crate_env,
                            initial,
                            &self.certificates,
                        )
                        .map_err(|error| error.to_string())?,
                        accessibility: proof,
                    });
                    self.certificates.insert(computation, certificate);
                }
                Ok(computation)
            }
            ComputationTermExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let transition = self.elaborate_computation(transition, environment)?;
                let computation =
                    environment
                        .crate_env
                        .arena()
                        .alloc(ComputationTermNode::RunCase {
                            state_ty,
                            result_ty,
                            step,
                            initial,
                            transition,
                        });
                if let (Some(accessibility), Some(transition_equality)) =
                    (accessibility, transition_equality)
                {
                    let reflected_context = crate::raw::reflection::reflect_context(
                        &environment.crate_env,
                        &self.context,
                    )
                    .map_err(|error| error.to_string())?;
                    let mut proof_scope = LocalScope::from_typing_context(reflected_context);
                    let accessibility = proof_scope.elab_exp(accessibility, environment)?;
                    let transition_equality =
                        proof_scope.elab_exp(transition_equality, environment)?;
                    let arena = environment.crate_env.arena();
                    let certificate = arena.alloc(ExpNode::SetRunCase {
                        state_ty: crate::raw::reflection::reflect_value_type(
                            &environment.crate_env,
                            state_ty,
                        )
                        .map_err(|error| error.to_string())?,
                        result_ty: crate::raw::reflection::reflect_value_type(
                            &environment.crate_env,
                            result_ty,
                        )
                        .map_err(|error| error.to_string())?,
                        step: crate::raw::reflection::reflect_value_with_certificates(
                            &environment.crate_env,
                            step,
                            &self.certificates,
                        )
                        .map_err(|error| error.to_string())?,
                        initial: crate::raw::reflection::reflect_value_with_certificates(
                            &environment.crate_env,
                            initial,
                            &self.certificates,
                        )
                        .map_err(|error| error.to_string())?,
                        transition: self
                            .certified_computation(environment, transition)
                            .ok_or("runCase transition is not certified")?,
                        accessibility,
                        transition_equality,
                    });
                    self.certificates.insert(computation, certificate);
                }
                Ok(computation)
            }
        }
    }

    fn elaborate_application(
        &mut self,
        function: &ProgramFunctionExp,
        arguments: &[ValueTermExp],
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, String> {
        enum Head {
            Value(ValueTerm, Option<ValueType>),
            Computation(ComputationTerm, Option<ComputationType>),
        }

        let head = match function {
            ProgramFunctionExp::Value(value) => {
                let value = self.elaborate_value(value, environment)?;
                let mut context = self.context.clone();
                let ty = self.infer_value_term(environment, &mut context, value).ok();
                Head::Value(value, ty)
            }
            ProgramFunctionExp::Computation(computation) => {
                let computation = self.elaborate_computation(computation, environment)?;
                let mut context = self.context.clone();
                let ty = self
                    .infer_computation_term(environment, &mut context, computation)
                    .ok();
                Head::Computation(computation, ty)
            }
            ProgramFunctionExp::Access(access) => {
                if let Some((index, entry)) = self.local_index(environment, access) {
                    let ProgramContextEntry::ValueTerm { ty, .. } = entry else {
                        return Err("Program type variable used as an application head".into());
                    };
                    Head::Value(environment.crate_env.arena().value_bound(index), Some(ty))
                } else {
                    match self.item(environment, access)? {
                        ItemAccessResult::ProgramValueParameter(id) => {
                            let ty = environment
                                .crate_env
                                .module_parameter_opt(id)
                                .and_then(|parameter| parameter.value_ty());
                            Head::Value(
                                environment
                                    .crate_env
                                    .arena()
                                    .alloc(ValueTermNode::ModuleParam(id)),
                                ty,
                            )
                        }
                        ItemAccessResult::Definition(item) => {
                            match environment.crate_env.definition(item.definition) {
                                DefinedConstant::ProgramValue { ty, .. } => Head::Value(
                                    environment
                                        .crate_env
                                        .arena()
                                        .alloc(ValueTermNode::DefinedConstant(item.definition)),
                                    Some(*ty),
                                ),
                                DefinedConstant::ProgramComputation { ty, .. } => {
                                    Head::Computation(
                                        environment.crate_env.arena().alloc(
                                            ComputationTermNode::DefinedConstant(item.definition),
                                        ),
                                        Some(*ty),
                                    )
                                }
                                _ => {
                                    return Err(
                                        "Program application head has the wrong category".into()
                                    );
                                }
                            }
                        }
                        _ => {
                            return Err(
                                "Program application head is not a function value or computation"
                                    .into(),
                            );
                        }
                    }
                }
            }
            ProgramFunctionExp::Associated {
                datatype,
                item,
                parameters,
            } => {
                let ItemAccessResult::ProgramInductive(datatype_item) =
                    self.item(environment, datatype)?
                else {
                    return Err("expected Program type before associated application".into());
                };
                let (_, definition) = datatype_item
                    .associated_definitions
                    .iter()
                    .find(|(candidate, _)| candidate == item)
                    .ok_or_else(|| {
                        format!("Program associated item {} was not found", item.as_str())
                    })?;
                let definition = *definition;
                let definition_ty = match environment.crate_env.definition(definition) {
                    DefinedConstant::ProgramValue { ty, .. } => Ok(*ty),
                    DefinedConstant::ProgramComputation { ty, .. } => Err(*ty),
                    _ => return Err("associated Program item has the wrong category".into()),
                };
                match definition_ty {
                    Ok(ty) => {
                        let value = self.elaborate_value(
                            &ValueTermExp::Constructor {
                                datatype: datatype.clone(),
                                constructor: item.clone(),
                                parameters: parameters.clone(),
                                fields: Vec::new(),
                            },
                            environment,
                        )?;
                        let ValueTermNode::DefinitionInstance { parameters, .. } =
                            environment.crate_env.arena().get(value)
                        else {
                            unreachable!()
                        };
                        let ty = crate::raw::program_definitions::instantiate_value_type(
                            environment.crate_env.arena(),
                            ty,
                            &parameters,
                            0,
                        );
                        Head::Value(value, Some(ty))
                    }
                    Err(ty) => {
                        let computation = self.elaborate_computation(
                            &ComputationTermExp::Associated {
                                datatype: datatype.clone(),
                                item: item.clone(),
                                parameters: parameters.clone(),
                            },
                            environment,
                        )?;
                        let ComputationTermNode::DefinitionInstance { parameters, .. } =
                            environment.crate_env.arena().get(computation)
                        else {
                            unreachable!()
                        };
                        let ty = crate::raw::program_definitions::instantiate_computation_type(
                            environment.crate_env.arena(),
                            ty,
                            &parameters,
                            0,
                        );
                        Head::Computation(computation, Some(ty))
                    }
                }
            }
        };

        let arguments = arguments
            .iter()
            .map(|argument| self.elaborate_value(argument, environment))
            .collect::<Result<Vec<_>, _>>()?;
        let head_is_computation = matches!(&head, Head::Computation(_, _));
        let (mut computation, mut computation_ty) = match head {
            Head::Computation(computation, ty) => (computation, ty),
            Head::Value(value, Some(ty)) => {
                let ty = self.resolve_value_type_head(environment, ty);
                let computation_ty = match environment.crate_env.arena().get(ty) {
                    ValueTypeNode::Thunk { computation_ty } => computation_ty,
                    ValueTypeNode::Meta { .. } => {
                        let (metavariable, spine) = self.fresh_meta(
                            environment,
                            SurfaceMeta::Implicit,
                            SourceSpan { start: 0, end: 0 },
                            MetaCategory::ComputationType,
                        )?;
                        let mut codomain =
                            environment
                                .crate_env
                                .arena()
                                .alloc(ComputationTypeNode::Meta {
                                    metavariable,
                                    spine,
                                });
                        let mut function_ty = None;
                        for (index, argument) in arguments.iter().rev().enumerate() {
                            let mut context = self.context.clone();
                            let domain =
                                self.infer_value_term(environment, &mut context, *argument)?;
                            let current = environment
                                .crate_env
                                .arena()
                                .alloc(ComputationTypeNode::Function { domain, codomain });
                            function_ty = Some(current);
                            if index + 1 < arguments.len() {
                                let thunk =
                                    environment.crate_env.arena().alloc(ValueTypeNode::Thunk {
                                        computation_ty: current,
                                    });
                                codomain = environment
                                    .crate_env
                                    .arena()
                                    .alloc(ComputationTypeNode::Return { value_ty: thunk });
                            }
                        }
                        let function_ty = function_ty.ok_or_else(|| {
                            "Program application requires at least one argument".to_string()
                        })?;
                        let expected = environment.crate_env.arena().alloc(ValueTypeNode::Thunk {
                            computation_ty: function_ty,
                        });
                        self.unify_value_types(environment, ty, expected)?;
                        function_ty
                    }
                    _ => {
                        return Err("Program application head value is not a function thunk".into());
                    }
                };
                (
                    environment
                        .crate_env
                        .arena()
                        .alloc(ComputationTermNode::Force { value }),
                    Some(computation_ty),
                )
            }
            Head::Value(_, None) => {
                return Err(
                    "cannot determine the type of Program function value; add a type annotation"
                        .into(),
                );
            }
        };

        for argument in arguments {
            let Some(ty) = computation_ty else {
                computation =
                    environment
                        .crate_env
                        .arena()
                        .alloc(ComputationTermNode::Application {
                            computation,
                            value: argument,
                        });
                continue;
            };
            let ty = self.resolve_computation_type_head(environment, ty);
            match environment.crate_env.arena().get(ty) {
                ComputationTypeNode::Function { codomain, .. } => {
                    computation =
                        environment
                            .crate_env
                            .arena()
                            .alloc(ComputationTermNode::Application {
                                computation,
                                value: argument,
                            });
                    computation_ty = Some(codomain);
                }
                ComputationTypeNode::Return { value_ty } => {
                    let value_ty = self.resolve_value_type_head(environment, value_ty);
                    let ValueTypeNode::Thunk {
                        computation_ty: thunk_ty,
                    } = environment.crate_env.arena().get(value_ty)
                    else {
                        if head_is_computation {
                            computation = environment.crate_env.arena().alloc(
                                ComputationTermNode::Application {
                                    computation,
                                    value: argument,
                                },
                            );
                            computation_ty = None;
                            continue;
                        }
                        return Err(
                            "Program computation application head did not return a function value"
                                .into(),
                        );
                    };
                    let function_ty = self.resolve_computation_type_head(environment, thunk_ty);
                    let ComputationTypeNode::Function { codomain, .. } =
                        environment.crate_env.arena().get(function_ty)
                    else {
                        return Err(
                            "Program computation application head did not return a function value"
                                .into(),
                        );
                    };
                    let var = environment.crate_env.intern("<cbv-function>");
                    let arena = environment.crate_env.arena();
                    let forced = arena.alloc(ComputationTermNode::Force {
                        value: arena.value_bound(0),
                    });
                    let shifted_argument =
                        crate::raw::program_calculus::shift_value_indices(arena, argument, 1, 0);
                    let body = arena.alloc(ComputationTermNode::Application {
                        computation: forced,
                        value: shifted_argument,
                    });
                    computation = arena.alloc(ComputationTermNode::Sequence {
                        computation,
                        var,
                        value_ty,
                        body,
                    });
                    computation_ty = Some(codomain);
                }
                ComputationTypeNode::Meta { .. } => {
                    if head_is_computation {
                        computation =
                            environment
                                .crate_env
                                .arena()
                                .alloc(ComputationTermNode::Application {
                                    computation,
                                    value: argument,
                                });
                        computation_ty = None;
                    } else {
                        return Err(
                            "cannot determine whether Program application head is a function; add a type annotation"
                                .into(),
                        );
                    }
                }
            }
        }
        Ok(computation)
    }
}

impl ProgramScope {
    /// Resolve only a metavariable at the root. Application elaboration needs
    /// the outer constructor, and rebuilding whole types here would make every
    /// ordinary application allocate a duplicate type tree.
    fn resolve_value_type_head(
        &self,
        environment: &GlobalEnvironment,
        mut ty: ValueType,
    ) -> ValueType {
        while let ValueTypeNode::Meta { metavariable, .. } = environment.crate_env.arena().get(ty) {
            let Some(MetaSolution::ValueType(solution)) = self.metas[metavariable.index()].solution
            else {
                break;
            };
            ty = solution;
        }
        ty
    }

    fn resolve_computation_type_head(
        &self,
        environment: &GlobalEnvironment,
        mut ty: ComputationType,
    ) -> ComputationType {
        while let ComputationTypeNode::Meta { metavariable, .. } =
            environment.crate_env.arena().get(ty)
        {
            let Some(MetaSolution::ComputationType(solution)) =
                self.metas[metavariable.index()].solution
            else {
                break;
            };
            ty = solution;
        }
        ty
    }

    fn zonk_value_type(&self, environment: &GlobalEnvironment, ty: ValueType) -> ValueType {
        let arena = environment.crate_env.arena();
        match arena.get(ty) {
            ValueTypeNode::Meta { metavariable, .. } => {
                match self.metas[metavariable.index()].solution {
                    Some(MetaSolution::ValueType(solution)) => {
                        self.zonk_value_type(environment, solution)
                    }
                    _ => ty,
                }
            }
            ValueTypeNode::Thunk { computation_ty } => arena.alloc(ValueTypeNode::Thunk {
                computation_ty: self.zonk_computation_type(environment, computation_ty),
            }),
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => arena.alloc(ValueTypeNode::RunStep {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
            }),
            ValueTypeNode::Inductive {
                indspec,
                parameters,
            } => arena.alloc(ValueTypeNode::Inductive {
                indspec,
                parameters: parameters
                    .into_iter()
                    .map(|parameter| self.zonk_value_type(environment, parameter))
                    .collect(),
            }),
            _ => ty,
        }
    }

    fn zonk_computation_type(
        &self,
        environment: &GlobalEnvironment,
        ty: ComputationType,
    ) -> ComputationType {
        let arena = environment.crate_env.arena();
        match arena.get(ty) {
            ComputationTypeNode::Meta { metavariable, .. } => {
                match self.metas[metavariable.index()].solution {
                    Some(MetaSolution::ComputationType(solution)) => {
                        self.zonk_computation_type(environment, solution)
                    }
                    _ => ty,
                }
            }
            ComputationTypeNode::Return { value_ty } => arena.alloc(ComputationTypeNode::Return {
                value_ty: self.zonk_value_type(environment, value_ty),
            }),
            ComputationTypeNode::Function { domain, codomain } => {
                arena.alloc(ComputationTypeNode::Function {
                    domain: self.zonk_value_type(environment, domain),
                    codomain: self.zonk_computation_type(environment, codomain),
                })
            }
        }
    }

    fn zonk_arguments(
        &self,
        environment: &GlobalEnvironment,
        arguments: Vec<ProgramArgument>,
    ) -> Vec<ProgramArgument> {
        arguments
            .into_iter()
            .map(|argument| match argument {
                ProgramArgument::ValueType(ty) => {
                    ProgramArgument::ValueType(self.zonk_value_type(environment, ty))
                }
                ProgramArgument::ValueTerm(value) => {
                    ProgramArgument::ValueTerm(self.zonk_value(environment, value))
                }
            })
            .collect()
    }

    fn zonk_value(&self, environment: &GlobalEnvironment, value: ValueTerm) -> ValueTerm {
        let arena = environment.crate_env.arena();
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.alloc(ValueTermNode::DefinitionInstance {
                definition,
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.zonk_value_type(environment, ty))
                    .collect(),
            }),
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => arena.alloc(ValueTermNode::Meta {
                metavariable,
                spine: self.zonk_arguments(environment, spine),
            }),
            ValueTermNode::Thunk { computation } => arena.alloc(ValueTermNode::Thunk {
                computation: self.zonk_computation(environment, computation),
            }),
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.alloc(ValueTermNode::Continue {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                next: self.zonk_value(environment, next),
            }),
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.alloc(ValueTermNode::Finish {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                output: self.zonk_value(environment, output),
            }),
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => arena.alloc(ValueTermNode::InductiveConstructor {
                indspec,
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.zonk_value_type(environment, ty))
                    .collect(),
                idx,
                fields: fields
                    .into_iter()
                    .map(|value| self.zonk_value(environment, value))
                    .collect(),
            }),
            _ => value,
        }
    }

    fn zonk_computation(
        &self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
    ) -> ComputationTerm {
        let arena = environment.crate_env.arena();
        match arena.get(computation) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.alloc(ComputationTermNode::DefinitionInstance {
                definition,
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.zonk_value_type(environment, ty))
                    .collect(),
            }),
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => arena.alloc(ComputationTermNode::Meta {
                metavariable,
                spine: self.zonk_arguments(environment, spine),
            }),
            ComputationTermNode::Return { value } => arena.alloc(ComputationTermNode::Return {
                value: self.zonk_value(environment, value),
            }),
            ComputationTermNode::Force { value } => arena.alloc(ComputationTermNode::Force {
                value: self.zonk_value(environment, value),
            }),
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => arena.alloc(ComputationTermNode::Lambda {
                var,
                value_ty: self.zonk_value_type(environment, value_ty),
                body: self.zonk_computation(environment, body),
            }),
            ComputationTermNode::Application { computation, value } => {
                arena.alloc(ComputationTermNode::Application {
                    computation: self.zonk_computation(environment, computation),
                    value: self.zonk_value(environment, value),
                })
            }
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => arena.alloc(ComputationTermNode::Sequence {
                computation: self.zonk_computation(environment, computation),
                var,
                value_ty: self.zonk_value_type(environment, value_ty),
                body: self.zonk_computation(environment, body),
            }),
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => arena.alloc(ComputationTermNode::ValueLet {
                var,
                value_ty: self.zonk_value_type(environment, value_ty),
                value: self.zonk_value(environment, value),
                body: self.zonk_computation(environment, body),
            }),
            ComputationTermNode::Case {
                indspec,
                scrutinee,
                branches,
            } => arena.alloc(ComputationTermNode::Case {
                indspec,
                scrutinee: self.zonk_value(environment, scrutinee),
                branches: branches
                    .into_iter()
                    .map(|branch| crate::raw::program::ProgramCaseBranch {
                        binders: branch.binders,
                        body: self.zonk_computation(environment, branch.body),
                    })
                    .collect(),
            }),
            ComputationTermNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => arena.alloc(ComputationTermNode::Run {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                step: self.zonk_value(environment, step),
                initial: self.zonk_value(environment, initial),
            }),
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => arena.alloc(ComputationTermNode::RunCase {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                step: self.zonk_value(environment, step),
                initial: self.zonk_value(environment, initial),
                transition: self.zonk_computation(environment, transition),
            }),
            _ => computation,
        }
    }

    fn value_type_occurs(
        &self,
        environment: &GlobalEnvironment,
        needle: MetaVarId,
        ty: ValueType,
    ) -> bool {
        let ty = self.zonk_value_type(environment, ty);
        match environment.crate_env.arena().get(ty) {
            ValueTypeNode::Meta { metavariable, .. } => metavariable == needle,
            ValueTypeNode::Thunk { computation_ty } => {
                self.computation_type_occurs(environment, needle, computation_ty)
            }
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => {
                self.value_type_occurs(environment, needle, state_ty)
                    || self.value_type_occurs(environment, needle, result_ty)
            }
            ValueTypeNode::Inductive { parameters, .. } => parameters
                .into_iter()
                .any(|parameter| self.value_type_occurs(environment, needle, parameter)),
            _ => false,
        }
    }

    fn computation_type_occurs(
        &self,
        environment: &GlobalEnvironment,
        needle: MetaVarId,
        ty: ComputationType,
    ) -> bool {
        let ty = self.zonk_computation_type(environment, ty);
        match environment.crate_env.arena().get(ty) {
            ComputationTypeNode::Meta { metavariable, .. } => metavariable == needle,
            ComputationTypeNode::Return { value_ty } => {
                self.value_type_occurs(environment, needle, value_ty)
            }
            ComputationTypeNode::Function { domain, codomain } => {
                self.value_type_occurs(environment, needle, domain)
                    || self.computation_type_occurs(environment, needle, codomain)
            }
        }
    }

    fn unify_value_types(
        &mut self,
        environment: &GlobalEnvironment,
        left: ValueType,
        right: ValueType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let left = self.zonk_value_type(environment, left);
        let right = self.zonk_value_type(environment, right);
        if crate::raw::program_calculus::value_type_is_alpha_eq(arena, left, right) {
            return Ok(());
        }
        match (arena.get(left), arena.get(right)) {
            (ValueTypeNode::Meta { metavariable, .. }, _) => {
                if self.value_type_occurs(environment, metavariable, right) {
                    return Err("cyclic Program value-type metavariable solution".into());
                }
                self.metas[metavariable.index()].solution = Some(MetaSolution::ValueType(right));
                Ok(())
            }
            (_, ValueTypeNode::Meta { metavariable, .. }) => {
                if self.value_type_occurs(environment, metavariable, left) {
                    return Err("cyclic Program value-type metavariable solution".into());
                }
                self.metas[metavariable.index()].solution = Some(MetaSolution::ValueType(left));
                Ok(())
            }
            (
                ValueTypeNode::Thunk {
                    computation_ty: left,
                },
                ValueTypeNode::Thunk {
                    computation_ty: right,
                },
            ) => self.unify_computation_types(environment, left, right),
            (
                ValueTypeNode::RunStep {
                    state_ty: left_state,
                    result_ty: left_result,
                },
                ValueTypeNode::RunStep {
                    state_ty: right_state,
                    result_ty: right_result,
                },
            ) => {
                self.unify_value_types(environment, left_state, right_state)?;
                self.unify_value_types(environment, left_result, right_result)
            }
            (
                ValueTypeNode::Inductive {
                    indspec: left_spec,
                    parameters: left_parameters,
                },
                ValueTypeNode::Inductive {
                    indspec: right_spec,
                    parameters: right_parameters,
                },
            ) if left_spec == right_spec && left_parameters.len() == right_parameters.len() => {
                for (left, right) in left_parameters.into_iter().zip(right_parameters) {
                    self.unify_value_types(environment, left, right)?;
                }
                Ok(())
            }
            _ => Err(format!(
                "Program value types do not unify: {:?} and {:?}",
                arena.get(left),
                arena.get(right)
            )),
        }
    }

    fn unify_computation_types(
        &mut self,
        environment: &GlobalEnvironment,
        left: ComputationType,
        right: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let left = self.zonk_computation_type(environment, left);
        let right = self.zonk_computation_type(environment, right);
        if crate::raw::program_calculus::computation_type_is_alpha_eq(arena, left, right) {
            return Ok(());
        }
        match (arena.get(left), arena.get(right)) {
            (ComputationTypeNode::Meta { metavariable, .. }, _) => {
                if self.computation_type_occurs(environment, metavariable, right) {
                    return Err("cyclic Program computation-type metavariable solution".into());
                }
                self.metas[metavariable.index()].solution =
                    Some(MetaSolution::ComputationType(right));
                Ok(())
            }
            (_, ComputationTypeNode::Meta { metavariable, .. }) => {
                if self.computation_type_occurs(environment, metavariable, left) {
                    return Err("cyclic Program computation-type metavariable solution".into());
                }
                self.metas[metavariable.index()].solution =
                    Some(MetaSolution::ComputationType(left));
                Ok(())
            }
            (
                ComputationTypeNode::Return { value_ty: left },
                ComputationTypeNode::Return { value_ty: right },
            ) => self.unify_value_types(environment, left, right),
            (
                ComputationTypeNode::Function {
                    domain: left_domain,
                    codomain: left_codomain,
                },
                ComputationTypeNode::Function {
                    domain: right_domain,
                    codomain: right_codomain,
                },
            ) => {
                self.unify_value_types(environment, left_domain, right_domain)?;
                self.unify_computation_types(environment, left_codomain, right_codomain)
            }
            _ => Err(format!(
                "Program computation types do not unify: {:?} and {:?}",
                arena.get(left),
                arena.get(right)
            )),
        }
    }

    fn finish_program_metas(&self) -> Result<(), String> {
        let unsolved = self
            .metas
            .iter()
            .filter(|meta| meta.solution.is_none())
            .collect::<Vec<_>>();
        if unsolved.is_empty() {
            return Ok(());
        }
        let meta = unsolved[0];
        let name = match meta.flavor {
            SurfaceMeta::Implicit => "_".to_string(),
            SurfaceMeta::Goal => "?".to_string(),
            SurfaceMeta::Named(number) => format!("?{number}"),
        };
        Err(format!(
            "unsolved Program metavariable {name} at {}..{} in {:?} syntax",
            meta.span.start, meta.span.end, meta.category
        ))
    }

    fn infer_kernel_value(
        &self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        ProgramCheckSession::new(&environment.crate_env, context)
            .infer_value_term(value)
            .map_err(|error| format!("cannot infer Program value: {error:?}"))
    }

    fn infer_kernel_computation(
        &self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        ProgramCheckSession::new(&environment.crate_env, context)
            .infer_computation_term(computation)
            .map_err(|error| format!("cannot infer Program computation: {error:?}"))
    }

    fn solve_value(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let expected = self.zonk_value_type(environment, expected);
        match arena.get(value) {
            ValueTermNode::DefinitionInstance { .. } => {
                let inferred = self.infer_value_term(environment, context, value)?;
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Meta { .. } => Ok(()),
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => {
                let inferred = self.infer_kernel_value(environment, context, value)?;
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Thunk { computation } => {
                if let ValueTypeNode::Thunk { computation_ty } = arena.get(expected) {
                    self.solve_computation(environment, context, computation, computation_ty)
                } else {
                    let inferred =
                        self.infer_computation_term(environment, context, computation)?;
                    let inferred = arena.alloc(ValueTypeNode::Thunk {
                        computation_ty: inferred,
                    });
                    self.unify_value_types(environment, inferred, expected)
                }
            }
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                if let ValueTypeNode::RunStep {
                    state_ty: expected_state,
                    result_ty: expected_result,
                } = arena.get(expected)
                {
                    self.unify_value_types(environment, state_ty, expected_state)?;
                    self.unify_value_types(environment, result_ty, expected_result)?;
                }
                self.solve_value(environment, context, next, state_ty)?;
                let inferred = arena.alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                });
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                if let ValueTypeNode::RunStep {
                    state_ty: expected_state,
                    result_ty: expected_result,
                } = arena.get(expected)
                {
                    self.unify_value_types(environment, state_ty, expected_state)?;
                    self.unify_value_types(environment, result_ty, expected_result)?;
                }
                self.solve_value(environment, context, output, result_ty)?;
                let inferred = arena.alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                });
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let result = arena.alloc(ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters.clone(),
                });
                self.unify_value_types(environment, result, expected)?;
                let parameters = parameters
                    .into_iter()
                    .map(|parameter| self.zonk_value_type(environment, parameter))
                    .collect::<Vec<_>>();
                let expected_fields = environment
                    .crate_env
                    .program_inductive(indspec)
                    .constructors()
                    .get(idx)
                    .ok_or_else(|| "Program constructor index out of bounds".to_string())?
                    .instantiated_fields(arena, &parameters);
                if fields.len() != expected_fields.len() {
                    return Err("Program constructor field count mismatch".into());
                }
                for (field, (_, field_ty)) in fields.into_iter().zip(expected_fields) {
                    self.solve_value(environment, context, field, field_ty)?;
                }
                Ok(())
            }
        }
    }

    fn infer_value_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        let arena = environment.crate_env.arena();
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramValue { ty, .. } =
                    environment.crate_env.definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(crate::raw::program_definitions::instantiate_value_type(
                    arena,
                    *ty,
                    &parameters,
                    0,
                ))
            }
            ValueTermNode::Meta { .. } => {
                Err("cannot infer an unconstrained Program value metavariable".into())
            }
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => {
                self.infer_kernel_value(environment, context, value)
            }
            ValueTermNode::Thunk { computation } => {
                let computation_ty =
                    self.infer_computation_term(environment, context, computation)?;
                Ok(arena.alloc(ValueTypeNode::Thunk { computation_ty }))
            }
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                self.solve_value(environment, context, next, state_ty)?;
                Ok(arena.alloc(ValueTypeNode::RunStep {
                    state_ty: self.zonk_value_type(environment, state_ty),
                    result_ty: self.zonk_value_type(environment, result_ty),
                }))
            }
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                self.solve_value(environment, context, output, result_ty)?;
                Ok(arena.alloc(ValueTypeNode::RunStep {
                    state_ty: self.zonk_value_type(environment, state_ty),
                    result_ty: self.zonk_value_type(environment, result_ty),
                }))
            }
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let expected_fields = environment
                    .crate_env
                    .program_inductive(indspec)
                    .constructors()
                    .get(idx)
                    .ok_or_else(|| "Program constructor index out of bounds".to_string())?
                    .instantiated_fields(arena, &parameters);
                if fields.len() != expected_fields.len() {
                    return Err("Program constructor field count mismatch".into());
                }
                for (field, (_, field_ty)) in fields.into_iter().zip(expected_fields) {
                    self.solve_value(environment, context, field, field_ty)?;
                }
                Ok(arena.alloc(ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|parameter| self.zonk_value_type(environment, parameter))
                        .collect(),
                }))
            }
        }
    }

    fn solve_computation(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let expected = self.zonk_computation_type(environment, expected);
        match arena.get(computation) {
            ComputationTermNode::Meta { .. } => Ok(()),
            ComputationTermNode::DefinedConstant(_) => {
                let inferred = self.infer_kernel_computation(environment, context, computation)?;
                self.unify_computation_types(environment, inferred, expected)
            }
            ComputationTermNode::Return { value } => {
                if let ComputationTypeNode::Return { value_ty } = arena.get(expected) {
                    self.solve_value(environment, context, value, value_ty)
                } else {
                    let value_ty = self.infer_value_term(environment, context, value)?;
                    let inferred = arena.alloc(ComputationTypeNode::Return { value_ty });
                    self.unify_computation_types(environment, inferred, expected)
                }
            }
            ComputationTermNode::Force { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let ValueTypeNode::Thunk { computation_ty } = arena.get(value_ty) else {
                    return Err("forced Program value is not a thunk".into());
                };
                self.unify_computation_types(environment, computation_ty, expected)
            }
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => {
                let ComputationTypeNode::Function { domain, codomain } = arena.get(expected) else {
                    let inferred =
                        self.infer_computation_term(environment, context, computation)?;
                    return self.unify_computation_types(environment, inferred, expected);
                };
                self.unify_value_types(environment, value_ty, domain)?;
                let domain = self.zonk_value_type(environment, domain);
                context.push(ProgramContextEntry::ValueTerm { var, ty: domain });
                let codomain = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, codomain, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, codomain);
                context.pop();
                result
            }
            ComputationTermNode::Application { computation, value } => {
                let function_ty = self.infer_computation_term(environment, context, computation)?;
                let function_ty = self.zonk_computation_type(environment, function_ty);
                let ComputationTypeNode::Function { domain, codomain } = arena.get(function_ty)
                else {
                    return Err("Program computation application head is not a function".into());
                };
                self.solve_value(environment, context, value, domain)?;
                self.unify_computation_types(environment, codomain, expected)
            }
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                self.solve_value(environment, context, value, value_ty)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let expected = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, expected, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, expected);
                context.pop();
                result
            }
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let first_ty = self.infer_computation_term(environment, context, computation)?;
                let first_ty = self.zonk_computation_type(environment, first_ty);
                let ComputationTypeNode::Return { value_ty: returned } = arena.get(first_ty) else {
                    return Err("Program sequence head does not return a value".into());
                };
                self.unify_value_types(environment, value_ty, returned)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let expected = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, expected, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, expected);
                context.pop();
                result
            }
            _ => {
                let inferred = self.infer_computation_term(environment, context, computation)?;
                self.unify_computation_types(environment, inferred, expected)
            }
        }
    }

    fn infer_computation_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        let arena = environment.crate_env.arena();
        match arena.get(computation) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramComputation { ty, .. } =
                    environment.crate_env.definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(
                    crate::raw::program_definitions::instantiate_computation_type(
                        arena,
                        *ty,
                        &parameters,
                        0,
                    ),
                )
            }
            ComputationTermNode::Meta { .. } => {
                Err("cannot infer an unconstrained Program computation metavariable".into())
            }
            ComputationTermNode::DefinedConstant(_) => {
                self.infer_kernel_computation(environment, context, computation)
            }
            ComputationTermNode::Return { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                Ok(arena.alloc(ComputationTypeNode::Return { value_ty }))
            }
            ComputationTermNode::Force { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let ValueTypeNode::Thunk { computation_ty } = arena.get(value_ty) else {
                    return Err("forced Program value is not a thunk".into());
                };
                Ok(computation_ty)
            }
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body_ty = self.infer_computation_term(environment, context, body);
                context.pop();
                Ok(arena.alloc(ComputationTypeNode::Function {
                    domain: value_ty,
                    codomain: strengthen_computation_type(arena, body_ty?, 0)
                        .ok_or("Program result type depends on a local value")?,
                }))
            }
            ComputationTermNode::Application { computation, value } => {
                let function_ty = self.infer_computation_term(environment, context, computation)?;
                let function_ty = self.zonk_computation_type(environment, function_ty);
                let ComputationTypeNode::Function { domain, codomain } = arena.get(function_ty)
                else {
                    return Err("Program computation application head is not a function".into());
                };
                self.solve_value(environment, context, value, domain)?;
                Ok(codomain)
            }
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                self.solve_value(environment, context, value, value_ty)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let result = self.infer_computation_term(environment, context, body);
                context.pop();
                strengthen_computation_type(arena, result?, 0)
                    .ok_or_else(|| "Program result type depends on a local value".into())
            }
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let first_ty = self.infer_computation_term(environment, context, computation)?;
                let first_ty = self.zonk_computation_type(environment, first_ty);
                let ComputationTypeNode::Return { value_ty: returned } = arena.get(first_ty) else {
                    return Err("Program sequence head does not return a value".into());
                };
                self.unify_value_types(environment, value_ty, returned)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let result = self.infer_computation_term(environment, context, body);
                context.pop();
                let mut result = result?;
                result = strengthen_computation_type(arena, result, 0)
                    .ok_or("Program result type depends on a local value")?;
                Ok(result)
            }
            _ => self.infer_kernel_computation(
                environment,
                context,
                self.zonk_computation(environment, computation),
            ),
        }
    }

    pub(crate) fn check_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(ValueTerm, ValueType), String> {
        let mut context = self.context.clone();
        self.solve_value(environment, &mut context, value, expected)?;
        self.finish_program_metas()?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, expected),
        ))
    }

    pub(crate) fn check_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(ComputationTerm, ComputationType), String> {
        let mut context = self.context.clone();
        self.solve_computation(environment, &mut context, computation, expected)?;
        self.finish_program_metas()?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, expected),
        ))
    }

    pub(crate) fn infer_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> Result<(ValueTerm, ValueType), String> {
        let mut context = self.context.clone();
        let ty = self.infer_value_term(environment, &mut context, value)?;
        self.finish_program_metas()?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, ty),
        ))
    }

    pub(crate) fn infer_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
    ) -> Result<(ComputationTerm, ComputationType), String> {
        let mut context = self.context.clone();
        let ty = self.infer_computation_term(environment, &mut context, computation)?;
        self.finish_program_metas()?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, ty),
        ))
    }
}
