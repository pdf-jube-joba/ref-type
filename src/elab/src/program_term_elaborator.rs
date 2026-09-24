//! Elaboration for the four disjoint Program syntactic categories.

use crate::{
    environment::DefinedConstant,
    ids::{MetaVarId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode,
        ProgramArgument, ProgramContext, ProgramContextEntry, ValueTerm, ValueTermNode, ValueType,
        ValueTypeNode,
    },
    program_calculus::strengthen_computation_type,
    program_derivation::ProgramCheckSession,
};
use crate::{resolver::ItemAccessResult, term_elaborator::LocalScope};
use hir::{
    AstId, ComputationTermExp, ComputationTermExpKind, ComputationTypeExp, ComputationTypeExpKind,
    LocalAccess, ProgramFunctionExp, ProgramFunctionExpKind, SurfaceMeta, ValueTermExp,
    ValueTermExpKind, ValueTypeExp, ValueTypeExpKind,
};

pub trait Handler: crate::term_elaborator::Handler {
    fn lookup_access(&self, access: &LocalAccess) -> Option<ItemAccessResult>;
    fn program_record(
        &self,
        id: crate::ids::ProgramInductiveId,
    ) -> Option<crate::resolver::ModItemProgramInductive>;
}

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
    origin: Option<AstId>,
    category: MetaCategory,
    spine: Vec<ProgramArgument>,
    solution: Option<MetaSolution>,
}

#[derive(Debug, Clone)]
pub struct ProgramScope {
    origins: Vec<Option<hir::AstId>>,
    context: ProgramContext,
    value_type_bindings: Vec<(SymbolId, ValueType)>,
    metas: Vec<ProgramMeta>,
    named_metas: HashMap<u32, MetaVarId>,
    has_runs: bool,
}

impl Default for ProgramScope {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramScope {
    fn associated_arguments(
        &mut self,
        environment: &mut impl Handler,
        parameters: &[ValueTypeExp],
        expected: usize,
    ) -> Result<Vec<ValueType>, String> {
        if parameters.is_empty() && expected > 0 {
            return (0..expected)
                .map(|_| {
                    self.elaborate_value_type(
                        &ValueTypeExpKind::Meta {
                            kind: SurfaceMeta::implicit(),
                            token: None,
                        }
                        .into(),
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
    pub fn new() -> Self {
        // Module parameters have stable identities and must not be captured as
        // de Bruijn locals: declarations and their uses can be nested beneath
        // different numbers of Program binders.
        Self {
            origins: Vec::new(),
            context: Vec::new(),
            value_type_bindings: Vec::new(),
            metas: Vec::new(),
            named_metas: HashMap::new(),
            has_runs: false,
        }
    }

    pub fn context(&self) -> &ProgramContext {
        &self.context
    }

    pub fn query_requires_checking(&self) -> bool {
        self.has_runs || !self.metas.is_empty()
    }

    pub fn finish_metas(&self, environment: &impl Handler) -> Result<(), String> {
        self.finish_program_metas(environment)
    }

    pub fn zonk_module_value_type(&self, environment: &impl Handler, ty: ValueType) -> ValueType {
        self.zonk_value_type(environment, ty)
    }

    pub fn zonk_module_value(&self, environment: &impl Handler, value: ValueTerm) -> ValueTerm {
        self.zonk_value(environment, value)
    }

    pub fn bind_value_type_name(&mut self, name: SymbolId, ty: ValueType) {
        self.value_type_bindings.push((name, ty));
    }

    pub fn push_type(&mut self, var: SymbolId, origin: Option<hir::AstId>) {
        self.origins.push(origin);
        self.context.push(ProgramContextEntry::ValueType { var });
    }

    fn push_value(&mut self, var: SymbolId, ty: ValueType, origin: Option<hir::AstId>) {
        self.origins.push(origin);
        self.context
            .push(ProgramContextEntry::ValueTerm { var, ty });
    }

    pub fn truncate(&mut self, len: usize) {
        self.origins.truncate(len);
        self.context.truncate(len);
    }

    fn local_index(
        &self,
        environment: &impl Handler,
        access: &LocalAccess,
    ) -> Option<(usize, ProgramContextEntry)> {
        let LocalAccess::Current { access } = access else {
            return None;
        };
        self.context
            .iter()
            .rev()
            .enumerate()
            .find_map(|(index, entry)| {
                let var = match entry {
                    ProgramContextEntry::ValueType { var }
                    | ProgramContextEntry::ValueTerm { var, .. } => *var,
                };
                if environment.env().symbol(var) != access.as_str() {
                    return None;
                }
                if let Some(origin) = self.origins[self.context.len() - index - 1] {
                    environment.record_local(access, origin);
                }
                Some((index, entry.clone()))
            })
    }

    fn item(
        &self,
        environment: &impl Handler,
        access: &LocalAccess,
    ) -> Result<ItemAccessResult, String> {
        environment
            .lookup_access(access)
            .ok_or_else(|| format!("Program name was not found: {access:?}"))
    }

    fn meta_spine(&self, environment: &impl Handler) -> Vec<ProgramArgument> {
        self.context
            .iter()
            .rev()
            .enumerate()
            .map(|(index, entry)| match entry {
                ProgramContextEntry::ValueType { .. } => {
                    ProgramArgument::ValueType(environment.env().arena().value_type_bound(index))
                }
                ProgramContextEntry::ValueTerm { .. } => {
                    ProgramArgument::ValueTerm(environment.env().arena().value_bound(index))
                }
            })
            .collect()
    }

    fn fresh_meta(
        &mut self,
        environment: &impl Handler,
        flavor: SurfaceMeta,
        origin: Option<AstId>,
        category: MetaCategory,
    ) -> Result<(MetaVarId, Vec<ProgramArgument>), String> {
        let spine = self.meta_spine(environment);
        let origin = origin.or_else(|| {
            Some(environment.env().sources.generated(
                environment.env().provenance.current_origin(),
                hir::GenerationReason::ImplicitType,
            ))
        });
        if let hir::MetaKind::Named(number) = flavor.kind
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
            origin,
            category,
            spine: spine.clone(),
            solution: None,
        });
        if let hir::MetaKind::Named(number) = flavor.kind {
            self.named_metas.insert(number, id);
        }
        Ok((id, spine))
    }

    pub fn elaborate_value_type(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut impl Handler,
    ) -> Result<ValueType, String> {
        let occurrence = environment
            .env()
            .provenance
            .enter(expression.origin, &environment.env().sources);
        let result = {
            self.elaborate_value_type_inner(expression, environment)
                .inspect_err(|_| {
                    environment.record_expression_error(expression.origin);
                })
        };
        environment.env().provenance.leave(
            occurrence,
            result.as_ref().ok().map(|term| (*term).into()),
            environment.arena(),
            &environment.env().sources,
        );
        result
    }

    fn elaborate_value_type_inner(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut impl Handler,
    ) -> Result<ValueType, String> {
        match &expression.kind {
            ValueTypeExpKind::Meta { kind, token } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *token, MetaCategory::ValueType)?;
                Ok(environment.env().arena().alloc(ValueTypeNode::Meta {
                    metavariable,
                    spine,
                }))
            }
            ValueTypeExpKind::Access { access, parameters } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.elaborate_value_type(parameter, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                let arena = environment.env().arena();
                if let LocalAccess::Current { access: name } = access
                    && let Some((_, ty)) = self
                        .value_type_bindings
                        .iter()
                        .rev()
                        .find(|(symbol, _)| environment.env().symbol(*symbol) == name.as_str())
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
                    _ => Err(format!(
                        "name does not denote a Program value type: '{access}'"
                    )),
                }
            }
            ValueTypeExpKind::Thunk(computation_ty) => {
                let computation_ty =
                    self.elaborate_computation_type(computation_ty, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ValueTypeNode::Thunk { computation_ty }))
            }
            ValueTypeExpKind::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                Ok(environment.env().arena().alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
        }
    }

    pub fn elaborate_computation_type(
        &mut self,
        expression: &ComputationTypeExp,
        environment: &mut impl Handler,
    ) -> Result<ComputationType, String> {
        let occurrence = environment
            .env()
            .provenance
            .enter(expression.origin, &environment.env().sources);
        let result = {
            self.elaborate_computation_type_inner(expression, environment)
                .inspect_err(|_| {
                    environment.record_expression_error(expression.origin);
                })
        };
        environment.env().provenance.leave(
            occurrence,
            result.as_ref().ok().map(|term| (*term).into()),
            environment.arena(),
            &environment.env().sources,
        );
        result
    }

    fn elaborate_computation_type_inner(
        &mut self,
        expression: &ComputationTypeExp,
        environment: &mut impl Handler,
    ) -> Result<ComputationType, String> {
        match &expression.kind {
            ComputationTypeExpKind::Meta { kind, token } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *token, MetaCategory::ComputationType)?;
                Ok(environment.env().arena().alloc(ComputationTypeNode::Meta {
                    metavariable,
                    spine,
                }))
            }
            ComputationTypeExpKind::Return(value_ty) => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTypeNode::Return { value_ty }))
            }
            ComputationTypeExpKind::Function { domain, codomain } => {
                let domain = self.elaborate_value_type(domain, environment)?;
                let codomain = self.elaborate_computation_type(codomain, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTypeNode::Function { domain, codomain }))
            }
        }
    }

    pub fn elaborate_value(
        &mut self,
        expression: &ValueTermExp,
        environment: &mut impl Handler,
    ) -> Result<ValueTerm, String> {
        let occurrence = environment
            .env()
            .provenance
            .enter(expression.origin, &environment.env().sources);
        let result = {
            self.elaborate_value_inner(expression, environment)
                .inspect_err(|_| {
                    environment.record_expression_error(expression.origin);
                })
        };
        environment.env().provenance.leave(
            occurrence,
            result.as_ref().ok().map(|term| (*term).into()),
            environment.arena(),
            &environment.env().sources,
        );
        result
    }

    fn elaborate_value_inner(
        &mut self,
        expression: &ValueTermExp,
        environment: &mut impl Handler,
    ) -> Result<ValueTerm, String> {
        let arena = environment.env().arena();
        match &expression.kind {
            ValueTermExpKind::Record {
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
                        .env()
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
                    .env()
                    .arena()
                    .alloc(ValueTermNode::InductiveConstructor {
                        indspec: item.inductive,
                        parameters,
                        idx: 0,
                        fields,
                    }))
            }
            ValueTermExpKind::Meta { kind, token } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *token, MetaCategory::ValueTerm)?;
                Ok(arena.alloc(ValueTermNode::Meta {
                    metavariable,
                    spine,
                }))
            }
            ValueTermExpKind::Access(access) => {
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
                        match environment.env().definition(item.definition) {
                            DefinedConstant::ProgramValue { .. } => {
                                Ok(arena.alloc(ValueTermNode::DefinedConstant(item.definition)))
                            }
                            _ => Err("definition is not a Program value".into()),
                        }
                    }
                    _ => Err(format!("name does not denote a Program value: '{access}'")),
                }
            }
            ValueTermExpKind::Constructor {
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
                        environment.env().definition(*definition),
                        DefinedConstant::ProgramValue { .. }
                    ) {
                        return Err("associated item is not a Program value".into());
                    }
                    let parameters = self.associated_arguments(
                        environment,
                        parameters,
                        environment.env().definition_parameters(*definition).len(),
                    )?;
                    return Ok(environment.env().arena().alloc(
                        ValueTermNode::DefinitionInstance {
                            definition: *definition,
                            parameters,
                        },
                    ));
                }
                if item.record_fields.is_some() {
                    if constructor.as_str() != "#" {
                        return Err(format!(
                            "Program associated item {} was not found",
                            constructor.as_str()
                        ));
                    }
                    let parameter_count = environment
                        .env()
                        .program_inductive(item.inductive)
                        .parameters()
                        .len();
                    let parameters =
                        self.associated_arguments(environment, parameters, parameter_count)?;
                    let fields = fields
                        .iter()
                        .map(|field| self.elaborate_value(field, environment))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(environment.env().arena().alloc(
                        ValueTermNode::InductiveConstructor {
                            indspec: item.inductive,
                            parameters,
                            idx: 0,
                            fields,
                        },
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
                    .env()
                    .arena()
                    .alloc(ValueTermNode::InductiveConstructor {
                        indspec: item.inductive,
                        parameters,
                        idx,
                        fields,
                    }))
            }
            ValueTermExpKind::Thunk(computation) => {
                let computation = self.elaborate_computation(computation, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ValueTermNode::Thunk { computation }))
            }
            ValueTermExpKind::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let next = self.elaborate_value(next, environment)?;
                Ok(environment.env().arena().alloc(ValueTermNode::Continue {
                    state_ty,
                    result_ty,
                    next,
                }))
            }
            ValueTermExpKind::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let output = self.elaborate_value(output, environment)?;
                Ok(environment.env().arena().alloc(ValueTermNode::Finish {
                    state_ty,
                    result_ty,
                    output,
                }))
            }
        }
    }

    pub fn elaborate_computation(
        &mut self,
        expression: &ComputationTermExp,
        environment: &mut impl Handler,
    ) -> Result<ComputationTerm, String> {
        let occurrence = environment
            .env()
            .provenance
            .enter(expression.origin, &environment.env().sources);
        let result = {
            self.elaborate_computation_inner(expression, environment)
                .inspect_err(|_| {
                    environment.record_expression_error(expression.origin);
                })
        };
        environment.env().provenance.leave(
            occurrence,
            result.as_ref().ok().map(|term| (*term).into()),
            environment.arena(),
            &environment.env().sources,
        );
        result
    }

    fn elaborate_computation_inner(
        &mut self,
        expression: &ComputationTermExp,
        environment: &mut impl Handler,
    ) -> Result<ComputationTerm, String> {
        match &expression.kind {
            ComputationTermExpKind::InferredProjection { value, field } => {
                let value = self.elaborate_value(value, environment)?;
                let mut context = self.context.clone();
                let value_ty = self.infer_kernel_value(environment, &mut context, value)?;
                let value_ty = self.resolve_value_type_head(environment, value_ty);
                let ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                } = environment.env().arena().get(value_ty)
                else {
                    return Err("Program field projection expects a record value".into());
                };
                let record = environment
                    .program_record(indspec)
                    .ok_or("Program field projection expects a record value")?;
                let (_, definition) = record
                    .associated_definitions
                    .iter()
                    .find(|(candidate, _)| candidate == field)
                    .ok_or_else(|| {
                        format!(
                            "Field {} not found in Program record {}",
                            field.as_str(),
                            record.type_name.as_str()
                        )
                    })?;
                if !matches!(
                    environment.env().definition(*definition),
                    DefinedConstant::ProgramComputation { .. }
                ) {
                    return Err("Program record projection is not a computation".into());
                }
                let projection =
                    environment
                        .env()
                        .arena()
                        .alloc(ComputationTermNode::DefinitionInstance {
                            definition: *definition,
                            parameters,
                        });
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Application {
                        computation: projection,
                        value,
                    }))
            }
            ComputationTermExpKind::Associated {
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
                    environment.env().definition(*definition),
                    DefinedConstant::ProgramComputation { .. }
                ) {
                    return Err("associated item is not a Program computation".into());
                }
                let parameters = self.associated_arguments(
                    environment,
                    parameters,
                    environment.env().definition_parameters(*definition).len(),
                )?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::DefinitionInstance {
                        definition: *definition,
                        parameters,
                    }))
            }
            ComputationTermExpKind::Meta { kind, token } => {
                let (metavariable, spine) =
                    self.fresh_meta(environment, *kind, *token, MetaCategory::ComputationTerm)?;
                Ok(environment.env().arena().alloc(ComputationTermNode::Meta {
                    metavariable,
                    spine,
                }))
            }
            ComputationTermExpKind::Access(access) => match self.item(environment, access)? {
                ItemAccessResult::Definition(item) => {
                    match environment.env().definition(item.definition) {
                        DefinedConstant::ProgramComputation { .. } => Ok(environment
                            .env()
                            .arena()
                            .alloc(ComputationTermNode::DefinedConstant(item.definition))),
                        _ => Err("definition is not a Program computation".into()),
                    }
                }
                _ => Err("name does not denote a Program computation".into()),
            },
            ComputationTermExpKind::Return(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Return { value }))
            }
            ComputationTermExpKind::Force(value) => {
                let value = self.elaborate_value(value, environment)?;
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Force { value }))
            }
            ComputationTermExpKind::Lambda {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let origin = var.origin();
                let var = environment.intern(var.as_str());
                let mark = self.context.len();
                self.push_value(var, value_ty, origin);
                let body = self.elaborate_computation(body, environment);
                self.truncate(mark);
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Lambda {
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationTermExpKind::Application {
                function,
                arguments,
            } => self.elaborate_application(function, arguments, environment),
            ComputationTermExpKind::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let computation = self.elaborate_computation(computation, environment)?;
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let origin = var.origin();
                let var = environment.intern(var.as_str());
                let mark = self.context.len();
                self.push_value(var, value_ty, origin);
                let body = self.elaborate_computation(body, environment);
                self.truncate(mark);
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Sequence {
                        computation,
                        var,
                        value_ty,
                        body: body?,
                    }))
            }
            ComputationTermExpKind::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let value_ty = self.elaborate_value_type(value_ty, environment)?;
                let value = self.elaborate_value(value, environment)?;
                let origin = var.origin();
                let var = environment.intern(var.as_str());
                let mark = self.context.len();
                self.push_value(var, value_ty, origin);
                let body = self.elaborate_computation(body, environment);
                self.truncate(mark);
                Ok(environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::ValueLet {
                        var,
                        value_ty,
                        value,
                        body: body?,
                    }))
            }
            ComputationTermExpKind::Case {
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
                let scrutinee_ty = ProgramCheckSession::new(environment.env(), &mut check_context)
                    .infer_value_term(scrutinee)
                    .map_err(|error| format!("cannot infer Program case scrutinee: {error:?}"))?;
                let ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                } = environment.env().arena().get(scrutinee_ty)
                else {
                    return Err("Program case scrutinee is not a Program datatype value".into());
                };
                if indspec != item.inductive {
                    return Err("Program case scrutinee datatype does not match its path".into());
                }
                let constructors = environment
                    .env()
                    .program_inductive(item.inductive)
                    .constructors()
                    .to_vec();
                let mut result = Vec::new();
                for (index, (constructor, binders, body)) in branches.iter().enumerate() {
                    if constructor != &item.ctor_names[index] {
                        return Err("Program case branches are not in constructor order".into());
                    }
                    let field_types = constructors[index]
                        .instantiated_fields(environment.env().arena(), &parameters);
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
                        let origin = binder.origin();
                        let binder = environment.intern(binder.as_str());
                        let ty = crate::program_calculus::shift_value_type_indices(
                            environment.env().arena(),
                            ty,
                            field_index,
                            0,
                        );
                        self.push_value(binder, ty, origin);
                        binder_ids.push(binder);
                    }
                    let body = self.elaborate_computation(body, environment);
                    self.truncate(mark);
                    result.push(crate::program::ProgramCaseBranch {
                        binders: binder_ids,
                        body: body?,
                    });
                }
                Ok(environment.env().arena().alloc(ComputationTermNode::Case {
                    indspec: item.inductive,
                    scrutinee,
                    branches: result,
                }))
            }
            ComputationTermExpKind::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                self.has_runs = true;
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let reflected_context =
                    crate::reflection::reflect_context(environment.env(), &self.context)
                        .map_err(|error| error.to_string())?;
                let accessibility =
                    LocalScope::from_typing_context(reflected_context, &self.origins)
                        .elab_exp(accessibility, environment)?;
                let computation = environment.env().arena().alloc(ComputationTermNode::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    accessibility,
                });
                Ok(computation)
            }
            ComputationTermExpKind::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                self.has_runs = true;
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let transition = self.elaborate_computation(transition, environment)?;
                let reflected_context =
                    crate::reflection::reflect_context(environment.env(), &self.context)
                        .map_err(|error| error.to_string())?;
                let mut proof_scope =
                    LocalScope::from_typing_context(reflected_context, &self.origins);
                let accessibility = proof_scope.elab_exp(accessibility, environment)?;
                let transition_equality = proof_scope.elab_exp(transition_equality, environment)?;
                let computation = environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::RunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                        accessibility,
                        transition_equality,
                    });
                Ok(computation)
            }
        }
    }

    fn elaborate_application(
        &mut self,
        function: &ProgramFunctionExp,
        arguments: &[ValueTermExp],
        environment: &mut impl Handler,
    ) -> Result<ComputationTerm, String> {
        enum Head {
            Value(Option<ValueType>),
            Computation(ComputationTerm, Option<ComputationType>),
        }

        let head = match &function.kind {
            ProgramFunctionExpKind::Value(value) => {
                let value = self.elaborate_value(value, environment)?;
                let mut context = self.context.clone();
                let ty = self.infer_value_term(environment, &mut context, value).ok();
                Head::Value(ty)
            }
            ProgramFunctionExpKind::Computation(computation) => {
                let computation = self.elaborate_computation(computation, environment)?;
                let mut context = self.context.clone();
                let ty = self
                    .infer_computation_term(environment, &mut context, computation)
                    .ok();
                Head::Computation(computation, ty)
            }
            ProgramFunctionExpKind::Access(access) => {
                if let Some((_index, entry)) = self.local_index(environment, access) {
                    let ProgramContextEntry::ValueTerm { ty, .. } = entry else {
                        return Err("Program type variable used as an application head".into());
                    };
                    Head::Value(Some(ty))
                } else {
                    match self.item(environment, access)? {
                        ItemAccessResult::ProgramValueParameter(id) => {
                            let ty = environment
                                .env()
                                .module_parameter_opt(id)
                                .and_then(|parameter| parameter.value_ty());
                            Head::Value(ty)
                        }
                        ItemAccessResult::Definition(item) => {
                            match environment.env().definition(item.definition) {
                                DefinedConstant::ProgramValue { ty, .. } => Head::Value(Some(*ty)),
                                DefinedConstant::ProgramComputation { ty, .. } => {
                                    Head::Computation(
                                        environment.env().arena().alloc(
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
            ProgramFunctionExpKind::Associated {
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
                let definition_ty = match environment.env().definition(definition) {
                    DefinedConstant::ProgramValue { ty, .. } => Ok(*ty),
                    DefinedConstant::ProgramComputation { ty, .. } => Err(*ty),
                    _ => return Err("associated Program item has the wrong category".into()),
                };
                match definition_ty {
                    Ok(ty) => {
                        let value = self.elaborate_value(
                            &ValueTermExpKind::Constructor {
                                datatype: datatype.clone(),
                                constructor: item.clone(),
                                parameters: parameters.clone(),
                                fields: Vec::new(),
                            }
                            .into(),
                            environment,
                        )?;
                        let ValueTermNode::DefinitionInstance { parameters, .. } =
                            environment.env().arena().get(value)
                        else {
                            unreachable!()
                        };
                        let ty = crate::program_definitions::instantiate_value_type(
                            environment.env().arena(),
                            ty,
                            &parameters,
                            0,
                        );
                        Head::Value(Some(ty))
                    }
                    Err(ty) => {
                        let computation = self.elaborate_computation(
                            &ComputationTermExpKind::Associated {
                                datatype: datatype.clone(),
                                item: item.clone(),
                                parameters: parameters.clone(),
                            }
                            .into(),
                            environment,
                        )?;
                        let ComputationTermNode::DefinitionInstance { parameters, .. } =
                            environment.env().arena().get(computation)
                        else {
                            unreachable!()
                        };
                        let ty = crate::program_definitions::instantiate_computation_type(
                            environment.env().arena(),
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
        let (mut computation, mut computation_ty) = match head {
            Head::Computation(computation, ty) => (computation, ty),
            Head::Value(Some(ty)) => {
                let ty = self.resolve_value_type_head(environment, ty);
                return match environment.env().arena().get(ty) {
                    ValueTypeNode::Thunk { .. } | ValueTypeNode::Meta { .. } => Err(
                        "Program function values require an explicit \\force before application"
                            .into(),
                    ),
                    _ => Err("Program application head value is not a function thunk".into()),
                };
            }
            Head::Value(None) => {
                return Err(
                    "cannot determine the type of Program function value; add a type annotation"
                        .into(),
                );
            }
        };

        for argument in arguments {
            let Some(ty) = computation_ty else {
                computation = environment
                    .env()
                    .arena()
                    .alloc(ComputationTermNode::Application {
                        computation,
                        value: argument,
                    });
                continue;
            };
            let ty = self.resolve_computation_type_head(environment, ty);
            match environment.env().arena().get(ty) {
                ComputationTypeNode::Function { codomain, .. } => {
                    computation =
                        environment
                            .env()
                            .arena()
                            .alloc(ComputationTermNode::Application {
                                computation,
                                value: argument,
                            });
                    computation_ty = Some(codomain);
                }
                ComputationTypeNode::Return { value_ty } => {
                    let value_ty = self.resolve_value_type_head(environment, value_ty);
                    if matches!(
                        environment.env().arena().get(value_ty),
                        ValueTypeNode::Thunk { .. }
                    ) {
                        return Err(
                            "Program computation returned a function value; use explicit \\bind and \\force before applying another argument"
                                .into(),
                        );
                    }
                    // Preserve raw ill-typed applications for checking and evaluation
                    // commands. This path inserts no sequencing construct.
                    computation =
                        environment
                            .env()
                            .arena()
                            .alloc(ComputationTermNode::Application {
                                computation,
                                value: argument,
                            });
                    computation_ty = None;
                }
                ComputationTypeNode::Meta { .. } => {
                    computation =
                        environment
                            .env()
                            .arena()
                            .alloc(ComputationTermNode::Application {
                                computation,
                                value: argument,
                            });
                    computation_ty = None;
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
    fn resolve_value_type_head(&self, environment: &impl Handler, mut ty: ValueType) -> ValueType {
        while let ValueTypeNode::Meta { metavariable, .. } = environment.env().arena().get(ty) {
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
        environment: &impl Handler,
        mut ty: ComputationType,
    ) -> ComputationType {
        while let ComputationTypeNode::Meta { metavariable, .. } = environment.env().arena().get(ty)
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

    fn zonk_value_type(&self, environment: &impl Handler, ty: ValueType) -> ValueType {
        let result = self.zonk_value_type_inner(environment, ty);
        environment.env().provenance.relate(ty, result);
        result
    }
    fn zonk_value_type_inner(&self, environment: &impl Handler, ty: ValueType) -> ValueType {
        let arena = environment.env().arena();
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
        environment: &impl Handler,
        ty: ComputationType,
    ) -> ComputationType {
        let result = self.zonk_computation_type_inner(environment, ty);
        environment.env().provenance.relate(ty, result);
        result
    }
    fn zonk_computation_type_inner(
        &self,
        environment: &impl Handler,
        ty: ComputationType,
    ) -> ComputationType {
        let arena = environment.env().arena();
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
        environment: &impl Handler,
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

    fn zonk_value(&self, environment: &impl Handler, value: ValueTerm) -> ValueTerm {
        let result = self.zonk_value_inner(environment, value);
        environment.env().provenance.relate(value, result);
        result
    }
    fn zonk_value_inner(&self, environment: &impl Handler, value: ValueTerm) -> ValueTerm {
        let arena = environment.env().arena();
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
        environment: &impl Handler,
        computation: ComputationTerm,
    ) -> ComputationTerm {
        let result = self.zonk_computation_inner(environment, computation);
        environment.env().provenance.relate(computation, result);
        result
    }
    fn zonk_computation_inner(
        &self,
        environment: &impl Handler,
        computation: ComputationTerm,
    ) -> ComputationTerm {
        let arena = environment.env().arena();
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
                    .map(|branch| crate::program::ProgramCaseBranch {
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
                accessibility,
            } => arena.alloc(ComputationTermNode::Run {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                step: self.zonk_value(environment, step),
                initial: self.zonk_value(environment, initial),
                accessibility,
            }),
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => arena.alloc(ComputationTermNode::RunCase {
                state_ty: self.zonk_value_type(environment, state_ty),
                result_ty: self.zonk_value_type(environment, result_ty),
                step: self.zonk_value(environment, step),
                initial: self.zonk_value(environment, initial),
                transition: self.zonk_computation(environment, transition),
                accessibility,
                transition_equality,
            }),
            _ => computation,
        }
    }

    fn value_type_occurs(
        &self,
        environment: &impl Handler,
        needle: MetaVarId,
        ty: ValueType,
    ) -> bool {
        let ty = self.zonk_value_type(environment, ty);
        match environment.env().arena().get(ty) {
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
        environment: &impl Handler,
        needle: MetaVarId,
        ty: ComputationType,
    ) -> bool {
        let ty = self.zonk_computation_type(environment, ty);
        match environment.env().arena().get(ty) {
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
        environment: &impl Handler,
        left: ValueType,
        right: ValueType,
    ) -> Result<(), String> {
        let arena = environment.env().arena();
        let left = self.zonk_value_type(environment, left);
        let right = self.zonk_value_type(environment, right);
        if crate::program_calculus::value_type_is_alpha_eq(arena, left, right) {
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
        environment: &impl Handler,
        left: ComputationType,
        right: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.env().arena();
        let left = self.zonk_computation_type(environment, left);
        let right = self.zonk_computation_type(environment, right);
        if crate::program_calculus::computation_type_is_alpha_eq(arena, left, right) {
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

    fn finish_program_metas(&self, environment: &impl Handler) -> Result<(), String> {
        let unsolved = self
            .metas
            .iter()
            .filter(|meta| meta.solution.is_none())
            .collect::<Vec<_>>();
        if unsolved.is_empty() {
            return Ok(());
        }
        let meta = unsolved[0];
        let name = match meta.flavor.kind {
            hir::MetaKind::Implicit => "_".to_string(),
            hir::MetaKind::Goal => "?".to_string(),
            hir::MetaKind::Named(number) => format!("?{number}"),
        };
        environment.record_expression_error(meta.origin);
        Err(format!(
            "unsolved Program metavariable {name} in {:?} syntax",
            meta.category
        ))
    }

    fn infer_kernel_value(
        &self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        ProgramCheckSession::new(environment.env(), context)
            .infer_value_term(value)
            .map_err(|error| format!("cannot infer Program value: {error:?}"))
    }

    fn infer_kernel_computation(
        &self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        ProgramCheckSession::new(environment.env(), context)
            .infer_computation_term(computation)
            .map_err(|error| format!("cannot infer Program computation: {error:?}"))
    }

    fn solve_value(
        &mut self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        environment.env().provenance.check(value, || {
            self.solve_value_inner(environment, context, value, expected)
        })
    }
    fn solve_value_inner(
        &mut self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        let arena = environment.env().arena();
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
                    .env()
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
        environment: &impl Handler,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        environment.env().provenance.check(value, || {
            self.infer_value_term_inner(environment, context, value)
        })
    }
    fn infer_value_term_inner(
        &mut self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        let arena = environment.env().arena();
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramValue { ty, .. } =
                    environment.env().definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(crate::program_definitions::instantiate_value_type(
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
                    .env()
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
        environment: &impl Handler,
        context: &mut ProgramContext,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        environment.env().provenance.check(computation, || {
            self.solve_computation_inner(environment, context, computation, expected)
        })
    }
    fn solve_computation_inner(
        &mut self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.env().arena();
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
                let codomain =
                    crate::program_calculus::shift_computation_type_indices(arena, codomain, 1, 0);
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
                let expected =
                    crate::program_calculus::shift_computation_type_indices(arena, expected, 1, 0);
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
                let expected =
                    crate::program_calculus::shift_computation_type_indices(arena, expected, 1, 0);
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
        environment: &impl Handler,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        environment.env().provenance.check(computation, || {
            self.infer_computation_term_inner(environment, context, computation)
        })
    }
    fn infer_computation_term_inner(
        &mut self,
        environment: &impl Handler,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        let arena = environment.env().arena();
        match arena.get(computation) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramComputation { ty, .. } =
                    environment.env().definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(crate::program_definitions::instantiate_computation_type(
                    arena,
                    *ty,
                    &parameters,
                    0,
                ))
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

    pub fn check_value_term_with_metas(
        &mut self,
        environment: &impl Handler,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(ValueTerm, ValueType), String> {
        let mut context = self.context.clone();
        self.solve_value(environment, &mut context, value, expected)?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, expected),
        ))
    }

    pub fn check_computation_term_with_metas(
        &mut self,
        environment: &impl Handler,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(ComputationTerm, ComputationType), String> {
        let mut context = self.context.clone();
        self.solve_computation(environment, &mut context, computation, expected)?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, expected),
        ))
    }

    pub fn infer_value_term_with_metas(
        &mut self,
        environment: &impl Handler,
        value: ValueTerm,
    ) -> Result<(ValueTerm, ValueType), String> {
        let mut context = self.context.clone();
        let ty = self.infer_value_term(environment, &mut context, value)?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, ty),
        ))
    }

    pub fn infer_computation_term_with_metas(
        &mut self,
        environment: &impl Handler,
        computation: ComputationTerm,
    ) -> Result<(ComputationTerm, ComputationType), String> {
        let mut context = self.context.clone();
        let ty = self.infer_computation_term(environment, &mut context, computation)?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, ty),
        ))
    }
}
