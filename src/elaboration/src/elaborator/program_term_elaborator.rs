//! Elaboration for the four disjoint Program syntactic categories.
use crate::{
    elaborator::{
        GlobalEnvironment, module_manager::ItemAccessResult, term_elaborator::LocalScope,
    },
    hir::{
        ComputationTermExp, ComputationTypeExp, LocalAccess, ProgramFunctionExp, SExp, SourceSpan,
        SurfaceMeta, ValueTermExp, ValueTypeExp,
    },
    metavariables::{
        ConstraintDiagnostic, ConstraintStatus, ElaborationError, MetaFlavor, MetaGoal, MetaState,
    },
    raw::{
        environment::DefinedConstant,
        exp::Arena,
        ids::{MetaVarId, SymbolId},
        printing::Printer,
        program::{
            ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode,
            ProgramArgument, ProgramContext, ProgramContextEntry, ValueTerm, ValueTermNode,
            ValueType, ValueTypeNode,
        },
        program_derivation::ProgramCheckSession,
        traversal::Term,
    },
};
use std::collections::{HashMap, HashSet};
mod inference;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetaCategory {
    ValueType,
    ComputationType,
    ValueTerm,
    ComputationTerm,
}

#[derive(Debug, Clone)]
struct ProgramMeta {
    flavor: MetaFlavor,
    span: SourceSpan,
    occurrences: Vec<SourceSpan>,
    category: MetaCategory,
    context: ProgramContext,
    solution: Option<Term>,
    expected: Option<Term>,
}

#[derive(Debug, Clone)]
enum ProgramConstraint {
    #[allow(dead_code)] // Retained for explicit solver diagnostics and debug tests.
    Equal(Term, Term),
    HasType(Term, Term),
}
#[derive(Debug, Clone)]
struct ProgramConstraintRecord {
    constraint: ProgramConstraint,
    status: ConstraintStatus,
    origins: Vec<SourceSpan>,
}

#[derive(Debug)]
pub(crate) struct ProgramScope {
    core: kernel::metavariables::MetaContext,
    core_ids: Vec<kernel::syntax::MetaId>,
    ids: HashMap<kernel::syntax::MetaId, MetaVarId>,
    names: Vec<SymbolId>,
    context: ProgramContext,
    value_type_bindings: Vec<(SymbolId, ValueType)>,
    metas: Vec<ProgramMeta>,
    named_metas: HashMap<u32, MetaVarId>,
    sources: HashMap<Term, Vec<SourceSpan>>,
    has_runs: bool,
    constraints: Vec<ProgramConstraintRecord>,
    origins: Vec<SourceSpan>,
}

impl Default for ProgramScope {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramScope {
    fn diagnostic_snapshot(&self) -> Self {
        Self {
            core: self.core.diagnostic_snapshot(),
            core_ids: self.core_ids.clone(),
            ids: self.ids.clone(),
            metas: self.metas.clone(),
            constraints: self.constraints.clone(),
            ..Self::new()
        }
    }

    fn associated_arguments(
        &mut self,
        environment: &mut GlobalEnvironment,
        parameters: &[ValueTypeExp],
        expected: usize,
    ) -> Result<Vec<ValueType>, ElaborationError> {
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
            )
            .into());
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
            core: Default::default(),
            core_ids: vec![],
            ids: HashMap::new(),
            names: Vec::new(),
            context: Vec::new(),
            value_type_bindings: Vec::new(),
            metas: Vec::new(),
            named_metas: HashMap::new(),
            sources: HashMap::new(),
            has_runs: false,
            constraints: Vec::new(),
            origins: Vec::new(),
        }
    }

    pub(crate) fn context(&self) -> &ProgramContext {
        &self.context
    }

    pub(crate) fn query_requires_checking(&self) -> bool {
        self.has_runs || !self.metas.is_empty()
    }

    pub(crate) fn finish_metas(
        &mut self,
        environment: &GlobalEnvironment,
    ) -> Result<(), ElaborationError> {
        self.finish_program_metas(environment)
    }

    pub(crate) fn zonk_module_value_type(
        &self,
        environment: &GlobalEnvironment,
        ty: ValueType,
    ) -> ValueType {
        self.zonk_value_type(environment, ty)
    }

    pub(crate) fn zonk_module_computation(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationTerm,
    ) -> ComputationTerm {
        self.zonk_computation(environment, value)
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
        let (LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. }) = access
        else {
            return None;
        };
        self.names
            .iter()
            .rev()
            .enumerate()
            .find_map(|(index, symbol)| {
                (environment.crate_env.name_matches(*symbol, access))
                    .then(|| (index, self.context[self.context.len() - index - 1].clone()))
            })
    }

    fn item(
        &self,
        environment: &GlobalEnvironment,
        access: &LocalAccess,
    ) -> Result<ItemAccessResult, ElaborationError> {
        Ok(environment
            .module_manager
            .get_item(&environment.crate_env, access)
            .ok_or_else(|| format!("Program name was not found: {access}"))?)
    }

    fn record_source(&mut self, environment: &GlobalEnvironment, term: Term, span: SourceSpan) {
        self.sources.entry(term).or_default().push(span);
        for id in inference::metas(environment.crate_env.arena(), term) {
            let meta = &mut self.metas[id.index()];
            if meta.span == SourceSpan::default() {
                meta.span = span;
                meta.occurrences = vec![span];
            }
        }
    }

    pub(crate) fn check_member(
        &mut self,
        value: &SExp,
        ty: &SExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<(), ElaborationError> {
        if let SExp::ModuleInstance { path, import_name } = value {
            let context =
                crate::raw::reflection::reflect_context(&environment.crate_env, &self.context)
                    .map_err(|error| error.to_string())?;
            let mut scope = LocalScope::from_typing_context(context);
            let binding = environment.instantiate_module_expression(path, &mut scope, self)?;
            environment.module_manager.register_hir_import(
                &environment.crate_env,
                import_name,
                binding,
            );
            return Ok(());
        }
        if let SExp::ConversionTarget { expression } = ty {
            if let (Ok(left), Ok(right)) = (
                ValueTypeExp::try_from(value.clone()),
                ValueTypeExp::try_from((**expression).clone()),
            ) && let (Ok(left), Ok(right)) = (
                self.elaborate_value_type(&left, environment),
                self.elaborate_value_type(&right, environment),
            ) {
                self.check_value_type_with_metas(environment, left)?;
                self.check_value_type_with_metas(environment, right)?;
                self.unify_terms(environment, Term::ValueType(left), Term::ValueType(right))?;
            } else {
                let context =
                    crate::raw::reflection::reflect_context(&environment.crate_env, &self.context)
                        .map_err(|error| error.to_string())?;
                let mut scope = LocalScope::from_typing_context(context.clone());
                let left = scope.elab_exp(value, environment)?;
                let right = scope.elab_exp(expression, environment)?;
                scope.infer_elaborated(left, environment)?;
                scope.infer_elaborated(right, environment)?;
                super::term_elaborator::Handler::unify(environment, &context, left, right)?;
            }
        } else if matches!(ty, SExp::ValueType) {
            let syntax: ValueTypeExp = value.clone().try_into()?;
            let ty = self.elaborate_value_type(&syntax, environment)?;
            self.check_value_type_with_metas(environment, ty)?;
        } else if let Ok(syntax) = ValueTypeExp::try_from(ty.clone())
            && let Ok(expected) = self.elaborate_value_type(&syntax, environment)
        {
            let syntax: ValueTermExp = value.clone().try_into()?;
            let value = self.elaborate_value(&syntax, environment)?;
            self.check_value_term_with_metas(environment, value, expected)?;
        } else if let Ok(syntax) = ComputationTypeExp::try_from(ty.clone())
            && let Ok(expected) = self.elaborate_computation_type(&syntax, environment)
        {
            let syntax: ComputationTermExp = value.clone().try_into()?;
            let value = self.elaborate_computation_expected(&syntax, expected, environment)?;
            self.check_computation_term_with_metas(environment, value, expected)?;
        } else {
            let context =
                crate::raw::reflection::reflect_context(&environment.crate_env, &self.context)
                    .map_err(|error| error.to_string())?;
            let mut scope = LocalScope::from_typing_context(context);
            let checked = SExp::Ascribe {
                term: Box::new(value.clone()),
                ty: Box::new(ty.clone()),
            };
            let value = scope.elab_exp(&checked, environment)?;
            scope.infer_elaborated(value, environment)?;
        }
        Ok(())
    }

    pub(crate) fn elaborate_value_type(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueType, ElaborationError> {
        let value = self.elaborate_value_type_inner(expression, environment)?;
        let span = match expression {
            ValueTypeExp::Meta { span, .. } => Some(*span),
            ValueTypeExp::Access { access, .. } => Some(access.span()),
            _ => None,
        };
        if let Some(span) = span {
            self.record_source(environment, Term::ValueType(value), span);
        }
        Ok(value)
    }

    fn elaborate_value_type_inner(
        &mut self,
        expression: &ValueTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueType, ElaborationError> {
        match expression {
            ValueTypeExp::Deferred { .. } => Err("unresolved frontend declaration".into()),
            ValueTypeExp::Checked { checks, body } => {
                for (value, ty) in checks {
                    self.check_member(value, ty, environment)?;
                }
                self.elaborate_value_type_inner(body, environment)
            }
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
                if let LocalAccess::Current { access: name, .. }
                | LocalAccess::Resolved { access: name, .. } = access
                    && let Some((_, ty)) = self
                        .value_type_bindings
                        .iter()
                        .rev()
                        .find(|(symbol, _)| environment.crate_env.name_matches(*symbol, name))
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
                    ItemAccessResult::Argument(
                        crate::raw::environment::ModuleArgument::ProgramType(ty),
                    ) if parameters.is_empty() => Ok(ty),
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
                    _ => {
                        Err(format!("name does not denote a Program value type: '{access}'").into())
                    }
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
    ) -> Result<ComputationType, ElaborationError> {
        let value = self.elaborate_computation_type_inner(expression, environment)?;
        let span = match expression {
            ComputationTypeExp::Meta { span, .. } => Some(*span),

            _ => None,
        };
        if let Some(span) = span {
            self.record_source(environment, Term::ComputationType(value), span);
        }
        Ok(value)
    }

    fn elaborate_computation_type_inner(
        &mut self,
        expression: &ComputationTypeExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationType, ElaborationError> {
        match expression {
            ComputationTypeExp::Deferred { .. } => Err("unresolved frontend declaration".into()),
            ComputationTypeExp::Checked { checks, body } => {
                for (value, ty) in checks {
                    self.check_member(value, ty, environment)?;
                }
                self.elaborate_computation_type_inner(body, environment)
            }
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
    ) -> Result<ValueTerm, ElaborationError> {
        let value = self.elaborate_value_inner(expression, environment)?;
        let span = match expression {
            ValueTermExp::Meta { span, .. } => Some(*span),
            ValueTermExp::Reference { access } | ValueTermExp::Access(access) => {
                Some(access.span())
            }
            ValueTermExp::Constructor { span, .. } => Some(*span),
            _ => None,
        };
        if let Some(span) = span {
            self.record_source(environment, Term::Value(value), span);
        }
        Ok(value)
    }

    fn elaborate_value_inner(
        &mut self,
        expression: &ValueTermExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ValueTerm, ElaborationError> {
        let arena = environment.crate_env.arena();
        match expression {
            ValueTermExp::Deferred { .. } => Err("unresolved frontend value declaration".into()),
            ValueTermExp::Checked { checks, body } => {
                for (value, ty) in checks {
                    self.check_member(value, ty, environment)?;
                }
                self.elaborate_value_inner(body, environment)
            }
            ValueTermExp::Ascribe { term, ty } => {
                let ty = self.elaborate_value_type(ty, environment)?;
                let term = self.elaborate_value(term, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ValueTermNode::Ascribe { term, ty }))
            }
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
                        )
                        .into());
                    }
                    if !names.contains(name) {
                        return Err(format!("Unknown structure field {}", name.as_str()).into());
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
                    .collect::<Result<Vec<_>, ElaborationError>>()?;
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
            ValueTermExp::Reference { access } | ValueTermExp::Access(access) => {
                if let Some((index, entry)) = self.local_index(environment, access) {
                    return match entry {
                        ProgramContextEntry::ValueTerm { .. } => Ok(arena.value_bound(index)),
                        ProgramContextEntry::ValueType { .. } => {
                            Err("Program type variable used as a value".into())
                        }
                    };
                }
                match self.item(environment, access)? {
                    ItemAccessResult::Argument(
                        crate::raw::environment::ModuleArgument::ProgramValue(value),
                    ) => Ok(value),
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
                    _ => Err(format!("name does not denote a Program value: '{access}'").into()),
                }
            }
            ValueTermExp::Constructor {
                span,
                datatype,
                constructor,
                parameters,
                fields,
            } => {
                environment.module_manager.record_associated_reference(
                    &environment.crate_env,
                    datatype,
                    constructor,
                    *span,
                );
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
                    if constructor.as_str() != "#" {
                        return Err(format!(
                            "Program associated item {} was not found",
                            constructor.as_str()
                        )
                        .into());
                    }
                    let parameter_count = environment
                        .crate_env
                        .program_inductive(item.inductive)
                        .parameters()
                        .len();
                    let parameters =
                        self.associated_arguments(environment, parameters, parameter_count)?;
                    let fields = fields
                        .iter()
                        .map(|field| self.elaborate_value(field, environment))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(environment.crate_env.arena().alloc(
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
                    )
                    .into());
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

    pub(crate) fn elaborate_computation_expected(
        &mut self,
        expression: &ComputationTermExp,
        expected: ComputationType,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, ElaborationError> {
        if let ComputationTermExp::Checked { checks, body } = expression {
            for (value, ty) in checks {
                self.check_member(value, ty, environment)?;
            }
            return self.elaborate_computation_expected(body, expected, environment);
        }
        let expected = self.resolve_computation_type_head(environment, expected);
        if let ComputationTermExp::Lambda {
            var,
            value_ty,
            body,
        } = expression
            && let ComputationTypeNode::Function { domain, codomain } =
                environment.crate_env.arena().get(expected)
        {
            let annotation = self.elaborate_value_type(value_ty, environment)?;
            self.unify_terms(
                environment,
                Term::ValueType(annotation),
                Term::ValueType(domain),
            )?;
            let value_ty = self.zonk_value_type(environment, domain);
            let var = environment.crate_env.intern_name(var);
            self.names.push(var);
            self.context
                .push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
            let Term::ComputationType(codomain) =
                Term::ComputationType(codomain).shift(environment.crate_env.arena(), 1, 0)
            else {
                unreachable!()
            };
            let body = self.elaborate_computation_expected(body, codomain, environment);
            self.names.pop();
            self.context.pop();
            return Ok(environment
                .crate_env
                .arena()
                .alloc(ComputationTermNode::Lambda {
                    var,
                    value_ty,
                    body: body?,
                }));
        }
        self.elaborate_computation(expression, environment)
    }

    pub(crate) fn elaborate_computation(
        &mut self,
        expression: &ComputationTermExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, ElaborationError> {
        let value = self.elaborate_computation_inner(expression, environment)?;
        let span = match expression {
            ComputationTermExp::Meta { span, .. } => Some(*span),
            ComputationTermExp::Access(access) => Some(access.span()),
            ComputationTermExp::Associated { span, .. } => Some(*span),
            _ => None,
        };
        if let Some(span) = span {
            self.record_source(environment, Term::Computation(value), span);
        }
        Ok(value)
    }

    fn elaborate_computation_inner(
        &mut self,
        expression: &ComputationTermExp,
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, ElaborationError> {
        match expression {
            ComputationTermExp::Deferred { .. } => Err("unresolved frontend declaration".into()),
            ComputationTermExp::Checked { checks, body } => {
                for (value, ty) in checks {
                    self.check_member(value, ty, environment)?;
                }
                self.elaborate_computation_inner(body, environment)
            }
            ComputationTermExp::Ascribe { term, ty } => {
                let ty = self.elaborate_computation_type(ty, environment)?;
                let term = self.elaborate_computation_expected(term, ty, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Ascribe { term, ty }))
            }
            ComputationTermExp::InferredProjection { value, field, .. } => {
                let value = self.elaborate_value(value, environment)?;
                let mut context = self.context.clone();
                let value_ty = self.infer_kernel_value(environment, &mut context, value)?;
                let value_ty = self.resolve_value_type_head(environment, value_ty);
                let ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                } = environment.crate_env.arena().get(value_ty)
                else {
                    return Err("Program field projection expects a record value".into());
                };
                let record = environment
                    .module_manager
                    .get_moditem_program_record(&environment.crate_env, indspec)
                    .ok_or("Program field projection expects a record value")?;
                let (_, definition) = record
                    .associated_definitions
                    .iter()
                    .find(|(candidate, _)| candidate.as_str() == field.as_str())
                    .ok_or_else(|| {
                        format!(
                            "Field {} not found in Program record {}",
                            field.as_str(),
                            record.type_name.as_str()
                        )
                    })?;
                if !matches!(
                    environment.crate_env.definition(*definition),
                    DefinedConstant::ProgramComputation { .. }
                ) {
                    return Err("Program record projection is not a computation".into());
                }
                let projection =
                    environment
                        .crate_env
                        .arena()
                        .alloc(ComputationTermNode::DefinitionInstance {
                            definition: *definition,
                            parameters,
                        });
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Application {
                        computation: projection,
                        value,
                    }))
            }
            ComputationTermExp::Associated {
                span,
                datatype,
                item: name,
                parameters,
            } => {
                environment.module_manager.record_associated_reference(
                    &environment.crate_env,
                    datatype,
                    name,
                    *span,
                );
                let ItemAccessResult::ProgramInductive(item) = self.item(environment, datatype)?
                else {
                    return Err("expected Program type before associated access".into());
                };
                let (_, definition) = item
                    .associated_definitions
                    .iter()
                    .find(|(candidate, _)| candidate.as_str() == name.as_str())
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
                let var = environment.crate_env.intern_name(var);
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
                let expected = environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTypeNode::Return { value_ty });
                self.solve_computation(
                    environment,
                    &mut self.context.clone(),
                    computation,
                    expected,
                )
                .map_err(|message| self.solver_error(environment, message))?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let var = environment.crate_env.intern_name(var);
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
                self.solve_value(environment, &mut self.context.clone(), value, value_ty)
                    .map_err(|message| self.solver_error(environment, message))?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let var = environment.crate_env.intern_name(var);
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
                        .map_err(|error| format!("cannot infer Program case scrutinee: {error}"))?;
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
                        )
                        .into());
                    }
                    let mark = self.context.len();
                    let mut binder_ids = Vec::new();
                    for (field_index, (binder, (_, ty))) in
                        binders.iter().zip(field_types).enumerate()
                    {
                        let binder = environment.crate_env.intern_name(binder);
                        let ty = crate::kernel_bridge::shift_value_type_indices(
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
            ComputationTermExp::StepMatch {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let computation_ty =
                    self.elaborate_computation_type(computation_ty, environment)?;
                let on_continue = self.elaborate_computation(on_continue, environment)?;
                let on_finish = self.elaborate_computation(on_finish, environment)?;
                let scrutinee = self.elaborate_value(scrutinee, environment)?;
                Ok(environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::StepMatch {
                        state_ty,
                        result_ty,
                        computation_ty,
                        on_continue,
                        on_finish,
                        scrutinee,
                    }))
            }
            ComputationTermExp::Run {
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
                    crate::raw::reflection::reflect_context(&environment.crate_env, &self.context)
                        .map_err(|error| error.to_string())?;
                let mut proof_scope = LocalScope::from_typing_context(reflected_context);
                let accessibility = proof_scope.elab_exp(accessibility, environment)?;
                proof_scope.infer_elaborated(accessibility, environment)?;
                environment.finish_metavariables()?;
                let accessibility = environment
                    .metavariables
                    .zonk(&environment.crate_env, accessibility);
                let computation = environment
                    .crate_env
                    .arena()
                    .alloc(ComputationTermNode::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        accessibility,
                    });
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
                self.has_runs = true;
                let state_ty = self.elaborate_value_type(state_ty, environment)?;
                let result_ty = self.elaborate_value_type(result_ty, environment)?;
                let step = self.elaborate_value(step, environment)?;
                let initial = self.elaborate_value(initial, environment)?;
                let transition = self.elaborate_computation(transition, environment)?;
                let reflected_context =
                    crate::raw::reflection::reflect_context(&environment.crate_env, &self.context)
                        .map_err(|error| error.to_string())?;
                let mut proof_scope = LocalScope::from_typing_context(reflected_context);
                let accessibility = proof_scope.elab_exp(accessibility, environment)?;
                let transition_equality = proof_scope.elab_exp(transition_equality, environment)?;
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
        environment: &mut GlobalEnvironment,
    ) -> Result<ComputationTerm, ElaborationError> {
        enum Head {
            Value(Option<ValueType>),
            Computation(ComputationTerm, Option<ComputationType>),
        }

        let head = match function {
            ProgramFunctionExp::Value(value) => {
                let value = self.elaborate_value(value, environment)?;
                let mut context = self.context.clone();
                let ty = self.infer_value_term(environment, &mut context, value).ok();
                Head::Value(ty)
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
                if let Some((_index, entry)) = self.local_index(environment, access) {
                    let ProgramContextEntry::ValueTerm { ty, .. } = entry else {
                        return Err("Program type variable used as an application head".into());
                    };
                    Head::Value(Some(ty))
                } else {
                    match self.item(environment, access)? {
                        ItemAccessResult::ProgramValueParameter(id) => {
                            let ty = environment
                                .crate_env
                                .module_parameter_opt(id)
                                .and_then(|parameter| parameter.value_ty());
                            Head::Value(ty)
                        }
                        ItemAccessResult::Definition(item) => {
                            match environment.crate_env.definition(item.definition) {
                                DefinedConstant::ProgramValue { ty, .. } => Head::Value(Some(*ty)),
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
                span,
                datatype,
                item,
                parameters,
            } => {
                environment.module_manager.record_associated_reference(
                    &environment.crate_env,
                    datatype,
                    item,
                    *span,
                );
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
                                span: *span,
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
                        let ty = crate::kernel_bridge::instantiate_value_type_parameters(
                            environment.crate_env.arena(),
                            ty,
                            &parameters,
                            0,
                        );
                        Head::Value(Some(ty))
                    }
                    Err(ty) => {
                        let computation = self.elaborate_computation(
                            &ComputationTermExp::Associated {
                                span: *span,
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
                        let ty = crate::kernel_bridge::instantiate_computation_type_parameters(
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
        let (mut computation, mut computation_ty) = match head {
            Head::Computation(computation, ty) => (computation, ty),
            Head::Value(Some(ty)) => {
                let ty = self.resolve_value_type_head(environment, ty);
                return match environment.crate_env.arena().get(ty) {
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
                    if matches!(
                        environment.crate_env.arena().get(value_ty),
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
                            .crate_env
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
                            .crate_env
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
