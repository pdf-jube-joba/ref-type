use crate::{
    elaborator::{module_manager::ItemAccessResult, term_elaborator::LocalScope},
    hir::*,
    kernel_bridge::{instantiate_telescope, shift_bound_indices, whnf},
    metavariables::{ElaborationError, MetaStore},
    output::Output,
    raw::{
        derivation::CheckSession,
        environment::{
            CrateEnv, DefinedConstant, ModuleArgument, ModuleParameter, ModuleParameterKind,
        },
        exp::*,
        ids::{ModuleId, *},
        inductive::{CtorBinder, InductiveTypeSpecs},
        program_derivation::ProgramCheckSession,
        program_inductive::{ProgramConstructorSpec, ProgramInductiveTypeSpecs},
        remapping::{exp_subst_map, remap_all_global_ids},
        sort::Sort,
        traversal::exp_contains_inductive,
    },
};
use std::collections::HashMap;

pub mod analysis;
mod declarations;
pub(crate) mod module_manager;
mod modules;
pub(crate) mod profiling;
pub(crate) mod program_term_elaborator;
mod queries;
mod structures;
pub(crate) mod term_elaborator;

fn apply_pts_projection(arena: &Arena, definition: DefId, parameters: &[Exp], value: Exp) -> Exp {
    let projection = arena.alloc(ExpNode::DefinedConstant(definition));
    crate::raw::utils::assoc_apply(
        arena,
        projection,
        parameters.iter().copied().chain([value]).collect(),
    )
}

fn projected_record_field_type(
    arena: &Arena,
    spec: &InductiveTypeSpecs,
    field: usize,
    parameters: &[Exp],
    value: Exp,
    preceding_projections: &[DefId],
) -> Result<Exp, crate::error::Error> {
    let constructor = spec.constructors()[0].instantiate_parameters(arena, parameters);
    let Some(CtorBinder::Simple((_, field_ty))) = constructor.telescope.get(field) else {
        return Err(crate::error::Error::Invalid(
            crate::error::Invalid::RecordFieldIndexOutOfBounds,
        ));
    };
    let preceding = preceding_projections
        .iter()
        .map(|definition| apply_pts_projection(arena, *definition, parameters, value))
        .collect::<Vec<_>>();
    Ok(instantiate_telescope(arena, *field_ty, &preceding))
}

// Workspace state for surface elaboration and kernel checking.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct GlobalEnvironment {
    #[cfg(test)]
    #[serde(skip)]
    source_modules: Vec<::syntax::syntax::Module>,
    pub(crate) crate_env: CrateEnv,
    #[serde(skip)]
    outputs: Vec<Output>,
    analysis: crate::analysis::Analysis,
    #[serde(skip)]
    diagnostic_location: Option<SourceLocation>,
    module_manager: module_manager::ModuleManager,
    #[serde(skip)]
    metavariables: MetaStore,
    #[serde(skip)]
    predeclared_modules: HashMap<*const Module, ModuleId>,
    resolved_declarations: usize,
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        let crate_env = CrateEnv::default();
        Self {
            #[cfg(test)]
            source_modules: vec![],
            crate_env,
            outputs: vec![],
            analysis: Default::default(),
            diagnostic_location: None,
            module_manager: Default::default(),
            metavariables: Default::default(),
            predeclared_modules: HashMap::new(),
            resolved_declarations: 0,
        }
    }
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn reflect_front_expression(&mut self, expression: &SExp) -> Result<Exp, ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        if let Ok(syntax) = ValueTypeExp::try_from(expression.clone())
            && let Ok(ty) = scope.elaborate_value_type(&syntax, self)
        {
            ProgramCheckSession::new(&self.crate_env, &mut scope.context().clone())
                .check_value_type(ty)
                .map_err(crate::error::Error::from)?;
            return crate::raw::reflection::reflect_value_type(&self.crate_env, ty)
                .map_err(|error| crate::error::Error::from(error).into());
        }
        if let Ok(syntax) = ValueTermExp::try_from(expression.clone()) {
            let value = scope.elaborate_value(&syntax, self)?;
            let (value, _) = scope.infer_value_term_with_metas(self, value)?;
            scope.finish_metas(self)?;
            let value = scope.zonk_module_value(self, value);
            return crate::raw::reflection::reflect_value(&self.crate_env, value)
                .map_err(|error| crate::error::Error::from(error).into());
        }
        let syntax: ComputationTermExp = expression.clone().try_into()?;
        let computation = scope.elaborate_computation(&syntax, self)?;
        let (computation, _) = scope.infer_computation_term_with_metas(self, computation)?;
        scope.finish_metas(self)?;
        let computation = scope.zonk_module_computation(self, computation);
        crate::raw::reflection::reflect_computation(&self.crate_env, computation)
            .map_err(|error| crate::error::Error::from(error).into())
    }
    fn check_program_member(&mut self, value: &SExp, ty: &SExp) -> Result<(), ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        scope.check_member(value, ty, self)?;
        scope.finish_metas(self)
    }
    fn locate_error(&mut self, span: SourceSpan) {
        // Keep the innermost failing statement when enclosing lets unwind.
        if let Some(location) = &mut self.diagnostic_location
            && location.span.start <= span.start
            && span.end <= location.span.end
        {
            location.span = span;
        }
    }

    fn env(&self) -> &CrateEnv {
        &self.crate_env
    }

    fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    fn intern(&mut self, name: &str) -> SymbolId {
        self.crate_env.intern(name)
    }

    fn symbol(&self, symbol: SymbolId) -> &str {
        self.crate_env.symbol(symbol)
    }

    fn fresh_meta(
        &mut self,
        kind: SurfaceMeta,
        span: SourceSpan,
        local_context: &ExpContext,
    ) -> Result<Exp, ElaborationError> {
        let mut context = self.module_manager.current_context(&self.crate_env);
        context.extend(local_context.iter().cloned());
        self.metavariables
            .fresh(&self.crate_env, kind, span, &context, local_context.len())
            .map_err(Into::into)
    }

    fn assign_meta(&mut self, meta: Exp, value: Exp) -> Result<(), ElaborationError> {
        self.metavariables
            .unify(&self.crate_env, meta, value)
            .map_err(|message| {
                self.metavariables
                    .constraint_error(&self.crate_env, message)
            })?;
        Ok(())
    }

    fn record_source(&mut self, term: Exp, span: SourceSpan) {
        self.metavariables
            .record_source(&self.crate_env, term, span);
    }

    fn reflect_program_expression(
        &mut self,
        parameter: resolve::hir::BindingId,
        expression: &SExp,
    ) -> Result<Exp, ElaborationError> {
        let binding = self.module_manager.hir_bindings.get(&parameter).ok_or(
            crate::error::Error::Invalid(crate::error::Invalid::UnknownHirParameter),
        )?;
        let module = *self.module_manager.hir_modules.get(&binding.module).ok_or(
            crate::error::Error::Invalid(crate::error::Invalid::UnknownHirModule),
        )?;
        let parameter = ModuleParamId {
            module,
            position: binding.parameter.ok_or(crate::error::Error::Invalid(
                crate::error::Invalid::ExpectedModuleParameter,
            ))? as u32,
        };
        let kind = self
            .crate_env
            .module_parameter_opt(parameter)
            .ok_or(crate::error::Error::Invalid(
                crate::error::Invalid::UnknownModuleParameter,
            ))?
            .kind;
        let mut scope = program_term_elaborator::ProgramScope::new();
        match kind {
            ModuleParameterKind::ProgramType => {
                let ty = scope
                    .elaborate_value_type(&ValueTypeExp::try_from(expression.clone())?, self)?;
                Ok(
                    crate::raw::reflection::reflect_value_type(&self.crate_env, ty)
                        .map_err(crate::error::Error::from)?,
                )
            }
            ModuleParameterKind::ProgramValue { .. } => {
                let value =
                    scope.elaborate_value(&ValueTermExp::try_from(expression.clone())?, self)?;
                Ok(
                    crate::raw::reflection::reflect_value(&self.crate_env, value)
                        .map_err(crate::error::Error::from)?,
                )
            }
            ModuleParameterKind::Pts { .. } => Err(crate::error::Error::Invalid(
                crate::error::Invalid::OnlyProgramParametersSupportSetReflection,
            )
            .into()),
        }
    }

    fn intern_name(&mut self, name: &Identifier) -> SymbolId {
        self.crate_env.intern_name(name)
    }

    fn instantiate_module(
        &mut self,
        path: &ModuleInstantiatePath,
        name: &Identifier,
        scope: &mut LocalScope,
    ) -> Result<(), ElaborationError> {
        let mut program_scope = program_term_elaborator::ProgramScope::new();
        let binding = self.instantiate_module_expression(path, scope, &mut program_scope)?;
        self.module_manager
            .register_hir_import(&self.crate_env, name, binding);
        Ok(())
    }

    fn direct_module_definition(
        &mut self,
        path: &ModuleInstantiatePath,
        name: &Identifier,
        access: &LocalAccess,
        scope: &mut LocalScope,
        arguments: &[&SExp],
    ) -> Result<Option<Exp>, ElaborationError> {
        let _profile =
            profiling::ProfileTimer::start("REF_TYPE_PROFILE_DIRECT_DEFINITIONS", || {
                format!("direct definition path={path:?} import={name:?} access={access:?}")
            });
        // Selecting a logical definition specializes its explicit kernel
        // captures. Constructors, Program declarations, and ambient local
        // namespaces still use ordinary graph instantiation.
        let Some(member) = self.module_manager.direct_import_member(name, access) else {
            if _profile.is_some() {
                eprintln!("direct definition fallback: member access is not the guarded import");
            }
            return Ok(None);
        };
        let (mut source, calls, inherited) = match path {
            ModuleInstantiatePath::FromModule { module, calls } => {
                let Some(source) = self.module_manager.hir_module(*module) else {
                    if _profile.is_some() {
                        eprintln!("direct definition fallback: unresolved source {module:?}");
                    }
                    return Ok(None);
                };
                (source, calls, Vec::new())
            }
            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                let mut source = self.module_manager.current();
                for _ in 0..*back_parent {
                    let Some(parent) = self.crate_env.module(source).parent() else {
                        return Ok(None);
                    };
                    source = parent;
                }
                (source, calls, Vec::new())
            }
            ModuleInstantiatePath::FromRoot { calls } => {
                (self.crate_env.root_module(), calls, Vec::new())
            }
            ModuleInstantiatePath::FromImport { import_name, calls } => {
                let Some(binding) = self.module_manager.hir_import(&self.crate_env, import_name)
                else {
                    return Ok(None);
                };
                let binding = self.crate_env.binding(binding);
                (binding.source, calls, binding.arguments.clone())
            }
        };
        if calls.is_empty() || self.crate_env.namespace_binding_id(source).is_some() {
            if _profile.is_some() {
                eprintln!(
                    "direct definition fallback: source={source:?} is already a namespace instance or has no calls"
                );
            }
            return Ok(None);
        }
        let mut substitutions = Vec::with_capacity(inherited.len());
        for (id, argument) in inherited {
            let ModuleArgument::Pts(value) = argument else {
                return Ok(None);
            };
            substitutions.push((id, value));
        }
        let mut pending = Vec::new();
        for (child_name, supplied) in calls {
            let Some(child) = self
                .module_manager
                .hir_child(&self.crate_env, source, child_name)
            else {
                if _profile.is_some() {
                    eprintln!(
                        "direct definition fallback: unresolved child {child_name:?} of {source:?}"
                    );
                }
                return Ok(None);
            };
            if self.crate_env.namespace_binding_id(child).is_some() {
                if _profile.is_some() {
                    eprintln!(
                        "direct definition fallback: child={child:?} is already a namespace instance"
                    );
                }
                return Ok(None);
            }
            let parameters = self.crate_env.module(child).parameters();
            if parameters.len() != supplied.len() {
                if _profile.is_some() {
                    eprintln!(
                        "direct definition fallback: module {child:?} requires {} arguments but received {}",
                        parameters.len(),
                        supplied.len()
                    );
                }
                return Ok(None);
            }
            for (position, (parameter, (argument_name, expression))) in
                parameters.iter().zip(supplied).enumerate()
            {
                let ModuleParameterKind::Pts { ty } = parameter.kind else {
                    return Ok(None);
                };
                if argument_name.as_str() != self.crate_env.symbol(parameter.name) {
                    return Ok(None);
                }
                pending.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    ty,
                    expression,
                ));
            }
            source = child;
        }
        let Some(crate::raw::environment::ModuleItem::Definition { definition, .. }) =
            self.crate_env.module(source).item(member.as_str())
        else {
            if _profile.is_some() {
                eprintln!(
                    "direct definition fallback: source {source:?} has no logical definition {}",
                    member.as_str()
                );
            }
            return Ok(None);
        };
        let definition = *definition;
        let (definition_ty, body, explicit) = match self.crate_env.definition(definition) {
            DefinedConstant::Pts { ty, body } => (*ty, *body, 0),
            DefinedConstant::Contextual {
                parameters,
                ty,
                body,
            } => (*ty, *body, parameters.len()),
            _ => return Ok(None),
        };
        if arguments.len() < explicit {
            if _profile.is_some() {
                eprintln!(
                    "direct definition fallback: member={} requires {explicit} own arguments but received {}",
                    member.as_str(),
                    arguments.len()
                );
            }
            return Ok(None);
        }
        if [definition_ty, body].into_iter().any(|term| {
            self.crate_env
                .arena()
                .max_loose_bound(crate::raw::traversal::Term::Logical(term))
                .is_some_and(|i| i >= explicit)
        }) {
            if _profile.is_some() {
                eprintln!(
                    "direct definition fallback: member={} retains an ambient local variable",
                    member.as_str()
                );
            }
            return Ok(None);
        }
        for (id, ty, expression) in pending {
            let expected =
                crate::kernel_bridge::captured_expression(&self.crate_env, ty, &substitutions)?;
            let argument = scope.elab_exp(expression, self)?;
            self.check(&mut scope.context().clone(), argument, expected)?;
            substitutions.push((id, self.metavariables.zonk(&self.crate_env, argument)));
        }
        let mut actual = Vec::with_capacity(explicit);
        if let DefinedConstant::Contextual { parameters, .. } =
            self.crate_env.definition(definition).clone()
        {
            for (index, ((_, ty), expression)) in parameters.iter().zip(arguments).enumerate() {
                let expected = crate::kernel_bridge::captured_expression(
                    &self.crate_env,
                    *ty,
                    &substitutions
                        .iter()
                        .map(|(id, value)| {
                            (
                                *id,
                                shift_bound_indices(self.crate_env.arena(), *value, index, 0),
                            )
                        })
                        .collect::<Vec<_>>(),
                )?;
                let expected = instantiate_telescope(self.crate_env.arena(), expected, &actual);
                let value = scope.elab_exp(expression, self)?;
                self.check(&mut scope.context().clone(), value, expected)?;
                actual.push(self.metavariables.zonk(&self.crate_env, value));
            }
        }
        let mut value = crate::kernel_bridge::captured_definition(
            &self.crate_env,
            definition,
            &substitutions,
            &actual,
        )?;
        for expression in &arguments[explicit..] {
            let argument = scope.elab_exp(expression, self)?;
            let ty = self.infer(&mut scope.context().clone(), value)?;
            let ty = whnf(
                &self.crate_env,
                self.metavariables.zonk(&self.crate_env, ty),
            );
            if let ExpNode::Prod { ty: domain, .. } = self.crate_env.arena().get(ty) {
                self.check(&mut scope.context().clone(), argument, domain)?;
            }
            value = self.crate_env.arena().alloc(ExpNode::App {
                func: value,
                arg: argument,
            });
        }
        self.materialize_module_term(scope.context(), value)
            .map(Some)
    }

    fn materialize_module_term(
        &mut self,
        context: &ExpContext,
        term: Exp,
    ) -> Result<Exp, ElaborationError> {
        use crate::raw::traversal::{Memoized, Rewrite, Term};
        struct Names;
        impl Rewrite for Names {
            fn rewrite(&mut self, _: Term, _: usize) -> Option<Term> {
                None
            }
            fn finish(&mut self, arena: &Arena, _: Term, _: usize, result: Term) -> Term {
                if let Term::Logical(e) = result
                    && let kernel::syntax::Node::Definition { id, arguments } = arena.core.get(e.0)
                    && let Some(reference) = arena.nominal_reference(id, &arguments, false)
                {
                    return Term::Logical(Exp(reference));
                }
                result
            }
        }
        let term =
            crate::kernel_bridge::logical(&self.crate_env, context, &[term], |_, _, terms| {
                Ok(Exp(terms[0]))
            })?;
        // Preserve names for subsequent namespace remapping, but never unfold
        // specialized bodies while converting back from the kernel DAG.
        let Term::Logical(term) =
            Term::Logical(term).walk(self.crate_env.arena(), 0, &mut Memoized::new(Names))
        else {
            unreachable!()
        };
        Ok(term)
    }

    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ElaborationError> {
        Ok(self
            .module_manager
            .get_item(&self.crate_env, access_path)
            .ok_or_else(|| crate::error::Error::UnknownAccess {
                access_path: (access_path).clone(),
            })?)
    }

    fn associated_reference(&mut self, access: &LocalAccess, field: &Identifier, span: SourceSpan) {
        self.module_manager
            .record_associated_reference(&self.crate_env, access, field, span);
    }

    fn field_projection(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        field_name: &Identifier,
    ) -> Result<Exp, ElaborationError> {
        let infer_type_e = self.infer(local_ctx, e).map_err(|error| {
            crate::error::Error::from(error)
                .context(crate::error::Context::FailedToInferTypeOfExpressionForFieldProjection)
        })?;
        if let ExpNode::IndType { indspec, .. } =
            self.crate_env.arena().get(whnf(&self.crate_env, e))
            && let Some(record) = self
                .module_manager
                .get_moditem_record(&self.crate_env, indspec)
        {
            let name = record.type_name.as_str();
            return Err(crate::error::Error::ProjectionFromStructureType {
                field: (field_name.as_str()).to_string(),
                name: (name).to_string(),
            }
            .into());
        }
        let mut candidates = vec![(e, infer_type_e)];
        let mut found_inductive = false;
        let mut found_record = false;
        while let Some((value, ty)) = candidates.pop() {
            let ty = whnf(&self.crate_env, ty);
            match self.crate_env.arena().get(ty) {
                ExpNode::TypeLift { superset, subset } => {
                    let proof = self
                        .crate_env
                        .arena()
                        .alloc(ExpNode::Prove(Prove::SubsetElim {
                            superset,
                            subset,
                            element: value,
                        }));
                    let law = self.infer(local_ctx, proof)?;
                    candidates.push((proof, law));
                    candidates.push((value, superset));
                }
                ExpNode::IndType {
                    indspec,
                    parameters,
                } => {
                    found_inductive = true;
                    if let Some(record) = self
                        .module_manager
                        .get_moditem_record(&self.crate_env, indspec)
                    {
                        found_record = true;
                        if let Some(projection) = record.field_projection(
                            &self.crate_env,
                            value,
                            field_name,
                            &parameters,
                        )? {
                            return Ok(projection);
                        }
                    }
                }
                _ => {}
            }
        }
        if !found_inductive {
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::ExpectedInductiveTypeForFieldProjection,
            )
            .into());
        }
        if !found_record {
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::InductiveTypeIsNotARecordType,
            )
            .into());
        }
        Err(crate::error::Error::UnknownRecordField {
            field: (field_name.as_str()).to_string(),
        }
        .into())
    }

    fn unify(
        &mut self,
        local_ctx: &ExpContext,
        left: Exp,
        right: Exp,
    ) -> Result<(), ElaborationError> {
        let mut context = self.module_manager.current_context(&self.crate_env);
        context.extend(local_ctx.iter().cloned());
        self.metavariables
            .unify_in_context(&self.crate_env, &context, left, right)
            .map(|_| ())
            .map_err(|message| {
                self.metavariables
                    .constraint_error(&self.crate_env, message)
            })
    }

    fn zonk(&self, exp: Exp) -> Exp {
        self.metavariables.zonk(&self.crate_env, exp)
    }

    fn infer(&mut self, local_ctx: &mut ExpContext, e: Exp) -> Result<Exp, ElaborationError> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        let module_context_len = ctx.len();
        ctx.append(local_ctx);
        let result = if !self.metavariables.is_empty() {
            // Earlier local definitions may already have solved their holes,
            // but their shared syntax still contains the metavariable nodes.
            for entry in &mut ctx {
                entry.ty = self.metavariables.zonk(&self.crate_env, entry.ty);
            }
            self.metavariables.infer_pts(
                &self.crate_env,
                self.module_manager.current(),
                &mut ctx,
                e,
            )
        } else {
            CheckSession::new(&self.crate_env, &mut ctx)
                .infer_pts(e)
                .map_err(|error| {
                    crate::error::Error::from(error)
                        .context(crate::error::Context::FailedToInferElaboratedSetPropExpression)
                })
        };
        *local_ctx = ctx.split_off(module_context_len);
        Ok(result?)
    }

    fn check(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        ty: Exp,
    ) -> Result<(), ElaborationError> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        ctx.extend(local_ctx.iter().cloned());
        self.check_term_with_metavariables(&mut ctx, e, ty)
            .map_err(|message| {
                self.metavariables
                    .constraint_error(&self.crate_env, message)
            })
    }

    fn match_parameters(
        &mut self,
        local_ctx: &mut ExpContext,
        scrutinee: Exp,
        inductive: InductiveId,
    ) -> Result<Vec<Exp>, ElaborationError> {
        let ty = self.infer(local_ctx, scrutinee)?;
        self.metavariables
            .inductive_arguments(&self.crate_env, inductive, ty)
            .map(|(parameters, _)| parameters)
            .map_err(|message| {
                self.metavariables
                    .constraint_error(&self.crate_env, message)
            })
    }

    fn elaborate_boxed_computation_type(
        &mut self,
        expression: &SExp,
    ) -> Result<crate::raw::program::ComputationType, ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
        let ty = scope.elaborate_computation_type(&computation_ty, self)?;
        scope.finish_metas(self)?;
        Ok(ty)
    }

    fn elaborate_boxed_program(
        &mut self,
        ty: &SExp,
        computation: &SExp,
    ) -> Result<
        (
            crate::raw::program::ComputationType,
            crate::raw::program::ComputationTerm,
        ),
        ElaborationError,
    > {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let ty = ComputationTypeExp::try_from(ty.clone())?;
        let computation = ComputationTermExp::try_from(computation.clone())?;
        let ty = scope.elaborate_computation_type(&ty, self)?;
        let computation = scope.elaborate_computation_expected(&computation, ty, self)?;
        let (computation, ty) = scope.check_computation_term_with_metas(self, computation, ty)?;
        Ok((ty, computation))
    }

    fn elaborate_program_type_arguments(
        &mut self,
        expressions: &[SExp],
        expected: usize,
    ) -> Result<Vec<crate::raw::program::ValueType>, ElaborationError> {
        if expressions.len() != expected {
            return Err(crate::error::Error::ReflectedTypeArgumentCountMismatch {
                actual: expressions.len(),
                expected,
            }
            .into());
        }
        let expressions = expressions
            .iter()
            .cloned()
            .map(ValueTypeExp::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let mut scope = program_term_elaborator::ProgramScope::new();
        let arguments = expressions
            .iter()
            .map(|expression| scope.elaborate_value_type(expression, self))
            .collect::<Result<Vec<_>, _>>()?;
        scope.finish_metas(self)?;
        Ok(arguments)
    }
}

impl GlobalEnvironment {
    pub fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    pub fn kernel_env(&self) -> std::cell::Ref<'_, kernel::environment::Environment> {
        self.crate_env.kernel.borrow()
    }

    pub fn crate_env(&self) -> &CrateEnv {
        &self.crate_env
    }

    fn finish_metavariables(&mut self) -> Result<(), ElaborationError> {
        self.metavariables.finish(&self.crate_env)
    }

    /// Infer a Set/Prop term whose surface syntax still contains metavariables.
    fn infer_term_with_metavariables(
        &mut self,
        ctx: &mut ExpContext,
        term: Exp,
    ) -> Result<Exp, crate::error::Error> {
        self.metavariables
            .infer_pts(&self.crate_env, self.module_manager.current(), ctx, term)
    }

    /// Check a term against an expected type containing metavariables without
    /// letting failed judgement-classification probes contaminate later ones.
    fn check_term_with_metavariables(
        &mut self,
        ctx: &mut ExpContext,
        term: Exp,
        expected: Exp,
    ) -> Result<(), crate::error::Error> {
        let expected = self.metavariables.zonk(&self.crate_env, expected);
        if matches!(self.crate_env.arena().get(expected), ExpNode::Meta { .. }) {
            let inferred = self.infer_term_with_metavariables(ctx, term)?;
            self.metavariables
                .unify(&self.crate_env, expected, inferred)?;
            return Ok(());
        }

        self.metavariables.check_pts(
            &self.crate_env,
            self.module_manager.current(),
            ctx,
            term,
            expected,
        )
    }
}

impl GlobalEnvironment {
    fn predeclare_module_tree(
        &mut self,
        parent: ModuleId,
        module: &Module,
    ) -> Result<(), ElaborationError> {
        let child = self
            .crate_env
            .reserve_child_module(parent, module.name.0.clone());
        let _time = timing::Scope::module(|| analysis::module_path(&self.crate_env, child));
        self.crate_env.publish_child_module(child)?;
        self.predeclared_modules.insert(module, child);
        self.module_manager.hir_modules.insert(module.id, child);
        if let Some(id) = module.name.1 {
            self.module_manager.hir_module_bindings.insert(id, child);
        }
        for (id, binding) in &self.module_manager.hir_bindings {
            if binding.module == module.id && binding.parameter.is_none() {
                self.crate_env
                    .register_hir_name(child, *id, binding.name.clone());
            }
        }
        let ModuleBody::Inline(items) = &module.body else {
            return Err(crate::error::Error::UnresolvedExternalModule {
                name: (module.name.as_str()).to_string(),
            }
            .into());
        };
        for item in items {
            if let ModuleItem::ChildModule { module } = item {
                self.predeclare_module_tree(child, module)?;
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn add_modules_to_root(
        &mut self,
        modules: &[::syntax::syntax::Module],
    ) -> Result<(), ElaborationError> {
        let mut source = std::mem::take(&mut self.source_modules);
        source.extend_from_slice(modules);
        *self = Self::default();
        let project = resolve::resolve(&source).map_err(|error| match error.location.clone() {
            Some(location) => ElaborationError::Located {
                location,
                error: Box::new(ElaborationError::Failure(error.into())),
            },
            None => ElaborationError::Failure(error.into()),
        })?;
        self.source_modules = source;
        self.add_project(&project)
            .map_err(|error| error.materialize(self))
    }

    pub(crate) fn add_project(
        &mut self,
        project: &resolve::Project,
    ) -> Result<(), ElaborationError> {
        self.add_project_range(
            project,
            0,
            project.order.len(),
            &(0..project.order.len()).collect(),
            &mut |_, _| {},
            &mut |_| {},
        )
    }

    pub(crate) fn add_project_range(
        &mut self,
        project: &resolve::Project,
        start: usize,
        end: usize,
        selected: &std::collections::BTreeSet<usize>,
        checkpoint: &mut impl FnMut(usize, &Self),
        progress: &mut impl FnMut(crate::CheckStepProgress),
    ) -> Result<(), ElaborationError> {
        self.analysis.references = project.references.clone();
        let checked = self
            .analysis
            .declarations
            .split_off(self.resolved_declarations);
        self.analysis.declarations = project.declarations.clone();
        self.resolved_declarations = self.analysis.declarations.len();
        self.analysis.declarations.extend(checked);
        self.module_manager.hir_imports = project.imports.clone();
        self.module_manager.hir_bindings = project.bindings.clone();
        self.add_expanded_modules_to_root(project, start, end, selected, checkpoint, progress)
    }

    fn add_expanded_modules_to_root(
        &mut self,
        project: &resolve::Project,
        start: usize,
        end: usize,
        selected: &std::collections::BTreeSet<usize>,
        checkpoint: &mut impl FnMut(usize, &Self),
        progress: &mut impl FnMut(crate::CheckStepProgress),
    ) -> Result<(), ElaborationError> {
        self.diagnostic_location = None;
        let modules = &project.modules;
        fn collect<'a>(
            module: &'a Module,
            scheduled: &mut HashMap<resolve::hir::ModuleId, &'a Module>,
        ) {
            scheduled.insert(module.id, module);
            if let ModuleBody::Inline(items) = &module.body {
                for item in items {
                    if let ModuleItem::ChildModule { module } = item {
                        collect(module, scheduled);
                    }
                }
            }
        }
        let mut scheduled = HashMap::new();
        for module in modules {
            collect(module, &mut scheduled);
        }
        if start != 0 {
            let sources: HashMap<_, _> = scheduled
                .values()
                .flat_map(|module| {
                    module
                        .source
                        .iter()
                        .chain(&module.header_source)
                        .map(|source| (source.id.clone(), source.clone()))
                })
                .collect();
            let restore = |location: &mut SourceLocation| -> Result<(), ElaborationError> {
                location.source = sources.get(&location.source.id).cloned().ok_or(
                    crate::error::Error::Invalid(
                        crate::error::Invalid::CheckpointSourceMissingFromProject,
                    ),
                )?;
                Ok(())
            };
            for declaration in &mut self.analysis.declarations {
                restore(&mut declaration.location)?;
            }
            for output in &mut self.analysis.outputs {
                restore(&mut output.location)?;
            }
            for reference in self.module_manager.references.get_mut() {
                restore(&mut reference.location)?;
            }
        }
        self.predeclared_modules.clear();
        if start == 0 {
            for module in modules {
                self.predeclare_module_tree(self.crate_env.root_module(), module)?;
            }
        } else {
            self.module_manager.hir_module_bindings.clear();
            for (&id, module) in &scheduled {
                let typed = self.module_manager.hir_modules[&id];
                self.predeclared_modules.insert(*module, typed);
                if let Some(binding) = module.name.1 {
                    self.module_manager
                        .hir_module_bindings
                        .insert(binding, typed);
                }
            }
            let source_modules = scheduled
                .keys()
                .map(|id| (*id, self.module_manager.hir_modules[id]))
                .collect();
            self.crate_env
                .refresh_hir_names(&source_modules, &project.bindings);
        }

        let result = (|| {
            for (position, step) in project.order.iter().enumerate().take(end).skip(start) {
                if !selected.contains(&position) {
                    continue;
                }
                let id = match step {
                    resolve::CheckStep::Parameters(id) => id,
                    resolve::CheckStep::Declaration { module, .. } => module,
                };
                let module = *scheduled.get(id).ok_or(crate::error::Error::Invalid(
                    crate::error::Invalid::UnknownHirModuleInExecutionOrder,
                ))?;
                let module_id = self.predeclared_modules[&(module as *const Module)];
                let _time =
                    timing::Scope::module(|| analysis::module_path(&self.crate_env, module_id));
                self.module_manager.moveto(module_id);
                progress(crate::CheckStepProgress::Started(position));
                let started = std::time::Instant::now();
                let result = match *step {
                    resolve::CheckStep::Parameters(_) => self.elaborate_module_parameters(module),
                    resolve::CheckStep::Declaration { index, .. } => {
                        self.elaborate_module_declaration(module, index)
                    }
                };
                progress(crate::CheckStepProgress::Finished {
                    position,
                    elapsed: started.elapsed(),
                    success: result.is_ok(),
                });
                result?;
                checkpoint(position + 1, self);
            }
            crate::lowering::Lowerer::new(&self.crate_env, &mut self.crate_env.kernel.borrow_mut())
                .lower_all()
                .map_err(ElaborationError::from)
        })();
        self.predeclared_modules.clear();
        self.collect_references();
        self.metavariables.clear();
        match (result, self.diagnostic_location.take()) {
            (Err(error), Some(location)) => Err(ElaborationError::Located {
                location,
                error: Box::new(error),
            }),
            (result, _) => result,
        }
    }

    #[cfg(test)]
    pub fn add_new_module_to_root(
        &mut self,
        module: &::syntax::syntax::Module,
    ) -> Result<(), ElaborationError> {
        self.add_modules_to_root(std::slice::from_ref(module))
    }
}
