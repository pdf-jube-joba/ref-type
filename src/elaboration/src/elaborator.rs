use crate::raw::ids::ModuleId;
use crate::raw::{
    calculus::{
        exp_contains_inductive, exp_subst_map, instantiate_telescope, remap_all_global_ids,
        shift_bound_indices, whnf,
    },
    derivation::CheckSession,
    environment::{
        CrateEnv, DefinedConstant, ModuleArgument, ModuleParameter, ModuleParameterKind,
    },
    exp::*,
    ids::*,
    inductive::{CtorBinder, InductiveTypeSpecs},
    program_derivation::ProgramCheckSession,
    program_inductive::{ProgramConstructorSpec, ProgramInductiveTypeSpecs},
    sort::Sort,
};
use crate::{
    elaborator::{module_manager::ItemAccessResult, term_elaborator::LocalScope},
    hir::*,
    metavariables::{ElaborationError, MetaStore},
    output::Output,
};
use std::collections::HashMap;

pub mod analysis;
mod declarations;
pub(crate) mod module_manager;
mod modules;
mod profiling;
pub(crate) mod program_term_elaborator;
mod queries;
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
) -> Result<Exp, String> {
    let constructor = spec.constructors()[0].instantiate_parameters(arena, parameters);
    let Some(CtorBinder::Simple((_, field_ty))) = constructor.telescope.get(field) else {
        return Err("record field index out of bounds".into());
    };
    let preceding = preceding_projections
        .iter()
        .map(|definition| apply_pts_projection(arena, *definition, parameters, value))
        .collect::<Vec<_>>();
    Ok(instantiate_telescope(arena, *field_ty, &preceding))
}

// Workspace state for surface elaboration and kernel checking.
pub struct GlobalEnvironment {
    #[cfg(test)]
    source_modules: Vec<::syntax::syntax::Module>,
    crate_env: CrateEnv,
    outputs: Vec<Output>,
    analysis: crate::analysis::Analysis,
    diagnostic_location: Option<SourceLocation>,
    module_manager: module_manager::ModuleManager,
    metavariables: MetaStore,
    predeclared_modules: HashMap<*const Module, ModuleId>,
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
        }
    }
}

impl term_elaborator::Handler for GlobalEnvironment {
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
        let binding = self
            .module_manager
            .hir_bindings
            .get(&parameter)
            .ok_or("unknown HIR parameter")?;
        let module = *self
            .module_manager
            .hir_modules
            .get(&binding.module)
            .ok_or("unknown HIR module")?;
        let parameter = ModuleParamId {
            module,
            position: binding.parameter.ok_or("expected module parameter")? as u32,
        };
        let kind = self
            .crate_env
            .module_parameter_opt(parameter)
            .ok_or("unknown module parameter")?
            .kind;
        let mut scope = program_term_elaborator::ProgramScope::new();
        match kind {
            ModuleParameterKind::ProgramType => {
                let ty = scope
                    .elaborate_value_type(&ValueTypeExp::try_from(expression.clone())?, self)?;
                Ok(
                    crate::raw::reflection::reflect_value_type(&self.crate_env, ty)
                        .map_err(|error| error.to_string())?,
                )
            }
            ModuleParameterKind::ProgramValue { .. } => {
                let value =
                    scope.elaborate_value(&ValueTermExp::try_from(expression.clone())?, self)?;
                Ok(
                    crate::raw::reflection::reflect_value(&self.crate_env, value)
                        .map_err(|error| error.to_string())?,
                )
            }
            ModuleParameterKind::Pts { .. } => {
                Err("only Program parameters support Set reflection".into())
            }
        }
    }

    fn intern_name(&mut self, name: &Identifier) -> SymbolId {
        self.crate_env.intern_name(name)
    }

    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ElaborationError> {
        Ok(self
            .module_manager
            .get_item(&self.crate_env, access_path)
            .ok_or_else(|| format!("Failed to access item at path {access_path:?}"))?)
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
            format!("Failed to infer type of expression for field projection: {error}")
        })?;
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
                        if let Some(projection) =
                            record.field_projection(&self.crate_env, value, field_name, &parameters)
                        {
                            return Ok(projection);
                        }
                    }
                }
                _ => {}
            }
        }
        if !found_inductive {
            return Err("Expected inductive type for field projection"
                .to_string()
                .into());
        }
        if !found_record {
            return Err("Inductive type is not a record type".to_string().into());
        }
        Err(format!(
            "Field {} not found in record or its laws",
            field_name.as_str()
        )
        .into())
    }

    fn unify(&mut self, left: Exp, right: Exp) -> Result<(), ElaborationError> {
        self.metavariables
            .unify(&self.crate_env, left, right)
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
                .map_err(|error| format!("Failed to infer elaborated Set/Prop expression: {error}"))
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
        let computation = scope.elaborate_computation(&computation, self)?;
        let (computation, ty) = scope.check_computation_term_with_metas(self, computation, ty)?;
        Ok((ty, computation))
    }

    fn elaborate_program_type_arguments(
        &mut self,
        expressions: &[SExp],
        expected: usize,
    ) -> Result<Vec<crate::raw::program::ValueType>, ElaborationError> {
        if expressions.len() != expected {
            return Err(format!(
                "reflected Program item expects {expected} type parameter(s), found {}",
                expressions.len()
            )
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
    ) -> Result<Exp, String> {
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
    ) -> Result<(), String> {
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
            return Err(format!(
                "External module '{}' was not resolved",
                module.name.as_str()
            )
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
        let project = resolve::resolve(&source).map_err(|error| match error.location {
            Some(location) => ElaborationError::Located {
                location,
                error: Box::new(ElaborationError::Message(error.message)),
            },
            None => ElaborationError::Message(error.message),
        })?;
        self.source_modules = source;
        self.add_project(&project)
    }

    pub(crate) fn add_project(
        &mut self,
        project: &resolve::Project,
    ) -> Result<(), ElaborationError> {
        self.analysis.references = project.references.clone();
        self.module_manager.hir_imports = project.imports.clone();
        self.module_manager.hir_bindings = project.bindings.clone();
        self.add_expanded_modules_to_root(project)
    }

    fn add_expanded_modules_to_root(
        &mut self,
        project: &resolve::Project,
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
        self.predeclared_modules.clear();
        for module in modules {
            self.predeclare_module_tree(self.crate_env.root_module(), module)?;
        }

        let result = (|| {
            for step in &project.order {
                let id = match step {
                    resolve::CheckStep::Parameters(id) => id,
                    resolve::CheckStep::Declaration { module, .. } => module,
                };
                let module = *scheduled
                    .get(id)
                    .ok_or("unknown HIR module in execution order")?;
                let module_id = self.predeclared_modules[&(module as *const Module)];
                self.module_manager.moveto(module_id);
                match *step {
                    resolve::CheckStep::Parameters(_) => {
                        self.elaborate_module_parameters(module)?
                    }
                    resolve::CheckStep::Declaration { index, .. } => {
                        self.elaborate_module_declaration(module, index)?
                    }
                }
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
