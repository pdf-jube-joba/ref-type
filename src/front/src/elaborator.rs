use crate::macros::MacroKind;
use crate::raw::{
    calculus::{exp_contains_inductive, exp_subst_map, instantiate_telescope, shift_bound_indices},
    derivation::CheckSession,
    environment::{
        CrateEnv, DefinedConstant, DefinitionKind, ModuleArgument, ModuleParameter,
        ModuleParameterKind,
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
    metavariables::{ElaborationError, MetaStore},
    output::Output,
    syntax::*,
};

pub mod module_manager;
pub mod program_term_elaborator;
pub mod term_elaborator;

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

// do type checking
#[derive(Default)]
pub struct GlobalEnvironment {
    kernel_env: kernel::stratified::environment::Environment,
    crate_env: CrateEnv,
    outputs: Vec<Output>,
    diagnostic_location: Option<SourceLocation>,
    module_manager: module_manager::ModuleManager,
    metavariables: MetaStore,
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn env(&self) -> &CrateEnv {
        &self.crate_env
    }

    fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    fn current_module(&self) -> ModuleId {
        self.module_manager.current()
    }

    fn module_context(&self) -> ExpContext {
        self.module_manager.current_context(&self.crate_env)
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
    ) -> Exp {
        let mut context = self.module_manager.current_context(&self.crate_env);
        context.extend(local_context.iter().cloned());
        self.metavariables
            .fresh(&self.crate_env, kind, span, &context, local_context.len())
    }

    fn expand_math_macro(
        &mut self,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        self.module_manager.expand_math_macro(
            &self.crate_env,
            scope.unwrap_or_else(|| self.module_manager.current()),
            tokens,
            depth,
            max_order,
        )
    }

    fn expand_named_macro(
        &mut self,
        name: &Identifier,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        self.module_manager.expand_named_macro(
            &self.crate_env,
            scope.unwrap_or_else(|| self.module_manager.current()),
            name,
            tokens,
            depth,
            max_order,
        )
    }

    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String> {
        self.module_manager
            .get_item(&self.crate_env, access_path)
            .ok_or("Failed to access item at path".to_string())
    }

    fn field_projection(&mut self, e: Exp, field_name: &Identifier) -> Result<Exp, String> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        let infer_type_e =
            CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx)
                .infer_pts(e)
                .map_err(|error| {
                    format!("Failed to infer type of expression for field projection: {error:?}")
                })?;

        let ExpNode::IndType {
            indspec,
            parameters,
        } = self.crate_env.arena().get(infer_type_e)
        else {
            return Err("Expected inductive type for field projection".to_string());
        };

        let record = self
            .module_manager
            .get_moditem_record(&self.crate_env, indspec)
            .ok_or("Inductive type is not a record type".to_string())?;

        let Some(exp) = record.field_projection(&self.crate_env, e, field_name, &parameters) else {
            return Err(format!("Field {} not found in record", field_name.as_str()));
        };

        Ok(exp)
    }

    fn infer(&mut self, local_ctx: &mut ExpContext, e: Exp) -> Result<Exp, String> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        let module_context_len = ctx.len();
        ctx.append(local_ctx);
        let result = if self.metavariables.contains_unsolved(&self.crate_env, e) {
            self.metavariables.infer_pts(
                &self.crate_env,
                self.module_manager.current(),
                &mut ctx,
                e,
            )
        } else {
            CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx)
                .infer_pts(e)
                .map_err(|error| {
                    format!("Failed to infer elaborated Set/Prop expression: {error:?}")
                })
        };
        *local_ctx = ctx.split_off(module_context_len);
        result
    }

    fn elaborate_program_type(
        &mut self,
        expression: &SExp,
    ) -> Result<crate::raw::program::ProgramType, String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        if let Ok(value_ty) = ValueTypeExp::try_from(expression.clone()) {
            return scope
                .elaborate_value_type(&value_ty, self)
                .map(crate::raw::program::ProgramType::Value);
        }
        let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
        scope
            .elaborate_computation_type(&computation_ty, self)
            .map(crate::raw::program::ProgramType::Computation)
    }

    fn elaborate_program(
        &mut self,
        expression: &SExp,
        ty: crate::raw::program::ProgramType,
    ) -> Result<(crate::raw::program::Program, Option<Exp>), String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        match ty {
            crate::raw::program::ProgramType::Value(_) => {
                let value = ValueExp::try_from(expression.clone())?;
                let value = scope.elaborate_value(&value, self)?;
                let certificate = scope.certified_value(self, value);
                Ok((crate::raw::program::Program::Value(value), certificate))
            }
            crate::raw::program::ProgramType::Computation(_) => {
                let computation = ComputationExp::try_from(expression.clone())?;
                let computation = scope.elaborate_computation(&computation, self)?;
                let certificate = scope.certified_computation(self, computation);
                Ok((
                    crate::raw::program::Program::Computation(computation),
                    certificate,
                ))
            }
        }
    }
}

impl GlobalEnvironment {
    pub fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    fn certify_query(&mut self, context: &ExpContext, term: Exp, ty: Exp) -> Result<(), String> {
        let mut lower = crate::lowering::Lowerer::new(&self.crate_env);
        lower.kernel = std::mem::take(&mut self.kernel_env);
        let result = (|| {
            let module = self.module_manager.current();
            let mut raw_context = context.clone();
            let term = lower.set(term, &mut raw_context, module)?;
            let expected = lower.classifier(ty, &mut raw_context, module)?;
            let context = lower.context(context, module)?;
            kernel::check::Checker::new(&lower.kernel, context).check(term, expected)
        })();
        self.kernel_env = lower.kernel;
        result
    }

    fn certify_program_query(
        &mut self,
        context: &crate::raw::program::ProgramContext,
        term: crate::raw::program::Program,
        ty: crate::raw::program::ProgramType,
    ) -> Result<(), String> {
        let mut lower = crate::lowering::Lowerer::new(&self.crate_env);
        lower.kernel = std::mem::take(&mut self.kernel_env);
        let result = (|| {
            let term = lower.program_in_context(term, &mut context.clone())?;
            let ty = lower.program_type(ty)?;
            let context = lower.program_context(context)?;
            kernel::check::Checker::new(&lower.kernel, context).check(term, ty)
        })();
        self.kernel_env = lower.kernel;
        result
    }

    pub fn kernel_env(&self) -> &kernel::stratified::environment::Environment {
        &self.kernel_env
    }

    pub fn crate_env(&self) -> &CrateEnv {
        &self.crate_env
    }

    pub fn outputs(&self) -> &[Output] {
        &self.outputs
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

    fn solve_module_arguments(
        &mut self,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: &mut [(Identifier, Vec<(Identifier, ModuleArgument)>)],
    ) -> Result<(), ElaborationError> {
        if self.metavariables.is_empty() {
            return Ok(());
        }
        let mut source = if let Some(back_parent) = back_parent {
            let mut module = self.module_manager.current();
            for _ in 0..back_parent {
                module =
                    self.crate_env.module(module).parent().ok_or_else(|| {
                        ElaborationError::Message("already at root module".into())
                    })?;
            }
            module
        } else {
            self.crate_env.root_module()
        };
        let mut substitutions = Vec::new();
        for (child_name, arguments) in calls.iter_mut() {
            let child = self
                .crate_env
                .module(source)
                .children()
                .iter()
                .copied()
                .find(|child| self.crate_env.module(*child).name() == child_name.as_str())
                .ok_or_else(|| {
                    ElaborationError::Message(format!(
                        "child module '{}' was not found",
                        child_name.as_str()
                    ))
                })?;
            let parameters = self.crate_env.module(child).parameters().to_vec();
            if parameters.len() != arguments.len() {
                return Err(ElaborationError::Message(format!(
                    "module '{}' argument count mismatch",
                    child_name.as_str()
                )));
            }
            for (position, ((argument_name, argument), parameter)) in
                arguments.iter_mut().zip(parameters).enumerate()
            {
                if argument_name.as_str() != self.crate_env.symbol(parameter.name) {
                    return Err(ElaborationError::Message(format!(
                        "module '{}' argument name mismatch",
                        child_name.as_str()
                    )));
                }
                match (parameter.kind, *argument) {
                    (ModuleParameterKind::Pts { ty }, ModuleArgument::Pts(exp)) => {
                        let expected = exp_subst_map(self.crate_env.arena(), ty, &substitutions);
                        self.metavariables
                            .check_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                exp,
                                expected,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                    }
                    (ModuleParameterKind::ProgramType, ModuleArgument::ProgramType(_))
                    | (ModuleParameterKind::ProgramValue { .. }, ModuleArgument::ProgramValue(_)) =>
                        {}
                    _ => {
                        return Err(ElaborationError::Message(
                            "module argument uses the wrong syntactic category".into(),
                        ));
                    }
                }
                let reflected = match *argument {
                    ModuleArgument::Pts(exp) => exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(&self.crate_env, ty).map_err(
                            |error| {
                                ElaborationError::Message(format!(
                                    "cannot reflect Program type module argument: {error}"
                                ))
                            },
                        )?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        &self.crate_env,
                        crate::raw::program::Program::Value(value),
                    )
                    .map_err(|error| {
                        ElaborationError::Message(format!(
                            "cannot reflect Program value module argument: {error}"
                        ))
                    })?,
                };
                substitutions.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    reflected,
                ));
            }
            source = child;
        }
        self.finish_metavariables()?;
        for (_, arguments) in calls {
            for (_, argument) in arguments {
                if let ModuleArgument::Pts(exp) = argument {
                    *exp = self.metavariables.zonk(&self.crate_env, *exp);
                }
            }
        }
        Ok(())
    }
}

impl GlobalEnvironment {
    pub fn add_new_module_to_root(&mut self, module: &Module) -> Result<(), ElaborationError> {
        self.diagnostic_location = None;
        self.module_manager.moveto_root();
        let result = self.module_add_rec(module).and_then(|()| {
            let (kernel, result) = crate::lowering::Lowerer::new(&self.crate_env)
                .extend(std::mem::take(&mut self.kernel_env));
            self.kernel_env = kernel;
            result.map_err(ElaborationError::from)?;
            Ok(())
        });
        match (result, self.diagnostic_location.take()) {
            (Err(error), Some(location)) => Err(ElaborationError::Located {
                location,
                error: Box::new(error),
            }),
            (result, _) => result,
        }
    }

    fn validate_definition(
        &self,
        context: &mut ExpContext,
        body: Exp,
        ty: Exp,
    ) -> Result<DefinitionKind, String> {
        CheckSession::new(&self.crate_env, self.module_manager.current(), context)
            .check_pts(body, ty)
            .map_err(|error| format!("Set/Prop definition check failed: {error:?}"))?;
        Ok(DefinitionKind::Pts)
    }

    fn add_record_projection_definitions(
        &mut self,
        inductive: InductiveId,
    ) -> Result<Vec<(Identifier, DefId)>, ElaborationError> {
        let module = self.module_manager.current();
        let spec = self.crate_env.inductive(inductive).clone();
        let parameters = spec.parameters().to_vec();
        let field_count = spec.constructors()[0].telescope.len();
        let structure_var = self.crate_env.intern("structure");
        let mut projections = Vec::with_capacity(field_count);

        for field in 0..field_count {
            let preceding_ids = projections
                .iter()
                .map(|(_, definition)| *definition)
                .collect::<Vec<_>>();
            let (name, ty, body) = {
                let arena = self.crate_env.arena();
                let CtorBinder::Simple((field_name, _)) = &spec.constructors()[0].telescope[field]
                else {
                    return Err("record fields must be non-recursive".into());
                };
                let name = Identifier(self.crate_env.symbol(*field_name).to_owned());
                if projections.iter().any(|(existing, _)| existing == &name) {
                    return Err(format!("duplicate record field name: {}", name.as_str()).into());
                }
                let parameter_arguments = (0..parameters.len())
                    .rev()
                    .map(|index| arena.exp_bound(index))
                    .collect::<Vec<_>>();
                let record_ty = arena.alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameter_arguments.clone(),
                });

                let parameters_under_value = parameter_arguments
                    .iter()
                    .map(|parameter| shift_bound_indices(arena, *parameter, 1, 0))
                    .collect::<Vec<_>>();
                let projected_ty = projected_record_field_type(
                    arena,
                    &spec,
                    field,
                    &parameters_under_value,
                    arena.exp_bound(0),
                    &preceding_ids,
                )?;
                let projection_ty = arena.alloc(ExpNode::Prod {
                    var: structure_var,
                    ty: record_ty,
                    body: projected_ty,
                });
                let ty = crate::raw::utils::assoc_prod(arena, parameters.clone(), projection_ty);

                let parameters_under_motive = parameters_under_value
                    .iter()
                    .map(|parameter| shift_bound_indices(arena, *parameter, 1, 0))
                    .collect::<Vec<_>>();
                let motive_record_ty = arena.alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameters_under_value.clone(),
                });
                let motive_result = projected_record_field_type(
                    arena,
                    &spec,
                    field,
                    &parameters_under_motive,
                    arena.exp_bound(0),
                    &preceding_ids,
                )?;
                let motive = arena.alloc(ExpNode::Lam {
                    var: structure_var,
                    ty: motive_record_ty,
                    body: motive_result,
                });

                let constructor =
                    spec.constructors()[0].instantiate_parameters(arena, &parameters_under_value);
                let case_telescope = constructor
                    .telescope
                    .into_iter()
                    .map(|binder| match binder {
                        CtorBinder::Simple(binder) => Ok(binder),
                        CtorBinder::StrictPositive { .. } => {
                            Err("record fields must be non-recursive".to_string())
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let selected = arena.exp_bound(field_count - 1 - field);
                let case = crate::raw::utils::assoc_lam(arena, case_telescope, selected);
                let elimination = arena.alloc(ExpNode::IndElim {
                    indspec: inductive,
                    elim: arena.exp_bound(0),
                    return_type: motive,
                    cases: vec![case],
                });
                let projection = arena.alloc(ExpNode::Lam {
                    var: structure_var,
                    ty: record_ty,
                    body: elimination,
                });
                let body = crate::raw::utils::assoc_lam(arena, parameters.clone(), projection);
                (name, ty, body)
            };

            let mut context = self.module_manager.current_context(&self.crate_env);
            CheckSession::new(&self.crate_env, module, &mut context)
                .check_pts(body, ty)
                .map_err(|error| {
                    format!(
                        "Generated projection {} does not typecheck: {error:?}",
                        name.as_str()
                    )
                })?;
            let definition = self
                .crate_env
                .add_definition(module, DefinedConstant::Pts { ty, body })?;
            projections.push((name, definition));
        }

        Ok(projections)
    }

    fn add_typed_program_inductive_decl(
        &mut self,
        type_name: &Identifier,
        parameters: &[RightBind],
        constructors: &[(Identifier, Vec<RightBind>, SExp)],
    ) -> Result<(), ElaborationError> {
        let module = self.module_manager.current();
        let inductive = self.crate_env.reserve_program_inductive(module);
        let reflected = self.crate_env.reserve_inductive(module);
        let type_name_symbol = self.crate_env.intern(type_name.as_str());
        let self_ty = self
            .crate_env
            .arena()
            .alloc(crate::raw::program::ValueTypeNode::Inductive {
                indspec: inductive,
                parameters: Vec::new(),
            });
        let mut scope = program_term_elaborator::ProgramScope::new();
        scope.bind_value_type_name(type_name_symbol, self_ty);

        let mut parameter_names = Vec::new();
        for RightBind { vars, ty } in parameters {
            if !matches!(ty.as_ref(), SExp::ValueType) {
                return Err("Program datatype parameters must have type \\VType".into());
            }
            for variable in vars {
                let variable = self.crate_env.intern(variable.as_str());
                parameter_names.push(variable);
                scope.push_type(variable);
            }
        }

        let mut constructor_names = Vec::new();
        let mut constructor_specs = Vec::new();
        for (constructor_name, fields, result) in constructors {
            if constructor_names
                .iter()
                .any(|existing: &Identifier| existing == constructor_name)
            {
                return Err(format!(
                    "duplicate Program constructor name: {}",
                    constructor_name.as_str()
                )
                .into());
            }
            constructor_names.push(constructor_name.clone());
            let mut elaborated_fields = Vec::new();
            for RightBind { vars, ty } in fields {
                let surface_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                let field_ty = scope.elaborate_value_type(&surface_ty, self)?;
                if vars.is_empty() {
                    elaborated_fields.push((SymbolId::ANONYMOUS, field_ty));
                } else {
                    for variable in vars {
                        let variable = self.crate_env.intern(variable.as_str());
                        elaborated_fields.push((variable, field_ty));
                    }
                }
            }
            let result: ValueTypeExp = result.clone().try_into()?;
            let result = scope.elaborate_value_type(&result, self)?;
            let crate::raw::program::ValueTypeNode::Inductive {
                indspec,
                parameters,
            } = self.crate_env.arena().get(result)
            else {
                return Err(format!(
                    "Program constructor {} must return {}",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            };
            let exact_parameters = parameters.is_empty()
                || (parameters.len() == parameter_names.len()
                    && parameters.iter().enumerate().all(|(index, parameter)| {
                        matches!(
                            self.crate_env.arena().get(*parameter),
                            crate::raw::program::ValueTypeNode::Bound(bound)
                                if bound == parameter_names.len() - 1 - index
                        )
                    }));
            if indspec != inductive || !exact_parameters {
                return Err(format!(
                    "Program constructor {} must return {} with all datatype parameters",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            }
            constructor_specs.push(ProgramConstructorSpec::new(elaborated_fields));
        }

        let program_spec = ProgramInductiveTypeSpecs::unchecked(
            parameter_names.clone(),
            constructor_specs,
            reflected,
        );
        self.crate_env
            .define_program_inductive(inductive, program_spec);

        let reflected_parameters = parameter_names
            .iter()
            .map(|name| (*name, self.crate_env.arena().sort(Sort::Set(0))))
            .collect();
        let reflected_constructors = self.crate_env.program_inductive(inductive).constructors().iter().map(|constructor| {
            let telescope = constructor.fields().iter().enumerate().map(|(field_index, (name, ty))| {
                let ty = crate::raw::reflection::reflect_value_type(&self.crate_env, *ty)
                    .map_err(|error| format!("cannot reflect Program constructor field: {error}"))?;
                let ty = crate::raw::calculus::shift_bound_indices(
                    self.crate_env.arena(),
                    ty,
                    field_index,
                    0,
                );
                if !exp_contains_inductive(self.crate_env.arena(), ty, reflected) {
                    return Ok(CtorBinder::Simple((*name, ty)));
                }
                let (binders, tail) = crate::raw::utils::decompose_prod(self.crate_env.arena(), ty);
                let (head, self_indices) = crate::raw::utils::decompose_app(self.crate_env.arena(), tail);
                if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == reflected) {
                    return Err("reflected recursive Program field is not strictly positive".to_string());
                }
                Ok(CtorBinder::StrictPositive { binders, self_indices })
            }).collect::<Result<Vec<_>, String>>()?;
            Ok(crate::raw::inductive::CtorType { telescope, indices: Vec::new() })
        }).collect::<Result<Vec<_>, String>>()?;
        self.crate_env.define_inductive(
            reflected,
            InductiveTypeSpecs::unchecked(
                reflected_parameters,
                Vec::new(),
                Sort::Set(0),
                reflected_constructors,
            ),
        );

        let mut program_context = self.module_manager.current_program_context(&self.crate_env);
        self.crate_env
            .program_inductive(inductive)
            .validate(
                &mut ProgramCheckSession::new(&self.crate_env, &mut program_context),
                inductive,
            )
            .map_err(|error| format!("Ill-formed Program datatype: {error:?}"))?;
        let mut reflected_context =
            crate::raw::reflection::reflect_context(&self.crate_env, &program_context)
                .map_err(|error| format!("cannot reflect Program context: {error}"))?;
        self.crate_env
            .inductive(reflected)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, &mut reflected_context),
                reflected,
            )
            .map_err(|error| format!("Ill-formed reflected datatype: {error:?}"))?;
        self.module_manager.publish_reserved_program_inductive(
            &mut self.crate_env,
            type_name.clone(),
            constructor_names,
            inductive,
            reflected,
        )?;
        Ok(())
    }

    fn module_add_rec(&mut self, module: &Module) -> Result<(), ElaborationError> {
        let Module {
            name,
            parameters,
            body,
            ..
        } = module;
        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });

        let ModuleBody::Inline(declarations) = body else {
            return Err(format!(
                "External module '{}' was not resolved; use the file loader",
                name.as_str()
            )
            .into());
        };

        // 1. before adding child, check well-typedness ness of parameters
        {
            self.metavariables.clear();
            let reserved_module = self
                .module_manager
                .reserve_child_and_moveto(&mut self.crate_env, name.0.clone());
            let mut ctx = self.module_manager.current_context(&self.crate_env);

            let mut parameter_position = 0_u32;

            let mut local_scope = term_elaborator::LocalScope::default();
            let mut program_scope = program_term_elaborator::ProgramScope::new();

            for RightBind { vars, ty } in parameters.iter() {
                let parameter_kind = if matches!(ty.as_ref(), SExp::ValueType) {
                    ModuleParameterKind::ProgramType
                } else if let Ok(mut pts_ty) = local_scope.elab_exp(ty, self) {
                    if !self.metavariables.is_empty() {
                        self.metavariables
                            .infer_sort(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                pts_ty,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                        pts_ty = self.metavariables.zonk(&self.crate_env, pts_ty);
                    }
                    CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx)
                        .infer_sort(pts_ty)
                        .map_err(|error| {
                            format!("Module parameter type is not Set/Prop: {error:?}")
                        })?;
                    ModuleParameterKind::Pts { ty: pts_ty }
                } else {
                    let program_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                    let program_ty = program_scope.elaborate_value_type(&program_ty, self)?;
                    let mut program_context = program_scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_value_type(program_ty)
                        .map_err(|error| {
                            format!(
                                "Program module parameter has an ill-formed value type: {error:?}"
                            )
                        })?;
                    ModuleParameterKind::ProgramValue { ty: program_ty }
                };

                for v in vars {
                    let symbol = self.crate_env.intern(v.as_str());
                    let position = parameter_position;
                    let parameter_id = ModuleParamId {
                        module: reserved_module,
                        position,
                    };
                    self.crate_env.add_module_parameter(
                        reserved_module,
                        ModuleParameter {
                            name: symbol,
                            kind: parameter_kind,
                        },
                    );
                    parameter_position += 1;
                    match parameter_kind {
                        ModuleParameterKind::Pts { ty } => {
                            ctx.push(ExpContextEntry { var: symbol, ty });
                            local_scope.push_typed_decl_var_exp(
                                symbol,
                                ty,
                                self.crate_env.arena().exp_module_param(parameter_id),
                            );
                        }
                        ModuleParameterKind::ProgramType
                        | ModuleParameterKind::ProgramValue { .. } => {
                            // The parameter was just published, so rebuild the
                            // scope and resolve it through its stable module ID.
                            program_scope = program_term_elaborator::ProgramScope::new();
                        }
                    }
                }
            }
        }

        let mut ctx = self.module_manager.current_context(&self.crate_env);

        // 2. elaborate declarations
        for (index, decl) in declarations.iter().enumerate() {
            self.diagnostic_location = module.source.as_ref().map(|source| SourceLocation {
                source: source.clone(),
                span: module
                    .declaration_spans
                    .get(index)
                    .copied()
                    .unwrap_or(module.span),
            });
            self.metavariables.clear();
            let mut local_scope = LocalScope::default();
            match decl {
                ModuleItem::Definition {
                    owner,
                    name,
                    binders,
                    ty,
                    body,
                } => {
                    if let Some(owner) = owner {
                        let expected = self
                            .module_manager
                            .associated_parameter_count(&self.crate_env, &owner.type_name)
                            .ok_or_else(|| {
                                format!(
                                    "Associated item owner '{}' is not a type in this module",
                                    owner.type_name.as_str()
                                )
                            })?;
                        let found = owner
                            .parameters
                            .iter()
                            .map(|binder| binder.vars.len())
                            .sum::<usize>();
                        if expected != found {
                            return Err(format!(
                                "Associated definition {}::{} expects {} owner parameter(s), found {}",
                                owner.type_name.as_str(),
                                name.as_str(),
                                expected,
                                found,
                            )
                            .into());
                        }
                    }
                    let mut all_binders = owner
                        .as_ref()
                        .map(|owner| owner.parameters.clone())
                        .unwrap_or_default();
                    all_binders.extend(binders.clone());
                    let mut ty = ty.clone();
                    let mut body = body.clone();
                    for binder in all_binders.into_iter().rev() {
                        ty = SExp::Prod {
                            bind: Bind::Named(binder.clone()),
                            body: Box::new(ty),
                        };
                        body = SExp::Lam {
                            bind: Bind::Named(binder),
                            body: Box::new(body),
                        };
                    }
                    let ty_elab = local_scope.elab_exp(&ty, self)?;
                    let body_elab = local_scope.elab_exp(&body, self)?;
                    if !self.metavariables.is_empty() {
                        self.check_term_with_metavariables(&mut ctx, body_elab, ty_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    let body_elab = self.metavariables.zonk(&self.crate_env, body_elab);
                    let kind = self
                        .validate_definition(&mut ctx, body_elab, ty_elab)
                        .map_err(|message| {
                            format!(
                                "Definition {} body does not check against declared type: {message}",
                                name.as_str()
                            )
                        })?;
                    debug_assert_eq!(kind, DefinitionKind::Pts);
                    let defined_constant = DefinedConstant::Pts {
                        ty: ty_elab,
                        body: body_elab,
                    };
                    if let Some(owner) = owner {
                        self.module_manager.add_associated_def(
                            &mut self.crate_env,
                            &owner.type_name,
                            name.clone(),
                            defined_constant,
                        )?;
                    } else {
                        self.module_manager.add_def(
                            &mut self.crate_env,
                            name.clone(),
                            defined_constant,
                        )?;
                    }
                }
                ModuleItem::ValueDefinition { name, ty, body } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_value_type(ty, self)?;
                    let body = scope.elaborate_value(body, self)?;
                    let (body, ty) = scope.check_value_with_metas(self, body, ty)?;
                    let certified_reflection = scope.certified_value(self, body);
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_value(body, ty)
                        .map_err(|error| {
                            format!(
                                "Program value definition {} is ill-typed: {error:?}",
                                name.as_str()
                            )
                        })?;
                    if scope.has_certificates()
                        && let Some(certificate) = certified_reflection
                    {
                        let reflected_ty =
                            crate::raw::reflection::reflect_value_type(&self.crate_env, ty)
                                .map_err(|error| error.to_string())?;
                        let mut context = self.module_manager.current_context(&self.crate_env);
                        CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut context,
                        )
                        .check_pts(certificate, reflected_ty)
                        .map_err(|error| {
                            format!(
                                "Program value definition {} has an invalid certificate: {error:?}",
                                name.as_str()
                            )
                        })?;
                    }
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramValue {
                            ty,
                            body,
                            certified_reflection,
                        },
                    )?;
                }
                ModuleItem::ComputationDefinition { name, ty, body } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_computation_type(ty, self)?;
                    let body = scope.elaborate_computation(body, self)?;
                    let (body, ty) = scope.check_computation_with_metas(self, body, ty)?;
                    let certified_reflection = scope.certified_computation(self, body);
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_computation(body, ty)
                        .map_err(|error| {
                            format!(
                                "Program computation definition {} is ill-typed: {error:?}",
                                name.as_str()
                            )
                        })?;
                    if scope.has_certificates()
                        && let Some(certificate) = certified_reflection
                    {
                        let reflected_ty =
                            crate::raw::reflection::reflect_computation_type(&self.crate_env, ty)
                                .map_err(|error| error.to_string())?;
                        let mut context = self.module_manager.current_context(&self.crate_env);
                        CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut context,
                        )
                        .check_pts(certificate, reflected_ty)
                        .map_err(|error| {
                            format!(
                                "Program computation definition {} has an invalid certificate: {error:?}",
                                name.as_str()
                            )
                        })?;
                    }
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramComputation {
                            ty,
                            body,
                            certified_reflection,
                        },
                    )?;
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    kind,
                    constructors,
                } => {
                    if matches!(kind, InductiveKind::Program) {
                        self.add_typed_program_inductive_decl(type_name, parameters, constructors)?;
                        continue;
                    }
                    let InductiveKind::Pts(sort) = kind else {
                        unreachable!();
                    };
                    let type_name_var = self.crate_env.intern(type_name.as_str());
                    let inductive = self
                        .crate_env
                        .reserve_inductive(self.module_manager.current());
                    let type_name_exp = self.crate_env.arena().alloc(ExpNode::IndType {
                        indspec: inductive,
                        parameters: vec![],
                    });
                    // register type name as binded var
                    local_scope.push_decl_var_exp(type_name_var, type_name_exp);

                    // elaborate parameters and indices
                    // binding is memorized in local scope
                    let mut parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    let mut indices_elab =
                        local_scope.elab_telescope_bind_in_decl(indices, self)?;
                    if !self.metavariables.is_empty() {
                        self.finish_metavariables()?;
                        for (_, ty) in &mut parameter_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                        for (_, ty) in &mut indices_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                    }

                    // elaborate constructors
                    let mut ctor_names = vec![];
                    let mut ctor_type_elabs = vec![];

                    for (ctor_name, rightbinds, ends) in constructors {
                        ctor_names.push(ctor_name.clone());

                        let (telescope, ends_elab) = {
                            let term = {
                                let mut term: SExp = ends.clone();
                                for bd in rightbinds.iter().rev() {
                                    term = SExp::Prod {
                                        bind: crate::syntax::Bind::Named(bd.clone()),
                                        body: Box::new(term),
                                    };
                                }
                                term
                            };
                            let mut term_elab = local_scope.elab_exp(&term, self)?;
                            if self
                                .metavariables
                                .contains_unsolved(&self.crate_env, term_elab)
                            {
                                local_scope.infer_elaborated(term_elab, self)?;
                                self.finish_metavariables()?;
                                term_elab = self.metavariables.zonk(&self.crate_env, term_elab);
                            }
                            crate::raw::utils::decompose_prod(self.crate_env.arena(), term_elab)
                        };

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            if exp_contains_inductive(self.crate_env.arena(), e, inductive) {
                                // strict positive case
                                let (inner_binders, inner_tail) =
                                    crate::raw::utils::decompose_prod(self.crate_env.arena(), e);
                                for (_, it) in inner_binders.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *it,
                                        inductive,
                                    ) {
                                        return Err("Ctor contains inductive type name  in non-strictly positive position".into());
                                    }
                                }
                                let (head, tail) = crate::raw::utils::decompose_app(
                                    self.crate_env.arena(),
                                    inner_tail,
                                );
                                if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == inductive)
                                {
                                    return Err("Constructor binder type head does not match inductive type name {type_name_var}".into());
                                }

                                for tail_elm in tail.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *tail_elm,
                                        inductive,
                                    ) {
                                        return Err("Constructor binder type tail contains inductive type name in non-strictly positive position".into());
                                    }
                                }
                                ctor_binders.push(CtorBinder::StrictPositive {
                                    binders: inner_binders,
                                    self_indices: tail,
                                });
                            } else {
                                // simple case
                                ctor_binders.push(CtorBinder::Simple((v, e)));
                            }
                        }

                        let (head, tail) =
                            crate::raw::utils::decompose_app(self.crate_env.arena(), ends_elab);
                        if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == inductive)
                        {
                            return Err(
                                "Constructor type head does not match inductive type name".into()
                            );
                        }

                        for tail_elm in tail.iter() {
                            if exp_contains_inductive(self.crate_env.arena(), *tail_elm, inductive)
                            {
                                return Err("Constructor type tail contains inductive type name in non-strictly positive position".into());
                            }
                        }

                        ctor_type_elabs.push(crate::raw::inductive::CtorType {
                            telescope: ctor_binders,
                            indices: tail,
                        });
                    }

                    let indspec = InductiveTypeSpecs::unchecked(
                        parameter_elab,
                        indices_elab,
                        *sort,
                        ctor_type_elabs,
                    );

                    self.crate_env.define_inductive(inductive, indspec);
                    let spec = self.crate_env.inductive(inductive).clone();
                    spec.validate(
                        &mut CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                        ),
                        inductive,
                    )
                    .map_err(|error| {
                        format!("Ill-formed inductive type specification: {error:?}")
                    })?;
                    self.module_manager.publish_reserved_inductive(
                        &mut self.crate_env,
                        type_name.clone(),
                        ctor_names,
                        inductive,
                    )?;
                }
                ModuleItem::Record {
                    type_name,
                    parameters,
                    sort,
                    fields,
                } => {
                    // treat record as inductive type with one constructor without recursive definition
                    // no register of type name as binded var since no recursive definition

                    // elaborate parameters
                    // binding is memorized in local scope
                    let mut parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    if !self.metavariables.is_empty() {
                        self.finish_metavariables()?;
                        for (_, ty) in &mut parameter_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                    }

                    // elaborate fields as constructors
                    let mut telescope = vec![];
                    let mut fields_get: Vec<(SymbolId, Exp)> = vec![];
                    for (field_name, field_ty) in fields {
                        let field_name_var = self.crate_env.intern(field_name.as_str());
                        let mut field_ty_elab = local_scope.elab_exp(field_ty, self)?;
                        if self
                            .metavariables
                            .contains_unsolved(&self.crate_env, field_ty_elab)
                        {
                            local_scope.infer_elaborated(field_ty_elab, self)?;
                            self.finish_metavariables()?;
                            field_ty_elab = self.metavariables.zonk(&self.crate_env, field_ty_elab);
                        }
                        fields_get.push((field_name_var, field_ty_elab));
                        // field may depend on previous fields
                        local_scope.push_typed_decl_var(field_name_var, field_ty_elab);
                        telescope.push(CtorBinder::Simple((field_name_var, field_ty_elab)));
                    }

                    let indspec = InductiveTypeSpecs::unchecked(
                        parameter_elab,
                        vec![],
                        *sort,
                        vec![crate::raw::inductive::CtorType {
                            telescope,
                            indices: vec![],
                        }],
                    );

                    let inductive = self
                        .crate_env
                        .reserve_inductive(self.module_manager.current());
                    self.crate_env.define_inductive(inductive, indspec);
                    self.crate_env
                        .inductive(inductive)
                        .clone()
                        .validate(
                            &mut CheckSession::new(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                            ),
                            inductive,
                        )
                        .map_err(|error| format!("Ill-formed structure: {error:?}"))?;
                    let projections = self.add_record_projection_definitions(inductive)?;
                    self.module_manager.publish_reserved_record(
                        &mut self.crate_env,
                        type_name.clone(),
                        inductive,
                        projections,
                    )?;
                }
                ModuleItem::ChildModule { module } => {
                    self.module_add_rec(module)?;
                }
                ModuleItem::Import { path, import_name } => {
                    if self
                        .crate_env
                        .module(self.module_manager.current())
                        .import(import_name.as_str())
                        .is_some()
                    {
                        return Err(format!(
                            "Module import '{}' is already defined",
                            import_name.as_str()
                        )
                        .into());
                    }
                    let (from, calls) = match path {
                        ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                            (Some(*back_parent), calls)
                        }
                        ModuleInstantiatePath::FromRoot { calls } => (None, calls),
                    };

                    let mut source = if let Some(back_parent) = from {
                        let mut module = self.module_manager.current();
                        for _ in 0..back_parent {
                            module = self
                                .crate_env
                                .module(module)
                                .parent()
                                .ok_or("already at root module")?;
                        }
                        module
                    } else {
                        self.crate_env.root_module()
                    };
                    let mut program_substitutions = Vec::new();
                    let mut program_scope = program_term_elaborator::ProgramScope::new();
                    let mut args = Vec::with_capacity(calls.len());
                    for (child_name, supplied) in calls.iter() {
                        let child = self
                            .crate_env
                            .module(source)
                            .children()
                            .iter()
                            .copied()
                            .find(|child| {
                                self.crate_env.module(*child).name() == child_name.as_str()
                            })
                            .ok_or_else(|| {
                                format!("child module '{}' was not found", child_name.as_str())
                            })?;
                        let parameters = self.crate_env.module(child).parameters().to_vec();
                        if supplied.len() != parameters.len() {
                            return Err(format!(
                                "module '{}' argument count mismatch",
                                child_name.as_str()
                            )
                            .into());
                        }
                        let mut elaborated = Vec::with_capacity(supplied.len());
                        for (position, ((name, expression), parameter)) in
                            supplied.iter().zip(parameters).enumerate()
                        {
                            if name.as_str() != self.crate_env.symbol(parameter.name) {
                                return Err(format!(
                                    "module '{}' argument name mismatch",
                                    child_name.as_str()
                                )
                                .into());
                            }
                            let argument = match parameter.kind {
                                ModuleParameterKind::Pts { .. } => {
                                    ModuleArgument::Pts(local_scope.elab_exp(expression, self)?)
                                }
                                ModuleParameterKind::ProgramType => {
                                    let syntax: ValueTypeExp = expression.clone().try_into()?;
                                    let ty = program_scope.elaborate_value_type(&syntax, self)?;
                                    ModuleArgument::ProgramType(ty)
                                }
                                ModuleParameterKind::ProgramValue { ty } => {
                                    let syntax: ValueExp = expression.clone().try_into()?;
                                    let value = program_scope.elaborate_value(&syntax, self)?;
                                    let expected =
                                        crate::raw::program_calculus::subst_value_type_module_params(
                                            self.crate_env.arena(),
                                            ty,
                                            &program_substitutions,
                                        );
                                    let (value, _) = program_scope
                                        .check_value_with_metas(self, value, expected)?;
                                    ModuleArgument::ProgramValue(value)
                                }
                            };
                            program_substitutions.push((
                                ModuleParamId {
                                    module: child,
                                    position: position as u32,
                                },
                                argument,
                            ));
                            elaborated.push((name.clone(), argument));
                        }
                        args.push((child_name.clone(), elaborated));
                        source = child;
                    }
                    program_scope.finish_metas()?;
                    for (_, arguments) in &mut args {
                        for (_, argument) in arguments {
                            match argument {
                                ModuleArgument::ProgramType(ty) => {
                                    *ty = program_scope.zonk_module_value_type(self, *ty);
                                    ProgramCheckSession::new(
                                        &self.crate_env,
                                        &mut Vec::new(),
                                    )
                                    .check_value_type(*ty)
                                    .map_err(|error| {
                                        format!(
                                            "Program type module argument is ill-formed: {error:?}"
                                        )
                                    })?;
                                }
                                ModuleArgument::ProgramValue(value) => {
                                    *value = program_scope.zonk_module_value(self, *value);
                                }
                                ModuleArgument::Pts(_) => {}
                            }
                        }
                    }

                    self.solve_module_arguments(&mut ctx, from, &mut args)?;

                    let access_result = self
                        .module_manager
                        .instantiate_module(&mut self.crate_env, &mut ctx, from, args)
                        .map_err(|e| format!("Module instantiation failed: {}", e))?;

                    self.module_manager.add_import(
                        &mut self.crate_env,
                        import_name.clone(),
                        access_result,
                    )?;
                }
                ModuleItem::MathMacro {
                    name,
                    before,
                    after,
                } => self.module_manager.register_macro(
                    &self.crate_env,
                    name.clone(),
                    MacroKind::Math,
                    before.clone(),
                    after.clone(),
                )?,
                ModuleItem::UserMacro {
                    name,
                    before,
                    after,
                } => self.module_manager.register_macro(
                    &self.crate_env,
                    name.clone(),
                    MacroKind::Named,
                    before.clone(),
                    after.clone(),
                )?,
                ModuleItem::UseMacro {
                    import_name,
                    macro_name,
                } => self
                    .module_manager
                    .use_macro(&self.crate_env, import_name, macro_name)?,
                ModuleItem::Eval { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    self.outputs.push(Output::Exp(
                        crate::raw::calculus::reduce_one(&self.crate_env, exp_elab)
                            .unwrap_or(exp_elab),
                    ));
                }
                ModuleItem::Normalize { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    self.outputs
                        .push(Output::Exp(crate::raw::calculus::normalize(
                            &self.crate_env,
                            exp_elab,
                        )));
                }
                ModuleItem::ComputationEval { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let computation = scope.elaborate_computation(exp, self)?;
                    let computation = if scope.has_metas() {
                        scope.infer_computation_with_metas(self, computation)?.0
                    } else {
                        computation
                    };
                    let reduced = crate::raw::program_calculus::reduce_computation_once(
                        &self.crate_env,
                        computation,
                    );
                    self.outputs
                        .push(Output::Computation(reduced.unwrap_or(computation)));
                }
                ModuleItem::ComputationNormalize { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let computation = scope.elaborate_computation(exp, self)?;
                    let computation = if scope.has_metas() {
                        scope.infer_computation_with_metas(self, computation)?.0
                    } else {
                        computation
                    };
                    self.outputs.push(
                        match crate::raw::program_calculus::evaluate_computation(
                            &self.crate_env,
                            computation,
                        ) {
                            crate::raw::program_calculus::Evaluation::Normal(result) => {
                                Output::Computation(result)
                            }
                            crate::raw::program_calculus::Evaluation::OutOfFuel(result) => {
                                Output::OutOfFuel(result)
                            }
                        },
                    );
                }
                ModuleItem::ValueCheck { exp, ty } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_value_type(ty, self)?;
                    let value = scope.elaborate_value(exp, self)?;
                    let (value, ty) = scope.check_value_with_metas(self, value, ty)?;
                    let mut context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut context)
                        .check_value(value, ty)
                        .map_err(|error| format!("Program value check failed: {error:?}"))?;
                    self.certify_program_query(
                        scope.context(),
                        crate::raw::program::Program::Value(value),
                        crate::raw::program::ProgramType::Value(ty),
                    )?;
                    self.outputs.push(Output::ValueType(ty));
                }
                ModuleItem::ComputationCheck { exp, ty } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_computation_type(ty, self)?;
                    let computation = scope.elaborate_computation(exp, self)?;
                    let (computation, ty) =
                        scope.check_computation_with_metas(self, computation, ty)?;
                    let mut context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut context)
                        .check_computation(computation, ty)
                        .map_err(|error| format!("Program computation check failed: {error:?}"))?;
                    self.certify_program_query(
                        scope.context(),
                        crate::raw::program::Program::Computation(computation),
                        crate::raw::program::ProgramType::Computation(ty),
                    )?;
                    self.outputs.push(Output::ComputationType(ty));
                }
                ModuleItem::ValueInfer { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let value = scope.elaborate_value(exp, self)?;
                    let (value, ty) = scope.infer_value_with_metas(self, value)?;
                    self.certify_program_query(
                        scope.context(),
                        crate::raw::program::Program::Value(value),
                        crate::raw::program::ProgramType::Value(ty),
                    )?;
                    self.outputs.push(Output::ValueType(ty));
                }
                ModuleItem::ComputationInfer { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let computation = scope.elaborate_computation(exp, self)?;
                    let (computation, ty) =
                        scope.infer_computation_with_metas(self, computation)?;
                    self.certify_program_query(
                        scope.context(),
                        crate::raw::program::Program::Computation(computation),
                        crate::raw::program::ProgramType::Computation(ty),
                    )?;
                    self.outputs.push(Output::ComputationType(ty));
                }
                ModuleItem::Check { exp, ty } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    if !self.metavariables.is_empty() {
                        self.check_term_with_metavariables(&mut ctx, exp_elab, ty_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    match CheckSession::new(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                    )
                    .check_pts(exp_elab, ty_elab)
                    {
                        Ok(()) => match self.certify_query(&ctx, exp_elab, ty_elab) {
                            Ok(()) => self.outputs.push(Output::Exp(ty_elab)),
                            Err(error) => self
                                .outputs
                                .push(Output::Message(format!("check failed: {error}"))),
                        },
                        Err(error) => self
                            .outputs
                            .push(Output::Message(format!("check failed: {error:?}"))),
                    }
                }
                ModuleItem::Infer { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    match CheckSession::new(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                    )
                    .infer_exp_judgement(exp_elab)
                    {
                        Ok(judgement) => match self.certify_query(&ctx, exp_elab, judgement.ty) {
                            Ok(()) => self.outputs.push(Output::Exp(judgement.ty)),
                            Err(error) => self
                                .outputs
                                .push(Output::Message(format!("infer failed: {error}"))),
                        },
                        Err(error) => self
                            .outputs
                            .push(Output::Message(format!("infer failed: {error:?}"))),
                    }
                }
            }
        }

        // 3. move back to parent
        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });
        self.module_manager
            .publish_current_module(&mut self.crate_env)?;
        self.module_manager.moveto_parent(&self.crate_env);
        Ok(())
    }
}
