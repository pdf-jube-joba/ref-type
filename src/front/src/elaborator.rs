use crate::macros::MacroKind;
use crate::raw::{
    calculus::{
        exp_contains_inductive, exp_subst_map, instantiate_telescope, remap_all_global_ids,
        shift_bound_indices,
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
    metavariables::{ElaborationError, MetaStore},
    output::Output,
    syntax::*,
};

mod declarations;
pub(crate) mod module_manager;
mod modules;
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

// do type checking
#[derive(Default)]
pub struct GlobalEnvironment {
    kernel_env: kernel::environment::Environment,
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
        // A bare CBV arrow in \Box/\box/\Force denotes its computation
        // translation. Function values remain explicit through \U(...).
        if matches!(expression, SExp::Prod { .. }) {
            let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
            return scope
                .elaborate_computation_type(&computation_ty, self)
                .map(crate::raw::program::ProgramType::ComputationType);
        }
        if let Ok(value_ty) = ValueTypeExp::try_from(expression.clone()) {
            return scope
                .elaborate_value_type(&value_ty, self)
                .map(crate::raw::program::ProgramType::ValueType);
        }
        let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
        scope
            .elaborate_computation_type(&computation_ty, self)
            .map(crate::raw::program::ProgramType::ComputationType)
    }

    fn elaborate_program(
        &mut self,
        expression: &SExp,
        ty: crate::raw::program::ProgramType,
    ) -> Result<(crate::raw::program::ProgramTerm, Option<Exp>), String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        match ty {
            crate::raw::program::ProgramType::ValueType(_) => {
                let value = ValueTermExp::try_from(expression.clone())?;
                let value = scope.elaborate_value(&value, self)?;
                let certificate = scope.certified_value(self, value);
                Ok((
                    crate::raw::program::ProgramTerm::ValueTerm(value),
                    certificate,
                ))
            }
            crate::raw::program::ProgramType::ComputationType(_) => {
                let computation = ComputationTermExp::try_from(expression.clone())?;
                let computation = scope.elaborate_computation(&computation, self)?;
                let certificate = scope.certified_computation(self, computation);
                Ok((
                    crate::raw::program::ProgramTerm::ComputationTerm(computation),
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

    pub fn kernel_env(&self) -> &kernel::environment::Environment {
        &self.kernel_env
    }

    pub fn crate_env(&self) -> &CrateEnv {
        &self.crate_env
    }

    pub fn outputs(&self) -> &[Output] {
        &self.outputs
    }

    fn finish_metavariables(&self) -> Result<(), ElaborationError> {
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
    pub fn add_new_module_to_root(&mut self, module: &Module) -> Result<(), ElaborationError> {
        self.diagnostic_location = None;
        self.module_manager.moveto_root();
        let result = self.module_add_rec(module).and_then(|()| {
            crate::lowering::Lowerer::new(&self.crate_env, &mut self.kernel_env)
                .lower_all()
                .map_err(ElaborationError::from)
        });
        match (result, self.diagnostic_location.take()) {
            (Err(error), Some(location)) => Err(ElaborationError::Located {
                location,
                error: Box::new(error),
            }),
            (result, _) => result,
        }
    }
}
