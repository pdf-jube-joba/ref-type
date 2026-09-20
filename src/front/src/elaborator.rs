use crate::macros::MacroKind;
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
    metavariables::{ElaborationError, MetaStore},
    output::Output,
    syntax::*,
};
use std::collections::{HashMap, HashSet};

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
    defer_child_modules: bool,
    predeclared_modules: bool,
    processed_modules: HashSet<ModuleId>,
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

    fn field_projection(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        field_name: &Identifier,
    ) -> Result<Exp, String> {
        let infer_type_e = self.infer(local_ctx, e).map_err(|error| {
            format!("Failed to infer type of expression for field projection: {error}")
        })?;
        let infer_type_e = whnf(&self.crate_env, infer_type_e);

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
            CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx)
                .infer_pts(e)
                .map_err(|error| {
                    format!("Failed to infer elaborated Set/Prop expression: {error:?}")
                })
        };
        *local_ctx = ctx.split_off(module_context_len);
        result
    }

    fn elaborate_boxed_computation_type(
        &mut self,
        expression: &SExp,
    ) -> Result<crate::raw::program::ComputationType, String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
        scope.elaborate_computation_type(&computation_ty, self)
    }

    fn elaborate_boxed_computation(
        &mut self,
        expression: &SExp,
    ) -> Result<crate::raw::program::ComputationTerm, String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let computation = ComputationTermExp::try_from(expression.clone())?;
        scope.elaborate_computation(&computation, self)
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
    fn predeclare_module_tree(
        &mut self,
        parent: ModuleId,
        module: &Module,
    ) -> Result<(), ElaborationError> {
        let child = self
            .crate_env
            .reserve_child_module(parent, module.name.0.clone());
        self.crate_env.publish_child_module(child)?;
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

    fn collect_module_tree<'a>(
        module: &'a Module,
        path: &mut Vec<String>,
        modules: &mut Vec<(Vec<String>, &'a Module)>,
    ) {
        path.push(module.name.0.clone());
        modules.push((path.clone(), module));
        if let ModuleBody::Inline(items) = &module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    Self::collect_module_tree(module, path, modules);
                }
            }
        }
        path.pop();
    }

    fn import_target(path: &ModuleInstantiatePath, module_path: &[String]) -> Option<Vec<String>> {
        let (mut base, calls) = match path {
            ModuleInstantiatePath::FromRoot { calls } => (Vec::new(), calls),
            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                let mut base = module_path.to_vec();
                for _ in 0..*back_parent {
                    base.pop()?;
                }
                (base, calls)
            }
            ModuleInstantiatePath::FromImport { .. } => return None,
        };
        base.extend(calls.iter().map(|(name, _)| name.0.clone()));
        Some(base)
    }

    fn module_order(modules: &[(Vec<String>, &Module)]) -> Result<Vec<usize>, ElaborationError> {
        let indices = modules
            .iter()
            .enumerate()
            .map(|(index, (path, _))| (path.clone(), index))
            .collect::<HashMap<_, _>>();
        let mut dependencies = vec![HashSet::new(); modules.len()];

        for (index, (path, module)) in modules.iter().enumerate() {
            if path.len() > 1 {
                dependencies[index].insert(
                    *indices
                        .get(&path[..path.len() - 1])
                        .ok_or("module parent was not predeclared")?,
                );
            }
            let ModuleBody::Inline(items) = &module.body else {
                continue;
            };
            let mut aliases = HashMap::new();
            for item in items {
                let ModuleItem::Import {
                    path: import,
                    import_name,
                } = item
                else {
                    continue;
                };
                let target = match import {
                    ModuleInstantiatePath::FromImport {
                        import_name: base,
                        calls,
                    } => aliases.get(base.as_str()).map(|base_path: &Vec<String>| {
                        let mut target = base_path.clone();
                        target.extend(calls.iter().map(|(name, _)| name.0.clone()));
                        target
                    }),
                    _ => Self::import_target(import, path),
                };
                if let Some(target) = target {
                    if let Some(target_index) = indices.get(&target)
                        && !target.starts_with(path)
                    {
                        dependencies[index].insert(*target_index);
                    }
                    aliases.insert(import_name.as_str().to_string(), target);
                }
            }
        }

        fn visit(
            index: usize,
            dependencies: &[HashSet<usize>],
            states: &mut [u8],
            order: &mut Vec<usize>,
        ) -> Result<(), ElaborationError> {
            match states[index] {
                2 => return Ok(()),
                1 => return Err("cyclic module import dependency".into()),
                _ => {}
            }
            states[index] = 1;
            for dependency in &dependencies[index] {
                visit(*dependency, dependencies, states, order)?;
            }
            states[index] = 2;
            order.push(index);
            Ok(())
        }

        let mut states = vec![0; modules.len()];
        let mut order = Vec::with_capacity(modules.len());
        for index in 0..modules.len() {
            visit(index, &dependencies, &mut states, &mut order)?;
        }
        Ok(order)
    }

    pub fn add_modules_to_root(&mut self, modules: &[Module]) -> Result<(), ElaborationError> {
        self.diagnostic_location = None;
        let mut scheduled = Vec::new();
        for module in modules {
            Self::collect_module_tree(module, &mut Vec::new(), &mut scheduled);
        }
        let order = Self::module_order(&scheduled)?;
        if order.iter().copied().eq(0..scheduled.len()) {
            for module in modules {
                self.add_new_module_to_root(module)?;
            }
            return Ok(());
        }

        self.predeclared_modules = true;
        self.processed_modules.clear();
        for module in modules {
            self.predeclare_module_tree(self.crate_env.root_module(), module)?;
        }

        let result = (|| {
            for index in order {
                let (path, module) = &scheduled[index];
                let module_id = self
                    .module_id_for_path(path)
                    .ok_or("module was not predeclared")?;
                if self.processed_modules.contains(&module_id) {
                    continue;
                }
                self.defer_child_modules = path.len() == 1 && Self::is_namespace_module(module);
                self.module_manager.moveto_root();
                for component in &path[..path.len() - 1] {
                    self.module_manager
                        .enter_existing_child(&self.crate_env, component)
                        .ok_or_else(|| {
                            ElaborationError::Message(format!(
                                "module parent '{}' was not predeclared",
                                component
                            ))
                        })?;
                }
                self.module_add_rec(module)?;
            }
            crate::lowering::Lowerer::new(&self.crate_env, &mut self.kernel_env)
                .lower_all()
                .map_err(ElaborationError::from)
        })();
        self.defer_child_modules = false;
        self.predeclared_modules = false;
        result
    }

    fn module_id_for_path(&self, path: &[String]) -> Option<ModuleId> {
        let mut module = self.crate_env.root_module();
        for component in path {
            module = self
                .crate_env
                .module(module)
                .children()
                .iter()
                .copied()
                .find(|child| self.crate_env.module(*child).name() == component)?;
        }
        Some(module)
    }

    fn is_namespace_module(module: &Module) -> bool {
        let ModuleBody::Inline(items) = &module.body else {
            return false;
        };
        !items.is_empty()
            && items
                .iter()
                .all(|item| matches!(item, ModuleItem::ChildModule { .. }))
    }

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
