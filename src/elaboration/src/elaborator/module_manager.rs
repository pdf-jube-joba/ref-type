use crate::raw::program::{ProgramContext, ProgramContextEntry};
#[cfg(test)]
use crate::raw::{environment::ModuleParameter, inductive::InductiveTypeSpecs};
use crate::raw::{
    environment::{
        ClosedNamespaceKey, CrateEnv, DeclarationRemapping, DefinedConstant, ModuleArgument,
        ModuleItem, ModuleParameterKind,
    },
    exp::{Exp, ExpContext, ExpContextEntry},
    ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId},
};
use crate::{
    hir::{Identifier, LocalAccess},
    items::{ModItemDefinition, ModItemInductive, ModItemProgramInductive, ModItemRecord},
    raw::{
        derivation::CheckSession,
        remapping::{exp_subst_map, remap_all_global_ids},
    },
};
use std::{cell::RefCell, collections::HashMap, sync::Arc};

#[derive(Debug, Clone)]
pub(crate) enum ItemAccessResult {
    Definition(ModItemDefinition),
    ReflectedDefinition(ModItemDefinition),
    Inductive(ModItemInductive),
    Record(ModItemRecord),
    ProgramInductive(ModItemProgramInductive),
    Expression(Exp),
    Argument(ModuleArgument),
    ProgramTypeParameter(ModuleParamId),
    ProgramValueParameter(ModuleParamId),
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub(crate) struct ModuleManager {
    current: ModuleId,
    #[serde(skip)]
    pub(crate) reference_location: Option<crate::hir::SourceLocation>,
    pub(crate) references: RefCell<Vec<crate::analysis::Reference>>,
    pub(crate) hir_module_bindings: HashMap<resolve::hir::BindingId, ModuleId>,
    pub(crate) hir_aliases: HashMap<resolve::hir::BindingId, ModuleId>,
    #[serde(skip)]
    pub(crate) hir_bindings: HashMap<resolve::hir::BindingId, resolve::Binding>,
    pub(crate) hir_modules: HashMap<resolve::hir::ModuleId, ModuleId>,
    #[serde(skip)]
    pub(crate) hir_imports: HashMap<resolve::hir::BindingId, resolve::Import>,
}

impl Default for ModuleManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleManager {
    pub(crate) fn new() -> Self {
        Self {
            current: ModuleId(0),
            reference_location: None,
            references: RefCell::default(),
            hir_bindings: HashMap::new(),
            hir_module_bindings: HashMap::new(),
            hir_aliases: HashMap::new(),
            hir_modules: HashMap::new(),
            hir_imports: HashMap::new(),
        }
    }

    pub(crate) fn current(&self) -> ModuleId {
        self.current
    }

    #[cfg(test)]
    fn add_child_and_moveto(
        &mut self,
        env: &mut CrateEnv,
        module_name: String,
        parameters: Vec<ModuleParameter>,
    ) -> Result<(), crate::error::Error> {
        self.current = env.add_child_module(self.current, module_name, parameters)?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn moveto_parent(&mut self, env: &CrateEnv) {
        if let Some(parent) = env.module(self.current).parent() {
            self.current = parent;
        }
    }

    #[cfg(test)]
    pub(crate) fn publish_current_module(
        &self,
        env: &mut CrateEnv,
    ) -> Result<(), crate::error::Error> {
        env.publish_child_module(self.current)
    }

    pub(crate) fn moveto(&mut self, module: ModuleId) {
        self.current = module;
    }

    #[cfg(test)]
    pub(crate) fn moveto_root(&mut self) {
        self.current = ModuleId(0);
    }

    pub(crate) fn current_context(&self, env: &CrateEnv) -> ExpContext {
        let mut context = Vec::new();
        let mut current = self.current;
        loop {
            let module = env.module(current);
            context.push(
                module
                    .parameters()
                    .iter()
                    .filter_map(|parameter| match parameter.kind {
                        ModuleParameterKind::Pts { ty } => Some(ExpContextEntry {
                            var: parameter.name,
                            ty,
                        }),
                        ModuleParameterKind::ProgramType
                        | ModuleParameterKind::ProgramValue { .. } => None,
                    })
                    .collect::<ExpContext>(),
            );
            if let Some(parent) = module.parent() {
                current = parent;
            } else {
                break;
            }
        }
        context.reverse();
        context.into_iter().flatten().collect()
    }

    pub(crate) fn current_program_context(&self, env: &CrateEnv) -> ProgramContext {
        let mut contexts = Vec::new();
        let mut current = self.current;
        loop {
            let module = env.module(current);
            contexts.push(
                module
                    .parameters()
                    .iter()
                    .filter_map(|parameter| match parameter.kind {
                        ModuleParameterKind::ProgramType => Some(ProgramContextEntry::ValueType {
                            var: parameter.name,
                        }),
                        ModuleParameterKind::ProgramValue { ty } => {
                            Some(ProgramContextEntry::ValueTerm {
                                var: parameter.name,
                                ty,
                            })
                        }
                        ModuleParameterKind::Pts { .. } => None,
                    })
                    .collect::<ProgramContext>(),
            );
            if let Some(parent) = module.parent() {
                current = parent;
            } else {
                break;
            }
        }
        contexts.reverse();
        contexts.into_iter().flatten().collect()
    }

    pub(crate) fn add_def(
        &self,
        env: &mut CrateEnv,
        name: Identifier,
        definition: DefinedConstant,
    ) -> Result<(), crate::error::Error> {
        let definition = env.add_definition(self.current, definition)?;
        env.publish_item(
            self.current,
            ModuleItem::Definition {
                name: name.0,
                definition,
            },
        )
    }

    pub(crate) fn add_associated_def(
        &self,
        env: &mut CrateEnv,
        owner: &Identifier,
        name: Identifier,
        definition: DefinedConstant,
    ) -> Result<(), crate::error::Error> {
        let definition = env.add_definition(self.current, definition)?;
        env.publish_associated_definition(self.current, owner.as_str(), name.0, definition)
    }

    pub(crate) fn associated_parameter_count(
        &self,
        env: &CrateEnv,
        owner: &Identifier,
    ) -> Option<usize> {
        match env.module(self.current).item(owner.as_str())? {
            ModuleItem::Inductive { inductive, .. } | ModuleItem::Record { inductive, .. } => {
                Some(env.inductive(*inductive).parameters().len())
            }
            ModuleItem::ProgramInductive { inductive, .. } => {
                Some(env.program_inductive(*inductive).parameters().len())
            }
            ModuleItem::Definition { .. } => None,
        }
    }

    #[cfg(test)]
    fn add_inductive(
        &self,
        env: &mut CrateEnv,
        type_name: Identifier,
        constructor_names: Vec<Identifier>,
        spec: InductiveTypeSpecs,
    ) -> Result<(), crate::error::Error> {
        let inductive = env.add_inductive(self.current, spec);
        env.publish_item(
            self.current,
            ModuleItem::Inductive {
                name: type_name.0,
                constructor_names: constructor_names.into_iter().map(|name| name.0).collect(),
                associated_definitions: Vec::new(),
                inductive,
            },
        )
    }

    pub(crate) fn publish_reserved_inductive(
        &self,
        env: &mut CrateEnv,
        type_name: Identifier,
        constructor_names: Vec<Identifier>,
        inductive: InductiveId,
    ) -> Result<(), crate::error::Error> {
        env.publish_item(
            self.current,
            ModuleItem::Inductive {
                name: type_name.0,
                constructor_names: constructor_names.into_iter().map(|name| name.0).collect(),
                associated_definitions: Vec::new(),
                inductive,
            },
        )
    }

    pub(crate) fn publish_reserved_program_inductive(
        &self,
        env: &mut CrateEnv,
        type_name: Identifier,
        constructor_names: Vec<Identifier>,
        inductive: ProgramInductiveId,
        reflected: InductiveId,
        record_fields: Option<Vec<String>>,
    ) -> Result<(), crate::error::Error> {
        env.publish_item(
            self.current,
            ModuleItem::ProgramInductive {
                record_fields,
                name: type_name.0,
                constructor_names: constructor_names.into_iter().map(|name| name.0).collect(),
                associated_definitions: Vec::new(),
                inductive,
                reflected,
            },
        )
    }

    pub(crate) fn publish_reserved_record(
        &self,
        env: &mut CrateEnv,
        type_name: Identifier,
        inductive: InductiveId,
        associated_definitions: Vec<(Identifier, DefId)>,
    ) -> Result<(), crate::error::Error> {
        env.publish_item(
            self.current,
            ModuleItem::Record {
                name: type_name.0,
                associated_definitions: associated_definitions
                    .into_iter()
                    .map(|(name, definition)| (name.0, definition))
                    .collect(),
                inductive,
            },
        )
    }

    pub(crate) fn add_import(
        &self,
        env: &mut CrateEnv,
        import_name: Identifier,
        binding: ModuleId,
    ) -> Result<(), crate::error::Error> {
        env.publish_import(self.current, import_name.0, binding)
    }

    pub(crate) fn get_moditem_record(
        &self,
        env: &CrateEnv,
        inductive: InductiveId,
    ) -> Option<ModItemRecord> {
        let ModuleItem::Record {
            name,
            inductive,
            associated_definitions,
        } = env.record_for_inductive(inductive)?
        else {
            return None;
        };
        Some(ModItemRecord {
            type_name: Identifier(name.clone()),
            inductive: *inductive,
            associated_definitions: associated_definitions
                .iter()
                .map(|(name, definition)| (Identifier(name.clone()), *definition))
                .collect(),
        })
    }

    pub(crate) fn get_moditem_program_record(
        &self,
        env: &CrateEnv,
        inductive: ProgramInductiveId,
    ) -> Option<ModItemProgramInductive> {
        let item = env.program_record_for_inductive(inductive)?;
        let ItemAccessResult::ProgramInductive(record) = convert_item(item) else {
            return None;
        };
        Some(record)
    }

    #[cfg(test)]
    fn resolve_start(
        &self,
        env: &CrateEnv,
        back_parent: Option<usize>,
    ) -> Result<ModuleId, crate::error::Error> {
        let Some(back_parent) = back_parent else {
            return Ok(env.root_module());
        };
        let mut module = self.current;
        for _ in 0..back_parent {
            module = env
                .module(module)
                .parent()
                .ok_or(crate::error::Error::Invalid(
                    crate::error::Invalid::CannotGoBackParentAlreadyAtRootModule,
                ))?;
        }
        Ok(module)
    }

    #[cfg(test)]
    pub(crate) fn bind_namespace(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, crate::error::Error> {
        let source = self.resolve_start(env, back_parent)?;
        self.bind_namespace_from(env, context, source, None, calls)
    }

    #[cfg(test)]
    pub(crate) fn bind_namespace_from(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        source: ModuleId,
        base: Option<ModuleId>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, crate::error::Error> {
        self.bind_namespace_in_context(env, context, &Vec::new(), source, base, calls)
    }

    pub(crate) fn bind_namespace_in_context(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        program_context: &crate::raw::program::ProgramContext,
        mut source: ModuleId,
        base: Option<ModuleId>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, crate::error::Error> {
        let _cost = timing::costs::Scope::enter("namespace.bind");
        // A child's argument type can refer to declarations imported by its
        // parameterized parent. Substituting parameters in the type expression
        // alone does not specialize those declarations. Publish the parent
        // namespace first so the child is checked with its declaration map.
        let mut has_arguments = false;
        let split = calls.iter().position(|(_, arguments)| {
            let dependent_stage = has_arguments && !arguments.is_empty();
            has_arguments |= !arguments.is_empty();
            dependent_stage
        });
        if let Some(split) = split {
            let mut prefix = calls;
            let suffix = prefix.split_off(split);
            let parent = self.bind_namespace_in_context(
                env,
                context,
                program_context,
                source,
                base,
                prefix,
            )?;
            return self.bind_namespace_in_context(
                env,
                context,
                program_context,
                env.binding(parent).source,
                Some(parent),
                suffix,
            );
        }
        let mut profile = super::profiling::ProfileTimer::start("REF_TYPE_PROFILE_MODULES", || {
            format!(
                "modules phase=reference from={:?} source={source:?} base={base:?} context={:?} arguments={calls:?} environment={:?} location={:?}",
                self.current,
                env.context_id(context),
                env.kernel.borrow().diagnostic_version(),
                self.reference_location
                    .as_ref()
                    .map(|location| (&location.source.id, location.span))
            )
        });
        let (mut substitutions, mut remapping) = base.map_or_else(
            || (Vec::new(), DeclarationRemapping::default()),
            |base| {
                let base = env.binding(base);
                let mut remapping = env.remapping(base.remapping).clone();
                // Child signatures use declarations from the original parent,
                // even when this namespace was reached through a re-export.
                // Its latest materialization map can otherwise contain only
                // the intermediate specialized IDs.
                for (&materialized, &original) in &base.definition_origins {
                    remapping.definition_ids.insert(original, materialized);
                }
                (base.arguments.clone(), remapping)
            },
        );
        let mut reflected_substitutions = substitutions
            .iter()
            .map(|(parameter, argument)| {
                let reflected = match argument {
                    ModuleArgument::Pts(exp) => *exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(env, *ty).map_err(|error| {
                            crate::error::Error::from(error).context(
                                crate::error::Context::CannotReflectProgramTypeModuleArgument,
                            )
                        })?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        env,
                        crate::raw::program::ProgramTerm::ValueTerm(*value),
                    )
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::CannotReflectProgramValueModuleArgument)
                    })?,
                };
                Ok((*parameter, reflected))
            })
            .collect::<Result<Vec<_>, crate::error::Error>>()?;
        let mut route = Vec::new();

        for (child_name, arguments) in calls {
            let child = self.hir_child(env, source, &child_name).ok_or_else(|| {
                crate::error::Error::UnknownChildInModule {
                    name: (child_name.as_str()).to_string(),
                    module: (env.module(source).name()).to_string(),
                }
            })?;
            let parameters = env.module(child).parameters().to_vec();
            if arguments.len() != parameters.len() {
                return Err(crate::error::Error::ModuleArgumentArityMismatch {
                    module: (child_name.as_str()).to_string(),
                    expected: parameters.len(),
                    actual: arguments.len(),
                });
            }
            for ((position, (argument_name, argument)), parameter) in
                arguments.iter().enumerate().zip(parameters)
            {
                if argument_name.as_str() != env.symbol(parameter.name) {
                    return Err(crate::error::Error::ModuleArgumentLabelMismatch {
                        module: (child_name.as_str()).to_string(),
                        expected: (env.symbol(parameter.name)).to_string(),
                        actual: (argument_name.as_str()).to_string(),
                    });
                }
                match (parameter.kind, argument) {
                    (ModuleParameterKind::Pts { ty }, ModuleArgument::Pts(argument)) => {
                        // Make implicit captures explicit before either remapping
                        // or substitution. Materializing an already specialized
                        // alias would substitute its argument telescope twice.
                        let expected =
                            crate::kernel_bridge::logical(env, context, &[ty], |_, _, terms| {
                                Ok(Exp(terms[0]))
                            })?;
                        let expected = remap_all_global_ids(
                            env.arena(),
                            expected,
                            &remapping.definition_ids,
                            &remapping.inductive_ids,
                            &remapping.program_inductive_ids,
                        );
                        let expected =
                            exp_subst_map(env.arena(), expected, &reflected_substitutions);
                        CheckSession::new(env, context)
                            .check_pts(*argument, expected)
                            .map_err(|error| {
                                if std::env::var_os("REF_TYPE_DEBUG_CONVERSION").is_some() {
                                    eprintln!(
                                        "checked module argument {}.{}: {}\nexpected: {}\nbase: {base:?}, source: {source:?}, substitutions: {substitutions:?}",
                                        child_name.as_str(),
                                        argument_name.as_str(),
                                        crate::raw::printing::format_exp(env, *argument),
                                        crate::raw::printing::format_exp(env, expected),
                                    );
                                    if let crate::raw::exp::ExpNode::ModuleParam(parameter) = env.arena().get(*argument) {
                                        eprintln!("argument classifier: {:?}", env.module_parameter_opt(parameter));
                                    }
                                }
                                crate::error::Error::from(error).context(
                                    crate::error::Context::ModuleArgument {
                                        module: (child_name.as_str()).to_owned(),
                                        argument: (argument_name.as_str()).to_owned(),
                                    },
                                )
                            })?;
                    }
                    (ModuleParameterKind::ProgramType, ModuleArgument::ProgramType(ty)) => {
                        crate::raw::program_derivation::ProgramCheckSession::new(
                            env,
                            &mut program_context.clone(),
                        )
                        .check_value_type(*ty)
                        .map_err(|error| {
                            crate::error::Error::from(error).context(
                                crate::error::Context::ProgramTypeModuleArgumentIsIllFormed,
                            )
                        })?;
                    }
                    (
                        ModuleParameterKind::ProgramValue { ty },
                        ModuleArgument::ProgramValue(value),
                    ) => {
                        let expected = crate::raw::remapping::remap_value_type_global_ids(
                            env.arena(),
                            ty,
                            &remapping.definition_ids,
                            &remapping.program_inductive_ids,
                        );
                        let expected = crate::raw::remapping::subst_value_type_module_params(
                            env.arena(),
                            expected,
                            &substitutions,
                        );
                        crate::raw::program_derivation::ProgramCheckSession::new(
                            env,
                            &mut program_context.clone(),
                        )
                        .check_value_term(*value, expected)
                        .map_err(|error| {
                            crate::error::Error::from(error).context(
                                crate::error::Context::ProgramValueModuleArgumentIsIllTyped,
                            )
                        })?;
                    }
                    _ => {
                        return Err(crate::error::Error::ModuleArgumentCategoryMismatch {
                            module: (child_name.as_str()).to_string(),
                            argument: (argument_name.as_str()).to_string(),
                        });
                    }
                }
                let parameter_id = ModuleParamId {
                    module: child,
                    position: position as u32,
                };
                let reflected = match argument {
                    ModuleArgument::Pts(exp) => *exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(env, *ty).map_err(|error| {
                            crate::error::Error::from(error).context(
                                crate::error::Context::CannotReflectProgramTypeModuleArgument,
                            )
                        })?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        env,
                        crate::raw::program::ProgramTerm::ValueTerm(*value),
                    )
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::CannotReflectProgramValueModuleArgument)
                    })?,
                };
                substitutions.push((parameter_id, *argument));
                reflected_substitutions.push((parameter_id, reflected));
            }
            source = child;
            route.push(child);
        }

        if route.is_empty() {
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::ModuleInstantiationPathMustContainAtLeastOneModule,
            ));
        }

        // Repeated closed instantiations can share the entire immutable graph,
        // including its namespaces, rather than allocating provisional IDs for
        // declarations that the specialization cache will immediately reuse.
        // Arguments containing local variables stay on the uncached path.
        // A closed instantiation is independent of unused caller bindings.
        // Source namespaces grow
        // only by appending items/bindings, so their lengths invalidate entries
        // recorded before a source module has finished elaborating.
        let namespace_key = (program_context.is_empty()
            && env.namespace_arguments_shareable(&substitutions))
        .then(|| ClosedNamespaceKey {
            base,
            route: route
                .iter()
                .map(|&id| {
                    (
                        id,
                        env.module(id).items().len(),
                        env.module(id).bindings().len(),
                    )
                })
                .collect(),
            arguments: substitutions.clone(),
        });
        if let Some(key) = &namespace_key
            && let Some((binding, dependencies)) = env.closed_namespaces.get(key).cloned()
        {
            for dependency in dependencies {
                env.attach_namespace_binding(self.current, dependency);
            }
            return Ok(binding);
        }
        // Conversion-equivalent closed arguments give the same nominal graph,
        // just as in the declaration specialization cache. Reuse that graph
        // before reserving thousands of already canonical declarations.
        if let Some(key) = &namespace_key {
            let reused = env.closed_namespaces.iter().find_map(|(candidate, value)| {
                (candidate.base == key.base
                    && candidate.route == key.route
                    && env.namespace_arguments_equal(&candidate.arguments, &key.arguments))
                .then(|| value.clone())
            });
            if let Some((binding, dependencies)) = reused {
                for &dependency in &dependencies {
                    env.attach_namespace_binding(self.current, dependency);
                }
                env.closed_namespaces
                    .insert(key.clone(), (binding, dependencies));
                return Ok(binding);
            }
        }
        let mut result_bindings = Vec::new();

        if let Some(timer) = &mut profile {
            timer.checkpoint("modules phase=arguments");
        }
        let cache_hits = std::cell::Cell::new(0usize);
        let cache_misses = std::cell::Cell::new(0usize);
        // Reserve stable IDs and publish only metadata. Declaration bodies are
        // transformed by CrateEnv when one of these IDs is first requested.
        // Imported specialization arguments may refer to any declaration in the
        // enclosing route. Finalize those IDs before consulting the import cache.
        let mut materialization_sources: Vec<_> =
            route.iter().map(|&module| (module, module, true)).collect();
        for &source_module in &route {
            materialization_sources.extend(env.module(source_module).bindings().iter().map(|id| {
                let binding = env.binding(*id);
                (binding.source, binding.materialized, false)
            }));
        }

        // Repeated imports retain separate namespace metadata, even when their
        // declarations already share canonical IDs. Materializing all copies
        // makes an import chain grow exponentially. Coalesce only namespaces
        // with the same source, declaration identities, and argument environment;
        // distinct specializations and path components remain separate.
        let mut seen = HashMap::new();
        let mut unique_sources = Vec::new();
        let mut aliases = Vec::new();
        for (source_module, item_source, path_component) in materialization_sources {
            let arguments = env
                .namespace_binding_id(item_source)
                .map(|id| env.binding(id).arguments.clone());
            let key = (
                source_module,
                env.module(item_source).items().to_vec(),
                arguments,
            );
            if !path_component && let Some(&index) = seen.get(&key) {
                aliases.push((item_source, index));
                continue;
            }
            let index = unique_sources.len();
            seen.insert(key, index);
            unique_sources.push((source_module, item_source, path_component));
        }
        let materialization_sources = unique_sources;

        struct ReservedGroup {
            source: ModuleId,
            item_source: ModuleId,
            path_component: bool,
            namespace: ModuleId,
            items: Vec<ModuleItem>,
            origins: HashMap<DefId, DefId>,
            arguments: Vec<(ModuleParamId, ModuleArgument)>,
            unchanged: bool,
        }
        let mut groups = Vec::with_capacity(materialization_sources.len());
        let mut lazy_definitions = Vec::new();
        let mut lazy_inductives = Vec::new();
        let mut lazy_datatypes = Vec::new();
        let mut namespaces = Vec::with_capacity(materialization_sources.len());
        // Prove stability before reserving any declaration IDs. Route modules
        // still need their own namespace metadata, but their unchanged items
        // can keep canonical IDs without substitution or conversion searches.
        let unchanged_sources = {
            let mut stability =
                crate::raw::namespaces::NamespaceStability::new(env, &reflected_substitutions);
            materialization_sources
                .iter()
                .map(|(source_module, item_source, _)| {
                    let arguments = env.namespace_binding_id(*item_source).map_or_else(
                        || env.namespace_arguments(*source_module),
                        |binding| env.binding(binding).arguments.clone(),
                    );
                    stability.arguments(&arguments)
                        && env
                            .module(*item_source)
                            .items()
                            .iter()
                            .all(|item| stability.item(item))
                })
                .collect::<Vec<_>>()
        };
        let reusable = materialization_sources
            .iter()
            .zip(&unchanged_sources)
            .map(
                |((source_module, item_source, path_component), unchanged)| {
                    !path_component
                        && (*unchanged
                            || (env.binding(*item_source).arguments.is_empty()
                                && env.namespace_arguments(*source_module).is_empty()))
                },
            )
            .collect::<Vec<_>>();
        let mut allocated = env
            .add_modules_in_scope(
                self.current,
                context.clone(),
                reusable.iter().filter(|reuse| !**reuse).count(),
            )?
            .into_iter();
        for ((_, item_source, _), reuse) in materialization_sources.iter().zip(reusable) {
            // Imports whose complete declaration provenance is unchanged retain
            // their namespace. Path components and changing specializations
            // continue through reservation and ordinary conversion below.
            if reuse {
                remapping.module_ids.insert(*item_source, *item_source);
                env.attach_namespace_binding(self.current, *item_source);
                result_bindings.push(*item_source);
                namespaces.push(*item_source);
                continue;
            }
            let materialized = allocated.next().expect("allocated import namespace");
            env.set_program_context(materialized, program_context.clone());
            remapping.module_ids.insert(*item_source, materialized);
            namespaces.push(materialized);
        }
        for (item_source, index) in aliases {
            remapping.module_ids.insert(item_source, namespaces[index]);
        }
        // All lazy declarations in this instantiation use the same immutable
        // argument environment; retain it once rather than copying every tuple.
        let shared_substitutions: Arc<[_]> = substitutions.clone().into();
        let shared_reflected_substitutions: Arc<[_]> = reflected_substitutions.clone().into();
        for (((source_module, item_source, path_component), materialized), unchanged) in
            materialization_sources
                .into_iter()
                .zip(namespaces)
                .zip(unchanged_sources)
        {
            if materialized == item_source {
                continue;
            }
            // Imported namespaces keep their own parameter telescope. Applying
            // the enclosing substitution must not replace its parameter IDs
            // with the caller's IDs, or subsequent child instantiation and
            // parameter access lose the imported arguments.
            let arguments = env.namespace_binding_id(item_source).map_or_else(
                || env.namespace_arguments(source_module),
                |binding| env.binding(binding).arguments.clone(),
            );
            let mut reserve_definition =
                |env: &mut CrateEnv, remapping: &mut DeclarationRemapping, source_id: DefId| {
                    let id = if unchanged {
                        source_id
                    } else {
                        let id = env.reserve_lazy_definition(
                            materialized,
                            source_id,
                            shared_substitutions.clone(),
                            shared_reflected_substitutions.clone(),
                        );
                        lazy_definitions.push(id);
                        id
                    };
                    remapping.definition_ids.insert(source_id, id);
                    id
                };
            let mut items = Vec::new();
            for item in env.module(item_source).items().to_vec() {
                let item = match item {
                    ModuleItem::Definition { name, definition } => ModuleItem::Definition {
                        name,
                        definition: reserve_definition(env, &mut remapping, definition),
                    },
                    ModuleItem::Inductive {
                        name,
                        constructor_names,
                        associated_definitions,
                        inductive,
                    } => {
                        let id = if unchanged {
                            inductive
                        } else {
                            env.reserve_lazy_inductive(
                                materialized,
                                inductive,
                                shared_reflected_substitutions.clone(),
                            )
                        };
                        remapping.inductive_ids.insert(inductive, id);
                        if !unchanged {
                            lazy_inductives.push(id);
                        }
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, &mut remapping, id)))
                            .collect();
                        ModuleItem::Inductive {
                            name,
                            constructor_names,
                            associated_definitions,
                            inductive: id,
                        }
                    }
                    ModuleItem::Record {
                        name,
                        associated_definitions,
                        inductive,
                    } => {
                        let id = if unchanged {
                            inductive
                        } else {
                            env.reserve_lazy_inductive(
                                materialized,
                                inductive,
                                shared_reflected_substitutions.clone(),
                            )
                        };
                        remapping.inductive_ids.insert(inductive, id);
                        if !unchanged {
                            lazy_inductives.push(id);
                        }
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, &mut remapping, id)))
                            .collect();
                        ModuleItem::Record {
                            name,
                            associated_definitions,
                            inductive: id,
                        }
                    }
                    ModuleItem::ProgramInductive {
                        record_fields,
                        name,
                        constructor_names,
                        associated_definitions,
                        inductive,
                        reflected,
                    } => {
                        let reflected_id = env.reserve_lazy_inductive(
                            materialized,
                            reflected,
                            shared_reflected_substitutions.clone(),
                        );
                        remapping.inductive_ids.insert(reflected, reflected_id);
                        lazy_inductives.push(reflected_id);
                        let id = env.reserve_lazy_program_inductive(
                            materialized,
                            inductive,
                            shared_substitutions.clone(),
                        );
                        remapping.program_inductive_ids.insert(inductive, id);
                        lazy_datatypes.push(id);
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, &mut remapping, id)))
                            .collect();
                        ModuleItem::ProgramInductive {
                            record_fields,
                            name,
                            constructor_names,
                            associated_definitions,
                            inductive: id,
                            reflected: reflected_id,
                        }
                    }
                };
                items.push(item);
            }
            groups.push(ReservedGroup {
                source: source_module,
                item_source,
                path_component,
                namespace: materialized,
                items,
                origins: HashMap::new(),
                arguments,
                unchanged,
            });
        }

        // Every declaration is resolvable before conversion in the reuse cache.
        let shared_remapping = env.store_remapping(remapping.clone());
        for &id in &lazy_definitions {
            env.set_lazy_definition_remapping(id, shared_remapping);
        }
        for &id in &lazy_inductives {
            env.set_lazy_inductive_remapping(id, shared_remapping);
        }
        for &id in &lazy_datatypes {
            env.set_lazy_program_inductive_remapping(id, shared_remapping);
        }

        // A conversion while reusing any item can force another reserved type.
        // Publish every type's source identity before running those conversions.
        for &id in &lazy_inductives {
            env.preview_lazy_inductive(id, &substitutions, &reflected_substitutions, &remapping);
        }

        // Parameter-free namespaces always reuse their original declarations.
        // Finalize them before conversion can materialize a dependent definition:
        // otherwise that definition permanently retains a provisional nominal ID.
        groups.sort_by_key(|group| !env.namespace_arguments(group.source).is_empty());

        // Enclosing declarations precede imports; imports retain their dependency order.
        // Replace reserved IDs with canonical IDs as each specialization is resolved.
        macro_rules! reuse {
            ($id:expr, $method:ident, $table:ident, $unchanged:expr) => {{
                let reserved = *$id;
                let (source, canonical, fresh) = if $unchanged {
                    timing::costs::count("namespace.early-reused-declarations", || 1);
                    (reserved, reserved, false)
                } else {
                    env.$method(
                        reserved,
                        &substitutions,
                        &reflected_substitutions,
                        &remapping,
                    )
                };
                if fresh {
                    cache_misses.set(cache_misses.get() + 1);
                } else {
                    cache_hits.set(cache_hits.get() + 1);
                }
                remapping.$table.insert(source, canonical);
                remapping.$table.insert(reserved, canonical);
                let shared = env.reserved_remapping_mut(shared_remapping);
                shared.$table.insert(source, canonical);
                shared.$table.insert(reserved, canonical);
                *$id = canonical;
                source
            }};
        }
        for group in &mut groups {
            let mut origins = HashMap::new();
            for item in &mut group.items {
                match item {
                    ModuleItem::Definition { definition, .. } => {
                        let source = reuse!(
                            definition,
                            reuse_lazy_definition,
                            definition_ids,
                            group.unchanged
                        );
                        origins.insert(
                            *definition,
                            env.definition_origin(source)
                                .map_or(source, |origin| origin.source),
                        );
                    }
                    ModuleItem::Inductive {
                        inductive,
                        associated_definitions,
                        ..
                    }
                    | ModuleItem::Record {
                        inductive,
                        associated_definitions,
                        ..
                    } => {
                        reuse!(
                            inductive,
                            reuse_lazy_inductive,
                            inductive_ids,
                            group.unchanged
                        );
                        for (_, definition) in associated_definitions {
                            let source = reuse!(
                                definition,
                                reuse_lazy_definition,
                                definition_ids,
                                group.unchanged
                            );
                            origins.insert(
                                *definition,
                                env.definition_origin(source)
                                    .map_or(source, |origin| origin.source),
                            );
                        }
                    }
                    ModuleItem::ProgramInductive {
                        inductive,
                        reflected,
                        associated_definitions,
                        ..
                    } => {
                        reuse!(
                            reflected,
                            reuse_lazy_inductive,
                            inductive_ids,
                            group.unchanged
                        );
                        reuse!(
                            inductive,
                            reuse_lazy_program_inductive,
                            program_inductive_ids,
                            group.unchanged
                        );
                        for (_, definition) in associated_definitions {
                            let source = reuse!(
                                definition,
                                reuse_lazy_definition,
                                definition_ids,
                                group.unchanged
                            );
                            origins.insert(
                                *definition,
                                env.definition_origin(source)
                                    .map_or(source, |origin| origin.source),
                            );
                        }
                    }
                }
            }
            group.origins = origins;
        }
        if let Some(timer) = &mut profile {
            timer.checkpoint("modules phase=materialize");
            eprintln!(
                "modules phase=specialization-cache source={source:?} hits={} misses={}",
                cache_hits.get(),
                cache_misses.get()
            );
        }
        if std::env::var_os("REF_TYPE_PROFILE_NAMESPACES").is_some() {
            eprintln!(
                "namespace {:?}: {} groups, {} definitions, {} inductives, {} datatypes; remapping: {} modules, {} definitions, {} inductives, {} datatypes",
                source,
                groups.len(),
                lazy_definitions.len(),
                lazy_inductives.len(),
                lazy_datatypes.len(),
                remapping.module_ids.len(),
                remapping.definition_ids.len(),
                remapping.inductive_ids.len(),
                remapping.program_inductive_ids.len(),
            );
        }
        let remapping = shared_remapping;

        let mut last_binding = None;
        let mut inherited_bindings = Vec::new();
        for group in groups {
            let arguments = env.substitute_namespace_arguments(
                &group.arguments,
                &substitutions,
                &reflected_substitutions,
                env.remapping(remapping),
            );
            // Unchanged imports need no new namespace metadata. Require exact
            // canonical declaration identities as well as identical, closed
            // arguments: neither conversion alone nor an unchanged telescope
            // is enough to establish that the whole imported graph is shared.
            if !group.path_component
                && env.namespace_arguments_shareable(&arguments)
                && group.items == env.module(group.item_source).items()
                && arguments == env.binding(group.item_source).arguments
            {
                for target in env
                    .reserved_remapping_mut(remapping)
                    .module_ids
                    .values_mut()
                {
                    if *target == group.namespace {
                        *target = group.item_source;
                    }
                }
                env.attach_namespace_binding(self.current, group.item_source);
                result_bindings.push(group.item_source);
                continue;
            }
            env.copy_hir_names(group.item_source, group.namespace);
            for item in group.items {
                env.publish_item(group.namespace, item)?;
            }
            let binding = env.add_namespace_binding(
                self.current,
                group.source,
                group.namespace,
                arguments,
                group.origins,
                remapping,
            );
            if let Some(previous) = env.namespace_binding_id(group.item_source) {
                inherited_bindings.push((binding, env.binding(previous).remapping));
            }
            result_bindings.push(binding);
            if group.path_component {
                last_binding = Some(binding);
            }
        }

        env.inherit_namespace_remappings(remapping, &inherited_bindings);
        env.compact_remapping(remapping);
        let binding = last_binding.expect("non-empty route was checked above");
        if let Some(key) = namespace_key {
            env.closed_namespaces
                .insert(key, (binding, result_bindings));
        }
        Ok(binding)
    }

    pub(crate) fn record_associated_reference(
        &self,
        env: &CrateEnv,
        access: &LocalAccess,
        field: &Identifier,
        span: crate::hir::SourceSpan,
    ) {
        let Some((target, item)) = self.resolve_hir_access(env, access) else {
            return;
        };
        let Some(owner) = crate::analysis::access_name(env, &item) else {
            return;
        };
        let field = field.as_str().trim_end_matches('^');
        let exists = match &item {
            ItemAccessResult::Inductive(item) => {
                item.ctor_names.iter().any(|name| name.as_str() == field)
                    || item
                        .associated_definitions
                        .iter()
                        .any(|(name, _)| name.as_str() == field)
            }
            ItemAccessResult::Record(item) => {
                field == "#"
                    || item
                        .associated_definitions
                        .iter()
                        .any(|(name, _)| name.as_str() == field)
            }
            ItemAccessResult::ProgramInductive(item) => {
                (field == "#" && item.record_fields.is_some())
                    || item.ctor_names.iter().any(|name| name.as_str() == field)
                    || item
                        .associated_definitions
                        .iter()
                        .any(|(name, _)| name.as_str() == field)
            }
            _ => false,
        };
        if exists && let Some(location) = &self.reference_location {
            self.references
                .borrow_mut()
                .push(crate::analysis::Reference {
                    module: crate::analysis::module_path(env, self.current),
                    location: crate::hir::SourceLocation {
                        source: location.source.clone(),
                        span,
                    },
                    target_module: crate::analysis::module_path(env, target),
                    target_name: format!("{}::{field}", owner.trim_end_matches('^')),
                });
        }
    }

    fn record_access(
        &self,
        env: &CrateEnv,
        access: &LocalAccess,
        target: ModuleId,
        item: &ItemAccessResult,
    ) {
        if let Some(location) = &self.reference_location
            && let Some(target_name) = crate::analysis::access_name(env, item)
            && access.span().end > access.span().start
        {
            self.references
                .borrow_mut()
                .push(crate::analysis::Reference {
                    module: crate::analysis::module_path(env, self.current),
                    location: crate::hir::SourceLocation {
                        source: location.source.clone(),
                        span: access.span(),
                    },
                    target_module: crate::analysis::module_path(env, target),
                    target_name: target_name.trim_end_matches('^').to_owned(),
                });
        }
    }

    pub(crate) fn hir_child(
        &self,
        env: &CrateEnv,
        source: ModuleId,
        name: &Identifier,
    ) -> Option<ModuleId> {
        if let Some(id) = name.1 {
            self.hir_module_bindings.get(&id).copied()
        } else {
            env.module(source)
                .children()
                .iter()
                .copied()
                .find(|child| env.module(*child).name() == name.as_str())
        }
    }

    pub(crate) fn hir_module(&self, module: crate::hir::ModuleId) -> Option<ModuleId> {
        self.hir_modules.get(&module).copied()
    }

    pub(crate) fn hir_import(&self, env: &CrateEnv, name: &Identifier) -> Option<ModuleId> {
        if let Some(id) = name.1 {
            self.hir_aliases.get(&id).copied()
        } else {
            env.resolve_import(self.current, name.as_str())
        }
    }

    pub(crate) fn direct_import_member<'a>(
        &self,
        name: &Identifier,
        access: &'a LocalAccess,
    ) -> Option<&'a Identifier> {
        match access {
            LocalAccess::Resolved { module, access, .. }
                if name
                    .1
                    .and_then(|id| self.hir_imports.get(&id))
                    .is_some_and(|import| import.target == *module) =>
            {
                Some(access)
            }
            LocalAccess::Named { access, child, .. } if access == name => Some(child),
            _ => None,
        }
    }

    pub(crate) fn register_hir_import(
        &mut self,
        env: &CrateEnv,
        name: &Identifier,
        binding: ModuleId,
    ) {
        let Some(import) = name.1.and_then(|id| self.hir_imports.get(&id)) else {
            return;
        };
        if let Some(id) = name.1 {
            self.hir_aliases.insert(id, binding);
        }
        let typed = env.binding(binding);
        let sources: Vec<_> = import
            .remapping
            .iter()
            .filter_map(|(source, instance)| {
                self.hir_modules
                    .get(source)
                    .copied()
                    .map(|source| (source, *instance))
            })
            .collect();
        for (source, instance) in sources {
            let target = env
                .remapping(typed.remapping)
                .module_ids
                .get(&source)
                .copied()
                .unwrap_or(source);
            self.hir_modules.insert(instance, target);
        }
        self.hir_modules.insert(import.target, typed.materialized);
    }

    fn resolve_hir_access(
        &self,
        env: &CrateEnv,
        access: &LocalAccess,
    ) -> Option<(ModuleId, ItemAccessResult)> {
        if let LocalAccess::Resolved {
            module,
            access: name,
            ..
        } = access
        {
            let module = *self.hir_modules.get(module)?;
            let id = name.1?;
            let binding = self.hir_bindings.get(&id)?;
            let item = if let Some(position) = binding.parameter {
                let source = *self.hir_modules.get(&binding.module)?;
                let parameter = ModuleParamId {
                    module: source,
                    position: position as u32,
                };
                if env.namespace_binding_id(module).is_some() {
                    let argument = env
                        .binding(module)
                        .arguments
                        .iter()
                        .find(|(id, _)| *id == parameter)?
                        .1;
                    match argument {
                        ModuleArgument::Pts(exp) => ItemAccessResult::Expression(exp),
                        argument => ItemAccessResult::Argument(argument),
                    }
                } else {
                    parameter_access(env, parameter, env.module_parameter_opt(parameter)?.kind)
                }
            } else {
                convert_item(env.module(module).hir_item(id)?)
            };
            Some((module, reflect_access(env, item, name.as_str())?))
        } else if let LocalAccess::Current { access: name, span } = access
            && name.1.is_some()
        {
            let binding = self.hir_bindings.get(&name.1?)?;
            self.resolve_hir_access(
                env,
                &LocalAccess::Resolved {
                    module: binding.module,
                    access: name.clone(),
                    span: *span,
                    display: name.0.clone(),
                },
            )
        } else {
            resolve_access(env, self.current, access)
        }
    }

    pub(crate) fn get_item(
        &self,
        env: &CrateEnv,
        access: &LocalAccess,
    ) -> Option<ItemAccessResult> {
        let _cost = timing::costs::Scope::enter("names.get-item");
        let (target, item) = self.resolve_hir_access(env, access)?;
        // Template references are recorded at their definition, before expansion.
        if !matches!(access, LocalAccess::Resolved { .. }) {
            self.record_access(env, access, target, &item);
        }
        Some(item)
    }
}

pub(crate) fn resolve_access(
    env: &CrateEnv,
    from: ModuleId,
    access: &LocalAccess,
) -> Option<(ModuleId, ItemAccessResult)> {
    let _cost = timing::costs::Scope::enter("names.resolve-access");
    let (mut module, reference, inherit) = match access {
        LocalAccess::Current { access, .. } => (from, access.as_str(), true),
        LocalAccess::Named { access, child, .. } => {
            let binding = env.resolve_import(from, access.as_str())?;
            (env.binding(binding).materialized, child.as_str(), false)
        }
        LocalAccess::Resolved { .. } | LocalAccess::Instantiated { .. } => return None,
    };
    let (name, _reflected) = reference
        .strip_suffix('^')
        .map_or((reference, false), |name| (name, true));
    let item = loop {
        if let Some(item) = lookup_name(env, module, name) {
            break item;
        }
        if !inherit {
            return None;
        }
        module = env.module(module).parent()?;
    };
    Some((module, reflect_access(env, item, reference)?))
}

fn reflect_access(
    env: &CrateEnv,
    item: ItemAccessResult,
    reference: &str,
) -> Option<ItemAccessResult> {
    let item = if reference.ends_with('^') {
        match item {
            ItemAccessResult::ProgramInductive(item) => {
                ItemAccessResult::Inductive(ModItemInductive {
                    type_name: Identifier(reference.to_owned()),
                    ctor_names: item.ctor_names,
                    inductive: item.reflected,
                    associated_definitions: Vec::new(),
                })
            }
            ItemAccessResult::Definition(item) => ItemAccessResult::ReflectedDefinition(item),
            ItemAccessResult::Argument(argument) => ItemAccessResult::Expression(match argument {
                ModuleArgument::ProgramType(ty) => {
                    crate::raw::reflection::reflect_value_type(env, ty).ok()?
                }
                ModuleArgument::ProgramValue(value) => {
                    crate::raw::reflection::reflect_value(env, value).ok()?
                }
                ModuleArgument::Pts(exp) => exp,
            }),
            ItemAccessResult::ProgramTypeParameter(parameter)
            | ItemAccessResult::ProgramValueParameter(parameter) => ItemAccessResult::Expression(
                env.arena()
                    .alloc(crate::raw::exp::ExpNode::ReflectedProgramParam(parameter)),
            ),
            _ => return None,
        }
    } else {
        item
    };
    Some(item)
}

fn lookup_name(env: &CrateEnv, module: ModuleId, name: &str) -> Option<ItemAccessResult> {
    let current = env.module(module);
    let item = if let Some(item) = current.item(name) {
        convert_item(item)
    } else {
        if env.namespace_binding_id(module).is_some() {
            let binding = env.binding(module);
            if let Some((_, argument)) = binding.arguments.iter().find(|(id, _)| {
                env.module_parameter_opt(*id)
                    .is_some_and(|parameter| env.symbol(parameter.name) == name)
            }) {
                return Some(match *argument {
                    ModuleArgument::Pts(exp) => ItemAccessResult::Expression(exp),
                    argument => ItemAccessResult::Argument(argument),
                });
            }
        }
        let (position, parameter) = current
            .parameters()
            .iter()
            .enumerate()
            .find(|(_, parameter)| env.symbol(parameter.name) == name)?;
        parameter_access(
            env,
            ModuleParamId {
                module,
                position: position as u32,
            },
            parameter.kind,
        )
    };
    Some(item)
}

fn parameter_access(
    env: &CrateEnv,
    id: ModuleParamId,
    kind: ModuleParameterKind,
) -> ItemAccessResult {
    match kind {
        ModuleParameterKind::Pts { .. } => {
            ItemAccessResult::Expression(env.arena().exp_module_param(id))
        }
        ModuleParameterKind::ProgramType => ItemAccessResult::ProgramTypeParameter(id),
        ModuleParameterKind::ProgramValue { .. } => ItemAccessResult::ProgramValueParameter(id),
    }
}

fn convert_item(item: &ModuleItem) -> ItemAccessResult {
    match item {
        ModuleItem::Definition { name, definition } => {
            ItemAccessResult::Definition(ModItemDefinition {
                def_name: Identifier(name.clone()),
                definition: *definition,
            })
        }
        ModuleItem::Inductive {
            name,
            constructor_names,
            associated_definitions,
            inductive,
        } => ItemAccessResult::Inductive(ModItemInductive {
            type_name: Identifier(name.clone()),
            ctor_names: constructor_names
                .iter()
                .map(|name| Identifier(name.clone()))
                .collect(),
            inductive: *inductive,
            associated_definitions: associated_definitions
                .iter()
                .map(|(name, definition)| (Identifier(name.clone()), *definition))
                .collect(),
        }),
        ModuleItem::Record {
            name,
            associated_definitions,
            inductive,
        } => ItemAccessResult::Record(ModItemRecord {
            type_name: Identifier(name.clone()),
            inductive: *inductive,
            associated_definitions: associated_definitions
                .iter()
                .map(|(name, definition)| (Identifier(name.clone()), *definition))
                .collect(),
        }),
        ModuleItem::ProgramInductive {
            record_fields,
            name,
            constructor_names,
            associated_definitions,
            inductive,
            reflected,
        } => ItemAccessResult::ProgramInductive(ModItemProgramInductive {
            record_fields: record_fields
                .as_ref()
                .map(|fields| fields.iter().cloned().map(Identifier).collect()),
            type_name: Identifier(name.clone()),
            ctor_names: constructor_names
                .iter()
                .map(|name| Identifier(name.clone()))
                .collect(),
            inductive: *inductive,
            reflected: *reflected,
            associated_definitions: associated_definitions
                .iter()
                .map(|(name, definition)| (Identifier(name.clone()), *definition))
                .collect(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::raw::{
        exp::ExpNode,
        inductive::{CtorType, InductiveTypeSpecs},
        sort::Sort,
    };

    fn pts_body(definition: &DefinedConstant) -> Exp {
        match definition {
            DefinedConstant::Pts { body, .. } => *body,
            _ => panic!("expected a Set/Prop definition"),
        }
    }

    fn parameter(env: &mut CrateEnv, name: &str, ty: Exp) -> ModuleParameter {
        ModuleParameter {
            name: env.intern(name),
            kind: ModuleParameterKind::Pts { ty },
        }
    }

    #[test]
    fn module_navigation_uses_persistent_module_envs() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        manager
            .add_child_and_moveto(&mut env, "Test1".into(), vec![])
            .unwrap();
        manager
            .add_child_and_moveto(&mut env, "Child1".into(), vec![])
            .unwrap();
        assert_eq!(env.module(manager.current()).name(), "Child1");
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        assert_eq!(env.module(manager.current()).name(), "Test1");
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        assert_eq!(manager.current(), env.root_module());
    }

    #[test]
    fn unparameterized_aliases_reuse_source_declarations() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        manager
            .add_child_and_moveto(&mut env, "Source".into(), vec![])
            .unwrap();
        let proposition = env.arena().sort(Sort::Prop);
        let proposition_kind = env.arena().sort(Sort::PropKind);
        for name in ["used", "unused"] {
            manager
                .add_def(
                    &mut env,
                    Identifier(name.into()),
                    DefinedConstant::Pts {
                        ty: proposition_kind,
                        body: proposition,
                    },
                )
                .unwrap();
        }
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let binding = manager
            .bind_namespace(
                &mut env,
                &mut Vec::new(),
                None,
                vec![(Identifier("Source".into()), vec![])],
            )
            .unwrap();
        let namespace = env.binding(binding).materialized;
        let id = |name| match env.module(namespace).item(name).unwrap() {
            ModuleItem::Definition { definition, .. } => *definition,
            _ => unreachable!(),
        };
        let used = id("used");
        let unused = id("unused");
        assert!(env.is_definition_materialized(used));
        assert!(env.is_definition_materialized(unused));
        assert_eq!(env.materialization_stats().definitions, 0);

        let _ = env.resolve_definition(used).unwrap();
        assert!(env.is_definition_materialized(used));
        assert!(env.is_definition_materialized(unused));
        assert_eq!(env.materialization_stats().definitions, 0);
        let _ = env.resolve_definition(used).unwrap();
        assert_eq!(env.materialization_stats().definitions, 0);
        // Sharing was decided before reservation, so the alias has no unused
        // definition slots left over from provisional specializations.
        let added = env
            .add_definition(
                namespace,
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: proposition,
                },
            )
            .unwrap();
        assert_eq!(added.index, 0);
    }

    #[test]
    fn repeated_bindings_share_definition_ids_and_internal_references() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        manager
            .add_child_and_moveto(&mut env, "Source".into(), vec![])
            .unwrap();

        let proposition = env.arena().sort(Sort::Prop);
        let proposition_kind = env.arena().sort(Sort::PropKind);
        manager
            .add_def(
                &mut env,
                Identifier("base".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: proposition,
                },
            )
            .unwrap();
        let ModuleItem::Definition {
            definition: base, ..
        } = env.module(manager.current()).items()[0]
        else {
            unreachable!()
        };
        let base_exp = env.arena().alloc(ExpNode::DefinedConstant(base));
        manager
            .add_def(
                &mut env,
                Identifier("alias".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: base_exp,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let instantiate = |manager: &mut ModuleManager, env: &mut CrateEnv| {
            manager
                .bind_namespace(
                    env,
                    &mut Vec::new(),
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&mut manager, &mut env);
        let second = instantiate(&mut manager, &mut env);
        assert_eq!(first, second);

        let ids = |env: &CrateEnv, binding| {
            env.module(env.binding(binding).materialized)
                .items()
                .iter()
                .map(|item| match item {
                    ModuleItem::Definition { definition, .. } => *definition,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>()
        };
        let first_ids = ids(&env, first);
        let second_ids = ids(&env, second);
        assert_eq!(first_ids, second_ids);
        assert_eq!(first_ids[0], base);
        assert_eq!(env.definition_origin(first_ids[0]), None);
        assert_eq!(env.definition_origin(base), None);
        assert!(matches!(
            env.arena().get(pts_body(env.definition(first_ids[1]))),
            ExpNode::DefinedConstant(id) if id == first_ids[0]
        ));
        assert!(matches!(
            env.arena().get(pts_body(env.definition(second_ids[1]))),
            ExpNode::DefinedConstant(id) if id == second_ids[0]
        ));
    }

    #[test]
    fn closed_namespace_reuse_attaches_dependencies_and_tracks_source_growth() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let proposition = env.arena().sort(Sort::Prop);
        let proposition_kind = env.arena().sort(Sort::PropKind);
        manager
            .add_child_and_moveto(&mut env, "Source".into(), vec![])
            .unwrap();
        let source = manager.current();
        manager
            .add_def(
                &mut env,
                Identifier("early".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: proposition,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        let instantiate = |manager: &mut ModuleManager, env: &mut CrateEnv| {
            manager
                .bind_namespace(
                    env,
                    &mut vec![],
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&mut manager, &mut env);
        manager
            .add_child_and_moveto(&mut env, "OtherOwner".into(), vec![])
            .unwrap();
        let reused = instantiate(&mut manager, &mut env);
        assert_eq!(first, reused);
        assert!(env.module(manager.current()).bindings().contains(&reused));
        assert!(env.module(reused).item("early").is_some());

        let local_name = env.intern("unused_local");
        let local_context = &mut vec![ExpContextEntry {
            var: local_name,
            ty: proposition,
        }];
        let in_local_context = manager
            .bind_namespace(
                &mut env,
                local_context,
                Some(1),
                vec![(Identifier("Source".into()), vec![])],
            )
            .unwrap();
        assert_eq!(in_local_context, first);

        manager.moveto(source);
        manager
            .add_def(
                &mut env,
                Identifier("late".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: proposition,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        let grown = instantiate(&mut manager, &mut env);
        assert_ne!(first, grown);
        assert!(env.module(grown).item("late").is_some());
        assert!(env.module(first).item("late").is_none());
    }

    #[test]
    fn module_instantiation_requires_all_well_typed_named_arguments() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));
        let parameter = parameter(&mut env, "A", set);
        manager
            .add_child_and_moveto(&mut env, "Parameterized".into(), vec![parameter])
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let call = |name: &str, arguments| vec![(Identifier(name.into()), arguments)];
        assert!(
            manager
                .bind_namespace(
                    &mut env,
                    &mut Vec::new(),
                    None,
                    call("Parameterized", vec![]),
                )
                .is_err()
        );
        let wrong_argument = env.arena().sort(Sort::Prop);
        assert!(
            manager
                .bind_namespace(
                    &mut env,
                    &mut Vec::new(),
                    None,
                    call(
                        "Parameterized",
                        vec![(Identifier("wrong".into()), wrong_argument.into())],
                    ),
                )
                .is_err()
        );
        assert!(env.module(env.root_module()).bindings().is_empty());

        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let mut context = vec![ExpContextEntry {
            var: carrier,
            ty: set,
        }];
        assert!(
            manager
                .bind_namespace(
                    &mut env,
                    &mut context,
                    None,
                    call(
                        "Parameterized",
                        vec![(Identifier("A".into()), argument.into())],
                    ),
                )
                .is_ok()
        );
    }

    #[test]
    fn inductives_from_two_bindings_are_the_same_type() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        manager
            .add_child_and_moveto(&mut env, "Source".into(), vec![])
            .unwrap();
        let _source = manager.current();
        let spec = InductiveTypeSpecs::unchecked(
            vec![],
            vec![],
            Sort::Set(0),
            vec![CtorType {
                telescope: vec![],
                indices: vec![],
            }],
        );
        manager
            .add_inductive(
                &mut env,
                Identifier("Token".into()),
                vec![Identifier("token".into())],
                spec,
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let instantiate = |manager: &mut ModuleManager, env: &mut CrateEnv| {
            manager
                .bind_namespace(
                    env,
                    &mut Vec::new(),
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&mut manager, &mut env);
        let second = instantiate(&mut manager, &mut env);
        let inductive = |env: &CrateEnv, binding| {
            let module = env.module(env.binding(binding).materialized);
            let ModuleItem::Inductive { inductive, .. } = module.item("Token").unwrap() else {
                unreachable!()
            };
            *inductive
        };
        let first = inductive(&env, first);
        let second = inductive(&env, second);
        assert_eq!(first, second);
        assert!(env.is_inductive_materialized(first));
        assert!(env.is_inductive_materialized(second));

        let first_constructor = env.arena().alloc(ExpNode::IndCtor {
            indspec: first,
            parameters: vec![],
            idx: 0,
        });
        let first_type = env.arena().alloc(ExpNode::IndType {
            indspec: first,
            parameters: vec![],
        });
        let second_type = env.arena().alloc(ExpNode::IndType {
            indspec: second,
            parameters: vec![],
        });
        assert!(
            CheckSession::new(&env, &mut Vec::new())
                .check_pts(first_constructor, first_type)
                .is_ok()
        );
        assert!(env.is_inductive_materialized(first));
        assert!(env.is_inductive_materialized(second));
        assert!(
            CheckSession::new(&env, &mut Vec::new())
                .check_pts(first_constructor, second_type)
                .is_ok()
        );
    }

    #[test]
    fn nested_namespace_materializes_parent_dependencies() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));
        let parameter = env.intern("A");
        manager
            .add_child_and_moveto(
                &mut env,
                "Parent".into(),
                vec![ModuleParameter {
                    name: parameter,
                    kind: ModuleParameterKind::Pts { ty: set },
                }],
            )
            .unwrap();
        let parameter_exp = env.arena().exp_module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager
            .add_def(
                &mut env,
                Identifier("parent_value".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: parameter_exp,
                },
            )
            .unwrap();
        let ModuleItem::Definition {
            definition: parent_definition,
            ..
        } = env.module(manager.current()).item("parent_value").unwrap()
        else {
            unreachable!()
        };
        let parent_definition = *parent_definition;

        manager
            .add_child_and_moveto(&mut env, "Child".into(), vec![])
            .unwrap();
        let parent_reference = env
            .arena()
            .alloc(ExpNode::DefinedConstant(parent_definition));
        manager
            .add_def(
                &mut env,
                Identifier("child_value".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: parent_reference,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_root();

        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let mut context = vec![ExpContextEntry {
            var: carrier,
            ty: set,
        }];
        let binding = manager
            .bind_namespace(
                &mut env,
                &mut context,
                None,
                vec![
                    (
                        Identifier("Parent".into()),
                        vec![(Identifier("A".into()), argument.into())],
                    ),
                    (Identifier("Child".into()), vec![]),
                ],
            )
            .unwrap();
        let final_module = env.module(env.binding(binding).materialized);
        let ModuleItem::Definition {
            definition: child_definition,
            ..
        } = final_module.item("child_value").unwrap()
        else {
            unreachable!()
        };
        let child = env
            .arena()
            .alloc(ExpNode::DefinedConstant(*child_definition));
        assert!(crate::kernel_bridge::exp_is_alpha_eq(
            &env,
            crate::kernel_bridge::whnf(&env, child),
            argument,
        ));
    }

    #[test]
    fn outer_substitution_specializes_parameterized_imports() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));

        let parameter = env.intern("A");
        manager
            .add_child_and_moveto(
                &mut env,
                "Param".into(),
                vec![ModuleParameter {
                    name: parameter,
                    kind: ModuleParameterKind::Pts { ty: set },
                }],
            )
            .unwrap();
        let parameter_exp = env.arena().exp_module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager
            .add_def(
                &mut env,
                Identifier("value".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: parameter_exp,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let outer_parameter = env.intern("A");
        manager
            .add_child_and_moveto(
                &mut env,
                "Outer".into(),
                vec![ModuleParameter {
                    name: outer_parameter,
                    kind: ModuleParameterKind::Pts { ty: set },
                }],
            )
            .unwrap();
        let outer_context_var = outer_parameter;
        let outer_argument = env.arena().exp_module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        let dependency = manager
            .bind_namespace(
                &mut env,
                &mut vec![ExpContextEntry {
                    var: outer_context_var,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Param".into()),
                    vec![(Identifier("A".into()), outer_argument.into())],
                )],
            )
            .unwrap();
        manager
            .add_import(&mut env, Identifier("P".into()), dependency)
            .unwrap();
        let ItemAccessResult::Definition(imported_value) = manager
            .get_item(
                &env,
                &LocalAccess::Named {
                    span: Default::default(),
                    access: Identifier("P".into()),
                    child: Identifier("value".into()),
                },
            )
            .unwrap()
        else {
            unreachable!()
        };
        let imported_value = env
            .arena()
            .alloc(ExpNode::DefinedConstant(imported_value.definition));
        manager
            .add_def(
                &mut env,
                Identifier("result".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: imported_value,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let binding = manager
            .bind_namespace(
                &mut env,
                &mut vec![ExpContextEntry {
                    var: carrier,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Outer".into()),
                    vec![(Identifier("A".into()), argument.into())],
                )],
            )
            .unwrap();
        let ExpNode::ModuleParam(outer_id) = env.arena().get(outer_argument) else {
            unreachable!()
        };
        let ExpNode::ModuleParam(source_id) = env.arena().get(parameter_exp) else {
            unreachable!()
        };
        let replacements = [(outer_id, argument)];
        let mut stability = crate::raw::namespaces::NamespaceStability::new(&env, &replacements);
        assert!(!stability.arguments(&[(source_id, ModuleArgument::Pts(imported_value))]));
        let specialized_dependency = *env
            .remapping(env.binding(binding).remapping)
            .module_ids
            .get(&dependency)
            .unwrap();
        let ExpNode::ModuleParam(source_parameter) = env.arena().get(parameter_exp) else {
            unreachable!()
        };
        assert_eq!(
            env.binding(specialized_dependency).arguments,
            vec![(source_parameter, ModuleArgument::Pts(argument))],
        );
        let module = env.module(env.binding(binding).materialized);
        let ModuleItem::Definition { definition, .. } = module.item("result").unwrap() else {
            unreachable!()
        };
        let result = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        assert!(crate::kernel_bridge::exp_is_alpha_eq(
            &env,
            crate::kernel_bridge::whnf(&env, result),
            argument,
        ));
    }
    #[test]
    fn closed_import_metadata_is_shared_under_an_outer_substitution() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));
        let proposition = env.arena().sort(Sort::Prop);
        let proposition_kind = env.arena().sort(Sort::PropKind);
        manager
            .add_child_and_moveto(&mut env, "Types".into(), vec![])
            .unwrap();
        manager
            .add_inductive(
                &mut env,
                Identifier("Token".into()),
                vec![],
                InductiveTypeSpecs::unchecked(vec![], vec![], Sort::Set(0), vec![]),
            )
            .unwrap();
        let ModuleItem::Inductive { inductive, .. } =
            env.module(manager.current()).item("Token").unwrap()
        else {
            unreachable!()
        };
        let token = env.arena().alloc(ExpNode::IndType {
            indspec: *inductive,
            parameters: vec![],
        });
        manager
            .add_def(
                &mut env,
                Identifier("Alias".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: token,
                },
            )
            .unwrap();
        let ModuleItem::Definition {
            definition: alias_id,
            ..
        } = env.module(manager.current()).item("Alias").unwrap()
        else {
            unreachable!()
        };
        let token_alias = env.arena().alloc(ExpNode::DefinedConstant(*alias_id));
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        let closed_parameter = parameter(&mut env, "Universe", set);
        manager
            .add_child_and_moveto(&mut env, "Closed".into(), vec![closed_parameter])
            .unwrap();
        manager
            .add_def(
                &mut env,
                Identifier("value".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: proposition,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let parameter = env.intern("A");
        manager
            .add_child_and_moveto(
                &mut env,
                "Outer".into(),
                vec![ModuleParameter {
                    name: parameter,
                    kind: ModuleParameterKind::Pts { ty: set },
                }],
            )
            .unwrap();
        let closed = manager
            .bind_namespace(
                &mut env,
                &mut vec![],
                None,
                vec![(
                    Identifier("Closed".into()),
                    vec![(Identifier("Universe".into()), token.into())],
                )],
            )
            .unwrap();
        let same_closed = manager
            .bind_namespace(
                &mut env,
                &mut vec![],
                None,
                vec![(
                    Identifier("Closed".into()),
                    vec![(Identifier("Universe".into()), token_alias.into())],
                )],
            )
            .unwrap();
        assert_eq!(closed, same_closed);
        manager
            .add_import(&mut env, Identifier("P".into()), closed)
            .unwrap();
        let ModuleItem::Definition { definition, .. } = env.module(closed).item("value").unwrap()
        else {
            unreachable!()
        };
        let value = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        manager
            .add_def(
                &mut env,
                Identifier("result".into()),
                DefinedConstant::Pts {
                    ty: proposition_kind,
                    body: value,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let binding = manager
            .bind_namespace(
                &mut env,
                &mut vec![ExpContextEntry {
                    var: carrier,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Outer".into()),
                    vec![(Identifier("A".into()), argument.into())],
                )],
            )
            .unwrap();
        assert_eq!(
            *env.remapping(env.binding(binding).remapping)
                .module_ids
                .get(&closed)
                .unwrap(),
            closed
        );
        let ModuleItem::Definition { definition, .. } = env.module(binding).item("result").unwrap()
        else {
            unreachable!()
        };
        let result = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        assert!(crate::kernel_bridge::exp_is_alpha_eq(
            &env,
            crate::kernel_bridge::whnf(&env, result),
            proposition
        ));
    }
    #[test]
    fn unchanged_parameterized_import_keeps_its_namespace_identity() {
        let mut manager = ModuleManager::new();
        let mut env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));
        let parameter = env.intern("A");
        let parameters = || {
            vec![ModuleParameter {
                name: parameter,
                kind: ModuleParameterKind::Pts { ty: set },
            }]
        };
        manager
            .add_child_and_moveto(&mut env, "External".into(), parameters())
            .unwrap();
        let external = env.arena().exp_module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        manager
            .add_child_and_moveto(&mut env, "Param".into(), parameters())
            .unwrap();
        let value = env.arena().exp_module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager
            .add_def(
                &mut env,
                Identifier("value".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: value,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        manager
            .add_child_and_moveto(&mut env, "Outer".into(), parameters())
            .unwrap();
        let dependency = manager
            .bind_namespace(
                &mut env,
                &mut vec![],
                None,
                vec![(
                    Identifier("Param".into()),
                    vec![(Identifier("A".into()), external.into())],
                )],
            )
            .unwrap();
        manager
            .add_import(&mut env, Identifier("P".into()), dependency)
            .unwrap();
        let ModuleItem::Definition { definition, .. } =
            env.module(dependency).item("value").unwrap()
        else {
            unreachable!()
        };
        let value = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        manager
            .add_def(
                &mut env,
                Identifier("result".into()),
                DefinedConstant::Pts {
                    ty: set,
                    body: value,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);
        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let binding = manager
            .bind_namespace(
                &mut env,
                &mut vec![ExpContextEntry {
                    var: carrier,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Outer".into()),
                    vec![(Identifier("A".into()), argument.into())],
                )],
            )
            .unwrap();
        assert_eq!(
            *env.remapping(env.binding(binding).remapping)
                .module_ids
                .get(&dependency)
                .unwrap(),
            dependency
        );
        let ModuleItem::Definition { definition, .. } = env.module(binding).item("result").unwrap()
        else {
            unreachable!()
        };
        let result = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        assert!(crate::kernel_bridge::exp_is_alpha_eq(
            &env,
            crate::kernel_bridge::whnf(&env, result),
            external
        ));
    }
}
