use crate::hir::{Identifier, LocalAccess};
use crate::items::{ModItemDefinition, ModItemInductive, ModItemProgramInductive, ModItemRecord};
use crate::raw::calculus::{exp_subst_map, remap_all_global_ids};
use crate::raw::derivation::CheckSession;
#[cfg(test)]
use crate::raw::environment::ModuleParameter;
use crate::raw::environment::{
    CrateEnv, DeclarationRemapping, DefinedConstant, ModuleArgument, ModuleItem,
    ModuleParameterKind,
};
use crate::raw::exp::{Exp, ExpContext, ExpContextEntry};
use crate::raw::ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId};
#[cfg(test)]
use crate::raw::inductive::InductiveTypeSpecs;
use crate::raw::program::{ProgramContext, ProgramContextEntry};
use std::{cell::RefCell, collections::HashMap};

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

#[derive(Debug)]
pub(crate) struct ModuleManager {
    current: ModuleId,
    pub(crate) reference_location: Option<crate::hir::SourceLocation>,
    pub(crate) references: RefCell<Vec<crate::analysis::Reference>>,
    pub(crate) hir_module_bindings: HashMap<resolve::hir::BindingId, ModuleId>,
    pub(crate) hir_aliases: HashMap<resolve::hir::BindingId, ModuleId>,
    pub(crate) hir_bindings: HashMap<resolve::hir::BindingId, resolve::Binding>,
    pub(crate) hir_modules: HashMap<resolve::hir::ModuleId, ModuleId>,
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
    ) -> Result<(), String> {
        self.current = env.add_child_module(self.current, module_name, parameters)?;
        Ok(())
    }

    pub(crate) fn reserve_child_and_moveto(
        &mut self,
        env: &mut CrateEnv,
        module_name: String,
    ) -> ModuleId {
        let id = env.reserve_child_module(self.current, module_name);
        self.current = id;
        id
    }

    pub(crate) fn moveto_parent(&mut self, env: &CrateEnv) {
        if let Some(parent) = env.module(self.current).parent() {
            self.current = parent;
        }
    }

    pub(crate) fn publish_current_module(&self, env: &mut CrateEnv) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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
    ) -> Result<(), String> {
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

    fn resolve_start(
        &self,
        env: &CrateEnv,
        back_parent: Option<usize>,
    ) -> Result<ModuleId, String> {
        let Some(back_parent) = back_parent else {
            return Ok(env.root_module());
        };
        let mut module = self.current;
        for _ in 0..back_parent {
            module = env
                .module(module)
                .parent()
                .ok_or_else(|| "Cannot go back parent: already at root module".to_string())?;
        }
        Ok(module)
    }

    pub(crate) fn bind_namespace(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, String> {
        let source = self.resolve_start(env, back_parent)?;
        self.bind_namespace_from(env, context, source, None, calls)
    }

    pub(crate) fn bind_namespace_from_alias(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        base: ModuleId,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, String> {
        let source = env.binding(base).source;
        self.bind_namespace_from(env, context, source, Some(base), calls)
    }

    fn bind_namespace_from(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        mut source: ModuleId,
        base: Option<ModuleId>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleId, String> {
        let (mut substitutions, mut remapping) = base.map_or_else(
            || (Vec::new(), DeclarationRemapping::default()),
            |base| {
                let base = env.binding(base);
                (base.arguments.clone(), base.remapping.clone())
            },
        );
        let mut reflected_substitutions = substitutions
            .iter()
            .map(|(parameter, argument)| {
                let reflected = match argument {
                    ModuleArgument::Pts(exp) => *exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(env, *ty).map_err(|error| {
                            format!("cannot reflect Program type module argument: {error}")
                        })?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        env,
                        crate::raw::program::ProgramTerm::ValueTerm(*value),
                    )
                    .map_err(|error| {
                        format!("cannot reflect Program value module argument: {error}")
                    })?,
                };
                Ok((*parameter, reflected))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let mut route = Vec::new();

        for (child_name, arguments) in calls {
            let child = self.hir_child(env, source, &child_name).ok_or_else(|| {
                format!(
                    "Child module '{}' not found in module '{}'",
                    child_name.as_str(),
                    env.module(source).name(),
                )
            })?;
            let parameters = env.module(child).parameters().to_vec();
            if arguments.len() != parameters.len() {
                return Err(format!(
                    "Argument length mismatch for module '{}': expected {}, got {}",
                    child_name.as_str(),
                    parameters.len(),
                    arguments.len(),
                ));
            }
            for ((position, (argument_name, argument)), parameter) in
                arguments.iter().enumerate().zip(parameters)
            {
                if argument_name.as_str() != env.symbol(parameter.name) {
                    return Err(format!(
                        "Argument name mismatch for module '{}': expected '{}', got '{}'",
                        child_name.as_str(),
                        env.symbol(parameter.name),
                        argument_name.as_str(),
                    ));
                }
                match (parameter.kind, argument) {
                    (ModuleParameterKind::Pts { ty }, ModuleArgument::Pts(argument)) => {
                        let expected = remap_all_global_ids(
                            env.arena(),
                            ty,
                            &remapping.definition_ids,
                            &remapping.inductive_ids,
                            &remapping.program_inductive_ids,
                        );
                        let expected =
                            exp_subst_map(env.arena(), expected, &reflected_substitutions);
                        CheckSession::new(env, context)
                            .check_pts(*argument, expected)
                            .map_err(|error| {
                                format!(
                                    "Module '{}' argument '{}' failed type checking: {error:?}",
                                    child_name.as_str(),
                                    argument_name.as_str(),
                                )
                            })?;
                    }
                    (ModuleParameterKind::ProgramType, ModuleArgument::ProgramType(ty)) => {
                        crate::raw::program_derivation::ProgramCheckSession::new(
                            env,
                            &mut Vec::new(),
                        )
                        .check_value_type(*ty)
                        .map_err(|error| {
                            format!("Program type module argument is ill-formed: {error:?}")
                        })?;
                    }
                    (
                        ModuleParameterKind::ProgramValue { ty },
                        ModuleArgument::ProgramValue(value),
                    ) => {
                        let expected = crate::raw::program_calculus::remap_value_type_global_ids(
                            env.arena(),
                            ty,
                            &remapping.definition_ids,
                            &remapping.program_inductive_ids,
                        );
                        let expected = crate::raw::program_calculus::subst_value_type_module_params(
                            env.arena(),
                            expected,
                            &substitutions,
                        );
                        crate::raw::program_derivation::ProgramCheckSession::new(
                            env,
                            &mut Vec::new(),
                        )
                        .check_value_term(*value, expected)
                        .map_err(|error| {
                            format!("Program value module argument is ill-typed: {error:?}")
                        })?;
                    }
                    _ => {
                        return Err(format!(
                            "Module '{}' argument '{}' uses the wrong syntactic category",
                            child_name.as_str(),
                            argument_name.as_str(),
                        ));
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
                            format!("cannot reflect Program type module argument: {error}")
                        })?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        env,
                        crate::raw::program::ProgramTerm::ValueTerm(*value),
                    )
                    .map_err(|error| {
                        format!("cannot reflect Program value module argument: {error}")
                    })?,
                };
                substitutions.push((parameter_id, *argument));
                reflected_substitutions.push((parameter_id, reflected));
            }
            source = child;
            route.push(child);
        }

        if route.is_empty() {
            return Err("Module instantiation path must contain at least one module".into());
        }

        // Reserve stable IDs and publish only metadata. Declaration bodies are
        // transformed by CrateEnv when one of these IDs is first requested.
        let mut materialization_sources = Vec::new();
        for source_module in route {
            materialization_sources.extend(env.module(source_module).bindings().iter().map(|id| {
                let binding = env.binding(*id);
                (binding.source, binding.materialized, false)
            }));
            materialization_sources.push((source_module, source_module, true));
        }

        struct ReservedGroup {
            source: ModuleId,
            path_component: bool,
            namespace: ModuleId,
            items: Vec<ModuleItem>,
            origins: HashMap<DefId, DefId>,
        }
        let mut groups = Vec::with_capacity(materialization_sources.len());
        let mut lazy_definitions = Vec::new();
        let mut lazy_inductives = Vec::new();
        let mut lazy_datatypes = Vec::new();
        for (source_module, item_source, path_component) in materialization_sources {
            let materialized = env.add_module_in_scope(self.current, context.clone())?;
            remapping.module_ids.insert(item_source, materialized);
            env.copy_hir_names(item_source, materialized);
            let mut origins = HashMap::new();
            let mut reserve_definition =
                |env: &mut CrateEnv, remapping: &mut DeclarationRemapping, source_id: DefId| {
                    let (id, fresh) = env.reserve_lazy_definition(
                        materialized,
                        source_id,
                        substitutions.clone(),
                        reflected_substitutions.clone(),
                        remapping,
                    );
                    remapping.definition_ids.insert(source_id, id);
                    origins.insert(
                        id,
                        env.definition_origin(source_id)
                            .map_or(source_id, |origin| origin.source),
                    );
                    if fresh {
                        lazy_definitions.push(id);
                    }
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
                        let (id, fresh) = env.reserve_lazy_inductive(
                            materialized,
                            inductive,
                            substitutions.clone(),
                            reflected_substitutions.clone(),
                            &remapping,
                        );
                        remapping.inductive_ids.insert(inductive, id);
                        if fresh {
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
                        let (id, fresh) = env.reserve_lazy_inductive(
                            materialized,
                            inductive,
                            substitutions.clone(),
                            reflected_substitutions.clone(),
                            &remapping,
                        );
                        remapping.inductive_ids.insert(inductive, id);
                        if fresh {
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
                        let (reflected_id, fresh) = env.reserve_lazy_inductive(
                            materialized,
                            reflected,
                            substitutions.clone(),
                            reflected_substitutions.clone(),
                            &remapping,
                        );
                        remapping.inductive_ids.insert(reflected, reflected_id);
                        if fresh {
                            lazy_inductives.push(reflected_id);
                        }
                        let (id, fresh) = env.reserve_lazy_program_inductive(
                            materialized,
                            inductive,
                            substitutions.clone(),
                            reflected_substitutions.clone(),
                            &remapping,
                        );
                        remapping.program_inductive_ids.insert(inductive, id);
                        if fresh {
                            lazy_datatypes.push(id);
                        }
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
                path_component,
                namespace: materialized,
                items,
                origins,
            });
        }

        for id in lazy_definitions {
            env.set_lazy_definition_remapping(id, remapping.clone());
        }
        for id in lazy_inductives {
            env.set_lazy_inductive_remapping(id, remapping.clone());
        }
        for id in lazy_datatypes {
            env.set_lazy_program_inductive_remapping(id, remapping.clone());
        }

        let mut last_binding = None;
        for group in groups {
            for item in group.items {
                env.publish_item(group.namespace, item)?;
            }
            let binding = env.add_namespace_binding(
                self.current,
                group.source,
                group.namespace,
                substitutions.clone(),
                group.origins,
                remapping.clone(),
            );
            if group.path_component {
                last_binding = Some(binding);
            }
        }

        Ok(last_binding.expect("non-empty route was checked above"))
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

    pub(crate) fn hir_import(&self, env: &CrateEnv, name: &Identifier) -> Option<ModuleId> {
        if let Some(id) = name.1 {
            self.hir_aliases.get(&id).copied()
        } else {
            env.resolve_import(self.current, name.as_str())
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
        for (source, instance) in &import.remapping {
            if let Some(source) = self.hir_modules.get(source).copied() {
                let target = typed
                    .remapping
                    .module_ids
                    .get(&source)
                    .copied()
                    .unwrap_or(source);
                self.hir_modules.insert(*instance, target);
            }
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
    let (mut module, reference, inherit) = match access {
        LocalAccess::Current { access, .. } => (from, access.as_str(), true),
        LocalAccess::Named { access, child, .. } => {
            let binding = env.resolve_import(from, access.as_str())?;
            (env.binding(binding).materialized, child.as_str(), false)
        }
        LocalAccess::Resolved { .. } => return None,
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
    use crate::raw::exp::ExpNode;
    use crate::raw::inductive::{CtorType, InductiveTypeSpecs};
    use crate::raw::sort::Sort;

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
        assert_ne!(first, second);

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
        let ExpNode::DefinedConstant(remapped_parent) =
            env.arena().get(pts_body(env.definition(*child_definition)))
        else {
            panic!("child definition should refer to the materialized parent definition")
        };
        assert_ne!(remapped_parent, parent_definition);
        let child = env
            .arena()
            .alloc(ExpNode::DefinedConstant(*child_definition));
        assert!(crate::raw::calculus::exp_is_alpha_eq(
            &env,
            crate::raw::calculus::whnf(&env, child),
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
        let module = env.module(env.binding(binding).materialized);
        let ModuleItem::Definition { definition, .. } = module.item("result").unwrap() else {
            unreachable!()
        };
        let result = env.arena().alloc(ExpNode::DefinedConstant(*definition));
        assert!(crate::raw::calculus::exp_is_alpha_eq(
            &env,
            crate::raw::calculus::whnf(&env, result),
            argument,
        ));
    }
}
