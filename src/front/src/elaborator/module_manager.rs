use crate::macros::{MacroInstantiation, ModuleMacroScope};
use crate::raw::calculus::{exp_subst_map, remap_all_global_ids};
use crate::raw::derivation::CheckSession;
#[cfg(test)]
use crate::raw::environment::ModuleParameter;
use crate::raw::environment::{
    CrateEnv, DefinedConstant, InstanceRemapping, ModuleArgument, ModuleItem, ModuleParameterKind,
};
use crate::raw::exp::{Exp, ExpContext, ExpContextEntry};
use crate::raw::ids::{
    DefId, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId, ProgramInductiveId,
};
#[cfg(test)]
use crate::raw::inductive::InductiveTypeSpecs;
use crate::raw::program::{ProgramContext, ProgramContextEntry};
use crate::syntax::{
    Identifier, LocalAccess, ModItemDefinition, ModItemInductive, ModItemProgramInductive,
    ModItemRecord,
};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) enum ItemAccessResult {
    Definition(ModItemDefinition),
    Inductive(ModItemInductive),
    Record(ModItemRecord),
    ProgramInductive(ModItemProgramInductive),
    Expression(Exp),
    ProgramTypeParameter(ModuleParamId),
    ProgramValueParameter(ModuleParamId),
}

#[derive(Debug)]
pub(crate) struct ModuleManager {
    current: ModuleId,
    pub(crate) macro_scopes: HashMap<ModuleId, ModuleMacroScope>,
    pub(crate) next_macro_order: u64,
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
            macro_scopes: HashMap::new(),
            next_macro_order: 0,
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
        instance: ModuleInstanceId,
    ) -> Result<(), String> {
        env.publish_import(self.current, import_name.0, instance)
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

    pub(crate) fn instantiate_module(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleInstanceId, String> {
        let source = self.resolve_start(env, back_parent)?;
        self.instantiate_module_from(env, context, source, None, calls)
    }

    pub(crate) fn instantiate_module_from_instance(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        base: ModuleInstanceId,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleInstanceId, String> {
        let source = env.instance(base).source;
        self.instantiate_module_from(env, context, source, Some(base), calls)
    }

    fn instantiate_module_from(
        &mut self,
        env: &mut CrateEnv,
        context: &mut ExpContext,
        mut source: ModuleId,
        base: Option<ModuleInstanceId>,
        calls: Vec<(Identifier, Vec<(Identifier, ModuleArgument)>)>,
    ) -> Result<ModuleInstanceId, String> {
        let (mut substitutions, mut remapping) = base.map_or_else(
            || (Vec::new(), InstanceRemapping::default()),
            |base| {
                let base = env.instance(base);
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
            let child = env
                .module(source)
                .children()
                .iter()
                .copied()
                .find(|child| env.module(*child).name() == child_name.as_str())
                .ok_or_else(|| {
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
                        let expected = exp_subst_map(env.arena(), ty, &reflected_substitutions);
                        let expected = remap_all_global_ids(
                            env.arena(),
                            expected,
                            &remapping.definition_ids,
                            &remapping.inductive_ids,
                            &remapping.program_inductive_ids,
                        );
                        CheckSession::new(env, self.current, context)
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
                        let expected = crate::raw::program_calculus::subst_value_type_module_params(
                            env.arena(),
                            ty,
                            &substitutions,
                        );
                        let expected = crate::raw::program_calculus::remap_value_type_global_ids(
                            env.arena(),
                            expected,
                            &remapping.definition_ids,
                            &remapping.program_inductive_ids,
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
            materialization_sources.extend(
                env.module(source_module)
                    .instances()
                    .iter()
                    .map(|instance| (instance.source, instance.materialized, false)),
            );
            materialization_sources.push((source_module, source_module, true));
        }

        struct ReservedGroup {
            source: ModuleId,
            item_source: ModuleId,
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
            let mut origins = HashMap::new();
            let mut reserve_definition = |env: &mut CrateEnv, source_id: DefId| {
                let id = env.reserve_lazy_definition(
                    materialized,
                    source_id,
                    substitutions.clone(),
                    reflected_substitutions.clone(),
                );
                remapping.definition_ids.insert(source_id, id);
                origins.insert(
                    id,
                    env.definition_origin(source_id)
                        .map_or(source_id, |origin| origin.source),
                );
                lazy_definitions.push(id);
                id
            };
            let mut items = Vec::new();
            for item in env.module(item_source).items().to_vec() {
                let item = match item {
                    ModuleItem::Definition { name, definition } => ModuleItem::Definition {
                        name,
                        definition: reserve_definition(env, definition),
                    },
                    ModuleItem::Inductive {
                        name,
                        constructor_names,
                        associated_definitions,
                        inductive,
                    } => {
                        let id = env.reserve_lazy_inductive(
                            materialized,
                            inductive,
                            reflected_substitutions.clone(),
                        );
                        remapping.inductive_ids.insert(inductive, id);
                        lazy_inductives.push(id);
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, id)))
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
                        let id = env.reserve_lazy_inductive(
                            materialized,
                            inductive,
                            reflected_substitutions.clone(),
                        );
                        remapping.inductive_ids.insert(inductive, id);
                        lazy_inductives.push(id);
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, id)))
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
                            reflected_substitutions.clone(),
                        );
                        remapping.inductive_ids.insert(reflected, reflected_id);
                        lazy_inductives.push(reflected_id);
                        let id = env.reserve_lazy_program_inductive(
                            materialized,
                            inductive,
                            substitutions.clone(),
                        );
                        remapping.program_inductive_ids.insert(inductive, id);
                        lazy_datatypes.push(id);
                        let associated_definitions = associated_definitions
                            .into_iter()
                            .map(|(name, id)| (name, reserve_definition(env, id)))
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

        let mut last_instance = None;
        for group in groups {
            for item in group.items {
                env.publish_item(group.namespace, item)?;
            }
            self.materialize_macros(
                env,
                group.item_source,
                group.namespace,
                &MacroInstantiation {
                    module_ids: &remapping.module_ids,
                    substitutions: &reflected_substitutions,
                    definition_ids: &remapping.definition_ids,
                    inductive_ids: &remapping.inductive_ids,
                    program_inductive_ids: &remapping.program_inductive_ids,
                },
            );
            let instance = env.add_instance_with_remapping(
                self.current,
                group.source,
                group.namespace,
                substitutions.clone(),
                group.origins,
                remapping.clone(),
            );
            if group.path_component {
                last_instance = Some(instance);
            }
        }

        Ok(last_instance.expect("non-empty route was checked above"))
    }

    pub(crate) fn get_item(
        &self,
        env: &CrateEnv,
        access: &LocalAccess,
    ) -> Option<ItemAccessResult> {
        match access {
            LocalAccess::Current { access } => {
                let mut module = self.current;
                loop {
                    let current = env.module(module);
                    if let Some(item) = current.item(access.as_str()) {
                        return Some(convert_item(item));
                    }
                    if let Some(parameter) = current
                        .parameters()
                        .iter()
                        .find(|parameter| env.symbol(parameter.name) == access.as_str())
                    {
                        let position = current
                            .parameters()
                            .iter()
                            .position(|p| p.name == parameter.name)
                            .unwrap() as u32;
                        return Some(parameter_access(
                            env,
                            ModuleParamId { module, position },
                            parameter.kind,
                        ));
                    }
                    module = current.parent()?;
                }
            }
            LocalAccess::Named { access, child } => {
                let instance = env.module(self.current).import(access.as_str())?;
                let materialized = env.instance(instance).materialized;
                env.module(materialized)
                    .item(child.as_str())
                    .map(convert_item)
            }
            LocalAccess::Resolved { module, access } => env
                .module(*module)
                .item(access.as_str())
                .map(convert_item)
                .or_else(|| {
                    env.module(*module)
                        .parameters()
                        .iter()
                        .position(|parameter| env.symbol(parameter.name) == access.as_str())
                        .map(|position| {
                            parameter_access(
                                env,
                                ModuleParamId {
                                    module: *module,
                                    position: position as u32,
                                },
                                env.module(*module).parameters()[position].kind,
                            )
                        })
                }),
        }
    }
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
    fn instance_declarations_materialize_only_when_requested() {
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

        let instance = manager
            .instantiate_module(
                &mut env,
                &mut Vec::new(),
                None,
                vec![(Identifier("Source".into()), vec![])],
            )
            .unwrap();
        let namespace = env.instance(instance).materialized;
        let id = |name| match env.module(namespace).item(name).unwrap() {
            ModuleItem::Definition { definition, .. } => *definition,
            _ => unreachable!(),
        };
        let used = id("used");
        let unused = id("unused");
        assert!(!env.is_definition_materialized(used));
        assert!(!env.is_definition_materialized(unused));
        assert_eq!(env.materialization_stats().definitions, 0);

        let _ = env.resolve_definition(used).unwrap();
        assert!(env.is_definition_materialized(used));
        assert!(!env.is_definition_materialized(unused));
        assert_eq!(env.materialization_stats().definitions, 1);
        let _ = env.resolve_definition(used).unwrap();
        assert_eq!(env.materialization_stats().definitions, 1);
    }

    #[test]
    fn repeated_instantiation_is_generative_and_remaps_internal_definitions() {
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
                .instantiate_module(
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

        let ids = |env: &CrateEnv, instance| {
            env.module(env.instance(instance).materialized)
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
        assert_ne!(first_ids, second_ids);
        assert_eq!(env.materialized_instance(first_ids[0].module), Some(first));
        assert_eq!(
            env.materialized_instance(second_ids[0].module),
            Some(second)
        );
        assert_eq!(
            env.definition_origin(first_ids[0]),
            Some(crate::raw::environment::DefinitionOrigin {
                instance: first,
                source: base,
            })
        );
        assert_eq!(
            env.definition_origin(second_ids[0]),
            Some(crate::raw::environment::DefinitionOrigin {
                instance: second,
                source: base,
            })
        );
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
                .instantiate_module(
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
                .instantiate_module(
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
        assert!(env.module(env.root_module()).instances().is_empty());

        let carrier = env.intern("Carrier");
        let argument = env.arena().exp_bound(0);
        let mut context = vec![ExpContextEntry {
            var: carrier,
            ty: set,
        }];
        assert!(
            manager
                .instantiate_module(
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
    fn inductives_from_two_instances_are_distinct_types() {
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
                .instantiate_module(
                    env,
                    &mut Vec::new(),
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&mut manager, &mut env);
        let second = instantiate(&mut manager, &mut env);
        let inductive = |env: &CrateEnv, instance| {
            let module = env.module(env.instance(instance).materialized);
            let ModuleItem::Inductive { inductive, .. } = module.item("Token").unwrap() else {
                unreachable!()
            };
            *inductive
        };
        let first = inductive(&env, first);
        let second = inductive(&env, second);
        assert_ne!(first, second);
        assert!(!env.is_inductive_materialized(first));
        assert!(!env.is_inductive_materialized(second));

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
            CheckSession::new(&env, env.root_module(), &mut Vec::new())
                .check_pts(first_constructor, first_type)
                .is_ok()
        );
        assert!(env.is_inductive_materialized(first));
        assert!(!env.is_inductive_materialized(second));
        assert!(
            CheckSession::new(&env, env.root_module(), &mut Vec::new())
                .check_pts(first_constructor, second_type)
                .is_err()
        );
    }

    #[test]
    fn nested_instance_materializes_parent_dependencies() {
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
        let instance = manager
            .instantiate_module(
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
        let final_module = env.module(env.instance(instance).materialized);
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
    fn outer_instantiation_rematerializes_parameterized_imports() {
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
            .instantiate_module(
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
        let instance = manager
            .instantiate_module(
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
        let module = env.module(env.instance(instance).materialized);
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
