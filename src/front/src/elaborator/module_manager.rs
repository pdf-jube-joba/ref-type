use crate::syntax::{
    Identifier, LocalAccess, ModItemDefinition, ModItemInductive, ModItemProgramInductive,
    ModItemRecord,
};
use kernel::calculus::{exp_subst_map, remap_all_global_ids};
use kernel::derivation::CheckSession;
use kernel::environment::{
    CrateEnv, DefinedConstant, ModuleItem, ModuleParameter, ModuleParameterKind,
};
use kernel::exp::{Context, ContextEntry, Exp};
use kernel::ids::{
    DefId, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId, ProgramInductiveId,
};
use kernel::inductive::InductiveTypeSpecs;
use kernel::program_inductive::ProgramInductiveTypeSpecs;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum ItemAccessResult {
    Definition(ModItemDefinition),
    Inductive(ModItemInductive),
    Record(ModItemRecord),
    ProgramInductive(ModItemProgramInductive),
    Expression(Exp),
}

enum PendingItem {
    Definition(String, DefId, DefId, DefinedConstant),
    Inductive(
        String,
        Vec<String>,
        InductiveId,
        InductiveTypeSpecs,
        Vec<PendingAssociatedDefinition>,
    ),
    Record(
        String,
        InductiveId,
        InductiveTypeSpecs,
        Vec<PendingAssociatedDefinition>,
    ),
    ProgramInductive(
        String,
        Vec<String>,
        ProgramInductiveId,
        InductiveId,
        ProgramInductiveTypeSpecs,
        InductiveTypeSpecs,
        Vec<PendingAssociatedDefinition>,
    ),
}

type PendingAssociatedDefinition = (String, DefId, DefId, DefinedConstant);

fn instantiate_associated_definitions(
    env: &CrateEnv,
    definitions: Vec<(String, DefId)>,
    substitutions: &[(ModuleParamId, Exp)],
) -> Vec<PendingAssociatedDefinition> {
    definitions
        .into_iter()
        .map(|(name, source_id)| {
            let value = env.definition(source_id);
            let origin = env
                .definition_origin(source_id)
                .map_or(source_id, |origin| origin.source);
            (
                name,
                source_id,
                origin,
                DefinedConstant {
                    kind: value.kind,
                    ty: exp_subst_map(env.arena(), value.ty, substitutions),
                    body: exp_subst_map(env.arena(), value.body, substitutions),
                },
            )
        })
        .collect()
}

fn materialize_associated_definitions(
    env: &mut CrateEnv,
    module: ModuleId,
    owner: &str,
    pending: Vec<PendingAssociatedDefinition>,
    definition_ids: &mut HashMap<DefId, DefId>,
    inductive_ids: &HashMap<InductiveId, InductiveId>,
    program_inductive_ids: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    definition_origins: &mut HashMap<DefId, DefId>,
) -> Result<(), String> {
    for (name, source_id, origin, definition) in pending {
        let definition = DefinedConstant {
            kind: definition.kind,
            ty: remap_all_global_ids(
                env.arena(),
                definition.ty,
                definition_ids,
                inductive_ids,
                program_inductive_ids,
            ),
            body: remap_all_global_ids(
                env.arena(),
                definition.body,
                definition_ids,
                inductive_ids,
                program_inductive_ids,
            ),
        };
        let materialized = env.add_definition(module, definition);
        definition_ids.insert(source_id, materialized);
        definition_origins.insert(materialized, origin);
        env.publish_associated_definition(module, owner, name, materialized)?;
    }
    Ok(())
}

#[derive(Debug)]
pub struct ModuleManager {
    current: ModuleId,
}

impl Default for ModuleManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleManager {
    pub fn new() -> Self {
        Self {
            current: ModuleId(0),
        }
    }

    pub fn current(&self) -> ModuleId {
        self.current
    }

    pub fn add_child_and_moveto(
        &mut self,
        env: &mut CrateEnv,
        module_name: String,
        parameters: Vec<ModuleParameter>,
    ) -> Result<(), String> {
        self.current = env.add_child_module(self.current, module_name, parameters)?;
        Ok(())
    }

    pub fn reserve_child_and_moveto(
        &mut self,
        env: &mut CrateEnv,
        module_name: String,
    ) -> ModuleId {
        let id = env.reserve_child_module(self.current, module_name);
        self.current = id;
        id
    }

    pub fn moveto_parent(&mut self, env: &CrateEnv) {
        if let Some(parent) = env.module(self.current).parent() {
            self.current = parent;
        }
    }

    pub fn publish_current_module(&self, env: &mut CrateEnv) -> Result<(), String> {
        env.publish_child_module(self.current)
    }

    pub fn moveto_root(&mut self) {
        self.current = ModuleId(0);
    }

    pub fn current_context(&self, env: &CrateEnv) -> Context {
        let mut context = Vec::new();
        let mut current = self.current;
        loop {
            let module = env.module(current);
            context.push(
                module
                    .parameters()
                    .iter()
                    .map(|parameter| match parameter.kind {
                        ModuleParameterKind::Pts { ty } => ContextEntry::Pts {
                            var: parameter.name,
                            ty,
                        },
                        ModuleParameterKind::ProgramType => ContextEntry::ProgramType {
                            var: parameter.name,
                        },
                        ModuleParameterKind::ProgramValue { ty } => ContextEntry::ProgramValue {
                            var: parameter.name,
                            ty,
                        },
                    })
                    .collect::<Context>(),
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

    pub fn add_def(
        &mut self,
        env: &mut CrateEnv,
        name: Identifier,
        definition: DefinedConstant,
    ) -> Result<(), String> {
        let definition = env.add_definition(self.current, definition);
        env.publish_item(
            self.current,
            ModuleItem::Definition {
                name: name.0,
                definition,
            },
        )
    }

    pub fn add_associated_def(
        &mut self,
        env: &mut CrateEnv,
        owner: &Identifier,
        name: Identifier,
        definition: DefinedConstant,
    ) -> Result<(), String> {
        let definition = env.add_definition(self.current, definition);
        env.publish_associated_definition(self.current, owner.as_str(), name.0, definition)
    }

    pub fn associated_parameter_count(&self, env: &CrateEnv, owner: &Identifier) -> Option<usize> {
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

    pub fn add_inductive(
        &mut self,
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

    pub fn publish_reserved_inductive(
        &mut self,
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

    pub fn publish_reserved_program_inductive(
        &mut self,
        env: &mut CrateEnv,
        type_name: Identifier,
        constructor_names: Vec<Identifier>,
        inductive: ProgramInductiveId,
        reflected: InductiveId,
    ) -> Result<(), String> {
        env.publish_item(
            self.current,
            ModuleItem::ProgramInductive {
                name: type_name.0,
                constructor_names: constructor_names.into_iter().map(|name| name.0).collect(),
                associated_definitions: Vec::new(),
                inductive,
                reflected,
            },
        )
    }

    pub fn add_record(
        &mut self,
        env: &mut CrateEnv,
        type_name: Identifier,
        spec: InductiveTypeSpecs,
    ) -> Result<(), String> {
        let inductive = env.add_inductive(self.current, spec);
        env.publish_item(
            self.current,
            ModuleItem::Record {
                name: type_name.0,
                associated_definitions: Vec::new(),
                inductive,
            },
        )
    }

    pub fn publish_reserved_record(
        &mut self,
        env: &mut CrateEnv,
        type_name: Identifier,
        inductive: InductiveId,
    ) -> Result<(), String> {
        env.publish_item(
            self.current,
            ModuleItem::Record {
                name: type_name.0,
                associated_definitions: Vec::new(),
                inductive,
            },
        )
    }

    pub fn add_import(
        &mut self,
        env: &mut CrateEnv,
        import_name: Identifier,
        instance: ModuleInstanceId,
    ) -> Result<(), String> {
        env.publish_import(self.current, import_name.0, instance)
    }

    pub fn get_moditem_record(
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

    pub fn instantiate_module(
        &self,
        env: &mut CrateEnv,
        context: &mut Context,
        back_parent: Option<usize>,
        calls: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    ) -> Result<ModuleInstanceId, String> {
        let mut source = self.resolve_start(env, back_parent)?;
        let mut substitutions = Vec::new();
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
                let mut session = CheckSession::new(env, self.current, context);
                let checked = match parameter.kind {
                    ModuleParameterKind::Pts { ty } => {
                        let expected = exp_subst_map(env.arena(), ty, &substitutions);
                        session.check_pts(*argument, expected)
                    }
                    ModuleParameterKind::ProgramType => session.check_value_type(*argument),
                    ModuleParameterKind::ProgramValue { ty } => {
                        let expected = exp_subst_map(env.arena(), ty, &substitutions);
                        session.check_value(*argument, expected)
                    }
                };
                checked.map_err(|error| {
                    format!(
                        "Module '{}' argument '{}' failed type checking: {error:?}",
                        child_name.as_str(),
                        argument_name.as_str(),
                    )
                })?;
                substitutions.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    *argument,
                ));
            }
            source = child;
            route.push(child);
        }

        if route.is_empty() {
            return Err("Module instantiation path must contain at least one module".into());
        }

        // Prepare every module on the path before allocating any instance IDs.
        // Parent items may be referenced by a nested module and must therefore
        // be materialized first, even though only the final module is named.
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

        let mut pending_groups = Vec::with_capacity(materialization_sources.len());
        for (instance_source, item_source, is_path_component) in materialization_sources {
            let source_items = env.module(item_source).items().to_vec();
            let mut pending = Vec::with_capacity(source_items.len());
            for item in source_items {
                pending.push(match item {
                    ModuleItem::Definition { name, definition } => {
                        let definition_value = env.definition(definition).clone();
                        let origin = env
                            .definition_origin(definition)
                            .map_or(definition, |origin| origin.source);
                        PendingItem::Definition(
                            name,
                            definition,
                            origin,
                            DefinedConstant {
                                kind: definition_value.kind,
                                ty: exp_subst_map(env.arena(), definition_value.ty, &substitutions),
                                body: exp_subst_map(
                                    env.arena(),
                                    definition_value.body,
                                    &substitutions,
                                ),
                            },
                        )
                    }
                    ModuleItem::Inductive {
                        name,
                        constructor_names,
                        associated_definitions,
                        inductive,
                    } => {
                        let spec = env.inductive(inductive).clone();
                        let instantiated = spec.instantiate(env.arena(), &substitutions);
                        PendingItem::Inductive(
                            name,
                            constructor_names,
                            inductive,
                            instantiated,
                            instantiate_associated_definitions(
                                env,
                                associated_definitions,
                                &substitutions,
                            ),
                        )
                    }
                    ModuleItem::Record {
                        name,
                        associated_definitions,
                        inductive,
                    } => {
                        let spec = env.inductive(inductive).clone();
                        let instantiated = spec.instantiate(env.arena(), &substitutions);
                        PendingItem::Record(
                            name,
                            inductive,
                            instantiated,
                            instantiate_associated_definitions(
                                env,
                                associated_definitions,
                                &substitutions,
                            ),
                        )
                    }
                    ModuleItem::ProgramInductive {
                        name,
                        constructor_names,
                        inductive,
                        reflected,
                        associated_definitions,
                    } => {
                        let spec = env
                            .program_inductive(inductive)
                            .clone()
                            .instantiate(env.arena(), &substitutions);
                        let reflected_spec = env
                            .inductive(reflected)
                            .clone()
                            .instantiate(env.arena(), &substitutions);
                        PendingItem::ProgramInductive(
                            name,
                            constructor_names,
                            inductive,
                            reflected,
                            spec,
                            reflected_spec,
                            instantiate_associated_definitions(
                                env,
                                associated_definitions,
                                &substitutions,
                            ),
                        )
                    }
                });
            }
            pending_groups.push((instance_source, is_path_component, pending));
        }

        let mut definition_ids = HashMap::new();
        let mut inductive_ids = HashMap::new();
        let mut program_inductive_ids = HashMap::new();
        let mut last_instance = None;
        for (source_module, is_path_component, pending) in pending_groups {
            let materialized = env.add_module();
            let mut definition_origins = HashMap::new();
            for item in pending {
                match item {
                    PendingItem::Definition(name, source_id, origin, definition) => {
                        let definition = DefinedConstant {
                            kind: definition.kind,
                            ty: remap_all_global_ids(
                                env.arena(),
                                definition.ty,
                                &definition_ids,
                                &inductive_ids,
                                &program_inductive_ids,
                            ),
                            body: remap_all_global_ids(
                                env.arena(),
                                definition.body,
                                &definition_ids,
                                &inductive_ids,
                                &program_inductive_ids,
                            ),
                        };
                        let definition = env.add_definition(materialized, definition);
                        definition_ids.insert(source_id, definition);
                        definition_origins.insert(definition, origin);
                        env.publish_item(
                            materialized,
                            ModuleItem::Definition { name, definition },
                        )?;
                    }
                    PendingItem::Inductive(
                        name,
                        constructor_names,
                        source_id,
                        spec,
                        associated,
                    ) => {
                        let inductive = env.reserve_inductive(materialized);
                        inductive_ids.insert(source_id, inductive);
                        let spec =
                            spec.remap_global_ids(env.arena(), &definition_ids, &inductive_ids);
                        env.define_inductive(inductive, spec);
                        env.publish_item(
                            materialized,
                            ModuleItem::Inductive {
                                name: name.clone(),
                                constructor_names,
                                associated_definitions: Vec::new(),
                                inductive,
                            },
                        )?;
                        materialize_associated_definitions(
                            env,
                            materialized,
                            &name,
                            associated,
                            &mut definition_ids,
                            &inductive_ids,
                            &program_inductive_ids,
                            &mut definition_origins,
                        )?;
                    }
                    PendingItem::Record(name, source_id, spec, associated) => {
                        let inductive = env.reserve_inductive(materialized);
                        inductive_ids.insert(source_id, inductive);
                        let spec =
                            spec.remap_global_ids(env.arena(), &definition_ids, &inductive_ids);
                        env.define_inductive(inductive, spec);
                        env.publish_item(
                            materialized,
                            ModuleItem::Record {
                                name: name.clone(),
                                associated_definitions: Vec::new(),
                                inductive,
                            },
                        )?;
                        materialize_associated_definitions(
                            env,
                            materialized,
                            &name,
                            associated,
                            &mut definition_ids,
                            &inductive_ids,
                            &program_inductive_ids,
                            &mut definition_origins,
                        )?;
                    }
                    PendingItem::ProgramInductive(
                        name,
                        constructor_names,
                        source_id,
                        reflected_source_id,
                        spec,
                        reflected_spec,
                        associated,
                    ) => {
                        let reflected = env.reserve_inductive(materialized);
                        inductive_ids.insert(reflected_source_id, reflected);
                        let inductive = env.reserve_program_inductive(materialized);
                        program_inductive_ids.insert(source_id, inductive);
                        let reflected_spec = reflected_spec.remap_global_ids(
                            env.arena(),
                            &definition_ids,
                            &inductive_ids,
                        );
                        let spec = spec.remap_global_ids(
                            env.arena(),
                            &definition_ids,
                            &inductive_ids,
                            &program_inductive_ids,
                        );
                        env.define_inductive(reflected, reflected_spec);
                        env.define_program_inductive(inductive, spec);
                        env.publish_item(
                            materialized,
                            ModuleItem::ProgramInductive {
                                name: name.clone(),
                                constructor_names,
                                associated_definitions: Vec::new(),
                                inductive,
                                reflected,
                            },
                        )?;
                        materialize_associated_definitions(
                            env,
                            materialized,
                            &name,
                            associated,
                            &mut definition_ids,
                            &inductive_ids,
                            &program_inductive_ids,
                            &mut definition_origins,
                        )?;
                    }
                }
            }
            let instance = env.add_instance(
                self.current,
                source_module,
                materialized,
                substitutions.clone(),
                definition_origins,
            );
            if is_path_component {
                last_instance = Some(instance);
            }
        }

        Ok(last_instance.expect("non-empty route was checked above"))
    }

    pub fn get_item(&self, env: &CrateEnv, access: &LocalAccess) -> Option<ItemAccessResult> {
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
                        return Some(ItemAccessResult::Expression(
                            env.arena().module_param(ModuleParamId {
                                module,
                                position: current
                                    .parameters()
                                    .iter()
                                    .position(|p| p.name == parameter.name)
                                    .unwrap() as u32,
                            }),
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
        }
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
            name,
            constructor_names,
            associated_definitions,
            inductive,
            reflected,
        } => ItemAccessResult::ProgramInductive(ModItemProgramInductive {
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
    use kernel::environment::DefinitionKind;
    use kernel::exp::Node;
    use kernel::inductive::{CtorType, InductiveTypeSpecs};
    use kernel::sort::Sort;

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
                DefinedConstant {
                    kind: DefinitionKind::Pts,
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
        let base_exp = env.arena().alloc(Node::DefinedConstant(base));
        manager
            .add_def(
                &mut env,
                Identifier("alias".into()),
                DefinedConstant {
                    kind: DefinitionKind::Pts,
                    ty: proposition_kind,
                    body: base_exp,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let instantiate = |manager: &ModuleManager, env: &mut CrateEnv| {
            manager
                .instantiate_module(
                    env,
                    &mut Vec::new(),
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&manager, &mut env);
        let second = instantiate(&manager, &mut env);
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
            Some(kernel::environment::DefinitionOrigin {
                instance: first,
                source: base,
            })
        );
        assert_eq!(
            env.definition_origin(second_ids[0]),
            Some(kernel::environment::DefinitionOrigin {
                instance: second,
                source: base,
            })
        );
        assert_eq!(env.definition_origin(base), None);
        assert!(matches!(
            env.arena().get(env.definition(first_ids[1]).body),
            Node::DefinedConstant(id) if id == first_ids[0]
        ));
        assert!(matches!(
            env.arena().get(env.definition(second_ids[1]).body),
            Node::DefinedConstant(id) if id == second_ids[0]
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
                        vec![(Identifier("wrong".into()), wrong_argument)],
                    ),
                )
                .is_err()
        );
        assert!(env.module(env.root_module()).instances().is_empty());

        let carrier = env.intern("Carrier");
        let argument = env.arena().bound(0);
        let mut context = vec![ContextEntry::Pts {
            var: carrier,
            ty: set,
        }];
        assert!(
            manager
                .instantiate_module(
                    &mut env,
                    &mut context,
                    None,
                    call("Parameterized", vec![(Identifier("A".into()), argument)],),
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

        let instantiate = |manager: &ModuleManager, env: &mut CrateEnv| {
            manager
                .instantiate_module(
                    env,
                    &mut Vec::new(),
                    None,
                    vec![(Identifier("Source".into()), vec![])],
                )
                .unwrap()
        };
        let first = instantiate(&manager, &mut env);
        let second = instantiate(&manager, &mut env);
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

        let first_constructor = env.arena().alloc(Node::IndCtor {
            indspec: first,
            parameters: vec![],
            idx: 0,
        });
        let first_type = env.arena().alloc(Node::IndType {
            indspec: first,
            parameters: vec![],
        });
        let second_type = env.arena().alloc(Node::IndType {
            indspec: second,
            parameters: vec![],
        });
        assert!(
            CheckSession::new(&env, env.root_module(), &mut Vec::new())
                .check(first_constructor, first_type)
                .is_ok()
        );
        assert!(
            CheckSession::new(&env, env.root_module(), &mut Vec::new())
                .check(first_constructor, second_type)
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
        let parameter_exp = env.arena().module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager
            .add_def(
                &mut env,
                Identifier("parent_value".into()),
                DefinedConstant {
                    kind: DefinitionKind::Pts,
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
        let parent_reference = env.arena().alloc(Node::DefinedConstant(parent_definition));
        manager
            .add_def(
                &mut env,
                Identifier("child_value".into()),
                DefinedConstant {
                    kind: DefinitionKind::Pts,
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
        let argument = env.arena().bound(0);
        let mut context = vec![ContextEntry::Pts {
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
                        vec![(Identifier("A".into()), argument)],
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
        let Node::DefinedConstant(remapped_parent) =
            env.arena().get(env.definition(*child_definition).body)
        else {
            panic!("child definition should refer to the materialized parent definition")
        };
        assert_ne!(remapped_parent, parent_definition);
        let child = env.arena().alloc(Node::DefinedConstant(*child_definition));
        assert!(kernel::calculus::exp_is_alpha_eq(
            &env,
            kernel::calculus::whnf(&env, child),
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
        let parameter_exp = env.arena().module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        manager
            .add_def(
                &mut env,
                Identifier("value".into()),
                DefinedConstant {
                    kind: DefinitionKind::Pts,
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
        let outer_argument = env.arena().module_param(ModuleParamId {
            module: manager.current(),
            position: 0,
        });
        let dependency = manager
            .instantiate_module(
                &mut env,
                &mut vec![ContextEntry::Pts {
                    var: outer_context_var,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Param".into()),
                    vec![(Identifier("A".into()), outer_argument)],
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
            .alloc(Node::DefinedConstant(imported_value.definition));
        manager
            .add_def(
                &mut env,
                Identifier("result".into()),
                DefinedConstant {
                    kind: DefinitionKind::Pts,
                    ty: set,
                    body: imported_value,
                },
            )
            .unwrap();
        manager.publish_current_module(&mut env).unwrap();
        manager.moveto_parent(&env);

        let carrier = env.intern("Carrier");
        let argument = env.arena().bound(0);
        let instance = manager
            .instantiate_module(
                &mut env,
                &mut vec![ContextEntry::Pts {
                    var: carrier,
                    ty: set,
                }],
                None,
                vec![(
                    Identifier("Outer".into()),
                    vec![(Identifier("A".into()), argument)],
                )],
            )
            .unwrap();
        let module = env.module(env.instance(instance).materialized);
        let ModuleItem::Definition { definition, .. } = module.item("result").unwrap() else {
            unreachable!()
        };
        let result = env.arena().alloc(Node::DefinedConstant(*definition));
        assert!(kernel::calculus::exp_is_alpha_eq(
            &env,
            kernel::calculus::whnf(&env, result),
            argument,
        ));
    }
}
