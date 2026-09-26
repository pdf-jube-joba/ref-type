//! Arena-independent observations produced while elaborating declarations.
use crate::{
    elaborator::{GlobalEnvironment, module_manager::ItemAccessResult},
    hir::{ModuleItem, SourceLocation},
    raw::{
        environment::{CrateEnv, DefinedConstant, ModuleItem as Item},
        ids::ModuleId,
        printing,
    },
};

#[derive(Debug, Clone)]
pub struct Declaration {
    pub module: Vec<String>,
    pub name: String,
    pub kind: &'static str,
    pub location: SourceLocation,
    pub ty: Option<String>,
}

pub use resolve::Reference;

#[derive(Debug, Clone)]
pub struct Output {
    pub module: Vec<String>,
    pub location: SourceLocation,
    pub text: String,
}

#[derive(Default, Debug)]
pub struct Analysis {
    pub declarations: Vec<Declaration>,
    pub references: Vec<Reference>,
    pub outputs: Vec<Output>,
}

pub(crate) fn module_path(env: &CrateEnv, mut module: ModuleId) -> Vec<String> {
    let mut path = Vec::new();
    loop {
        if env.namespace_binding_id(module).is_some() {
            module = env.binding(module).source;
        }
        let current = env.module(module);
        let Some(parent) = current.parent() else {
            break;
        };
        path.push(crate::raw::printing::module_component(env, module));
        module = parent;
    }
    path.reverse();
    path
}

pub(crate) fn access_name(env: &CrateEnv, item: &ItemAccessResult) -> Option<String> {
    Some(match item {
        ItemAccessResult::Definition(item) | ItemAccessResult::ReflectedDefinition(item) => {
            item.def_name.0.clone()
        }
        ItemAccessResult::Inductive(item) => item.type_name.0.clone(),
        ItemAccessResult::Record(item) => item.type_name.0.clone(),
        ItemAccessResult::ProgramInductive(item) => item.type_name.0.clone(),
        ItemAccessResult::ProgramTypeParameter(id)
        | ItemAccessResult::ProgramValueParameter(id) => env
            .symbol(
                env.module(id.module)
                    .parameters()
                    .get(id.position as usize)?
                    .name,
            )
            .to_owned(),
        ItemAccessResult::Argument(_) => return None,
        ItemAccessResult::Expression(exp) => {
            let (crate::raw::exp::ExpNode::ModuleParam(id)
            | crate::raw::exp::ExpNode::ReflectedProgramParam(id)) = env.arena().get(*exp)
            else {
                return None;
            };
            env.symbol(
                env.module(id.module)
                    .parameters()
                    .get(id.position as usize)?
                    .name,
            )
            .to_owned()
        }
    })
}

fn definition_type(env: &CrateEnv, id: crate::raw::ids::DefId) -> String {
    match env.definition(id) {
        DefinedConstant::Pts { ty, .. } => printing::format_exp(env, *ty),
        DefinedConstant::ProgramValue { ty, .. } => printing::format_value_type(env, *ty),
        DefinedConstant::ProgramComputation { ty, .. } => {
            printing::format_computation_type(env, *ty)
        }
    }
}

impl GlobalEnvironment {
    pub fn active_module_path(&self) -> Vec<String> {
        module_path(&self.crate_env, self.module_manager.current())
    }

    pub fn analysis(&self) -> &Analysis {
        &self.analysis
    }

    pub(crate) fn record_declaration(&mut self, item: &ModuleItem, output_start: usize) {
        let Some(location) = self.diagnostic_location.clone() else {
            return;
        };
        let env = &self.crate_env;
        let module_id = self.module_manager.current();
        let module = module_path(env, module_id);
        for output in &self.outputs[output_start..] {
            self.analysis.outputs.push(Output {
                module: module.clone(),
                location: location.clone(),
                text: crate::output::format_output(env, output),
            });
        }
        let (name, kind, owner) = match item {
            ModuleItem::Definition { name, owner, .. } => (
                name.as_str(),
                "definition",
                owner.as_ref().map(|owner| owner.type_name.as_str()),
            ),
            ModuleItem::Inductive { type_name, .. } => (type_name.as_str(), "inductive", None),
            ModuleItem::Record { type_name, .. } => (type_name.as_str(), "record", None),
            ModuleItem::Import { import_name, .. } => (import_name.as_str(), "import", None),
            ModuleItem::MathMacro { name, .. } | ModuleItem::UserMacro { name, .. } => {
                (name.as_str(), "macro", None)
            }
            _ => return,
        };
        let published = env.module(module_id).item(owner.unwrap_or(name));
        let ty = match published {
            Some(Item::Definition { definition, .. }) => Some(definition_type(env, *definition)),
            Some(
                Item::Inductive {
                    inductive,
                    associated_definitions,
                    ..
                }
                | Item::Record {
                    inductive,
                    associated_definitions,
                    ..
                },
            ) => {
                if owner.is_some() {
                    associated_definitions
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, id)| definition_type(env, *id))
                } else {
                    let spec = env.inductive(*inductive);
                    Some(printing::format_exp(
                        env,
                        crate::raw::utils::assoc_prod(
                            env.arena(),
                            spec.parameters().to_vec(),
                            spec.arity(env.arena()),
                        ),
                    ))
                }
            }
            Some(Item::ProgramInductive {
                associated_definitions,
                ..
            }) => {
                if owner.is_some() {
                    associated_definitions
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, id)| definition_type(env, *id))
                } else {
                    Some("\\VType".into())
                }
            }
            _ => None,
        };
        self.analysis.declarations.push(Declaration {
            module: module.clone(),
            name: owner.map_or_else(|| name.to_owned(), |owner| format!("{owner}::{name}")),
            kind,
            location: location.clone(),
            ty,
        });
        if owner.is_none() {
            match published {
                Some(Item::Inductive {
                    inductive,
                    constructor_names,
                    ..
                }) => {
                    for (index, constructor) in constructor_names.iter().enumerate() {
                        self.analysis.declarations.push(Declaration {
                            module: module.clone(),
                            name: format!("{name}::{constructor}"),
                            kind: "constructor",
                            location: location.clone(),
                            ty: Some(constructor_type(env, *inductive, index)),
                        });
                    }
                }
                Some(Item::Record {
                    inductive,
                    associated_definitions,
                    ..
                }) => {
                    self.analysis.declarations.push(Declaration {
                        module: module.clone(),
                        name: format!("{name}::#"),
                        kind: "constructor",
                        location: location.clone(),
                        ty: Some(constructor_type(env, *inductive, 0)),
                    });
                    for (field, definition) in associated_definitions {
                        self.analysis.declarations.push(Declaration {
                            module: module.clone(),
                            name: format!("{name}::{field}"),
                            kind: "field",
                            location: location.clone(),
                            ty: Some(definition_type(env, *definition)),
                        });
                    }
                }
                Some(Item::ProgramInductive {
                    constructor_names,
                    inductive,
                    associated_definitions,
                    ..
                }) => {
                    for (index, constructor) in constructor_names.iter().enumerate() {
                        self.analysis.declarations.push(Declaration {
                            module: module.clone(),
                            name: format!("{name}::{constructor}"),
                            kind: "constructor",
                            location: location.clone(),
                            ty: Some(program_constructor_type(env, *inductive, index)),
                        });
                    }
                    for (field, definition) in associated_definitions {
                        self.analysis.declarations.push(Declaration {
                            module: module.clone(),
                            name: format!("{name}::{field}"),
                            kind: "field",
                            location: location.clone(),
                            ty: Some(definition_type(env, *definition)),
                        });
                    }
                }
                _ => {}
            }
        }
    }

    pub(crate) fn record_parameters(&mut self) {
        let Some(location) = self.diagnostic_location.clone() else {
            return;
        };
        let env = &self.crate_env;
        let id = self.module_manager.current();
        let module = module_path(env, id);
        for parameter in env.module(id).parameters() {
            let ty = match parameter.kind {
                crate::raw::environment::ModuleParameterKind::Pts { ty } => {
                    printing::format_exp(env, ty)
                }
                crate::raw::environment::ModuleParameterKind::ProgramType => "\\VType".into(),
                crate::raw::environment::ModuleParameterKind::ProgramValue { ty } => {
                    printing::format_value_type(env, ty)
                }
            };
            self.analysis.declarations.push(Declaration {
                module: module.clone(),
                name: env.symbol(parameter.name).to_owned(),
                kind: "parameter",
                location: location.clone(),
                ty: Some(ty),
            });
        }
    }

    pub(crate) fn collect_references(&mut self) {
        self.analysis
            .references
            .extend(self.module_manager.references.borrow_mut().drain(..));
    }
}

fn constructor_type(env: &CrateEnv, id: crate::raw::ids::InductiveId, index: usize) -> String {
    let spec = env.inductive(id);
    let parameters = (0..spec.parameters().len())
        .rev()
        .map(|index| env.arena().alloc(crate::raw::exp::ExpNode::Bound(index)))
        .collect();
    let ty = crate::raw::inductive::InductiveTypeSpecs::type_of_constructor(
        env.arena(),
        id,
        spec,
        index,
        parameters,
    );
    printing::format_exp(
        env,
        crate::raw::utils::assoc_prod(env.arena(), spec.parameters().to_vec(), ty),
    )
}

fn program_constructor_type(
    env: &CrateEnv,
    id: crate::raw::ids::ProgramInductiveId,
    index: usize,
) -> String {
    let spec = env.program_inductive(id);
    let mut signature = String::new();
    for name in spec.parameters() {
        signature.push_str(&format!("({}: \\VType) -> ", env.symbol(*name)));
    }
    for (name, ty) in spec.constructors()[index].fields() {
        signature.push_str(&format!(
            "({}: {}) -> ",
            env.symbol(*name),
            printing::format_value_type(env, *ty)
        ));
    }
    signature.push_str(&format!(
        "vind({}:{})[{}]",
        printing::format_module(env, id.module),
        id.index,
        spec.parameters()
            .iter()
            .map(|name| env.symbol(*name))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    signature
}
