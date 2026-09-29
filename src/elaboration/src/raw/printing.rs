//! Human-readable formatting for kernel expressions.
#[cfg(test)]
use crate::raw::program::ProgramTerm;

use crate::raw::{
    environment::CrateEnv,
    exp::{Axiom, Exp, ExpContext, ExpNode, Prove},
    ids::{ModuleParamId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode, ValueTerm,
        ValueTermNode, ValueType, ValueTypeNode,
    },
    sort::Sort,
};

pub fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Prop => "\\Prop".to_string(),
        Sort::PropKind => "\\PropKind".to_string(),
        Sort::Set(level) => format!("\\Set({level})"),
        Sort::SetKind(level) => format!("\\SetKind({level})"),
    }
}

pub struct Printer<'a> {
    env: &'a CrateEnv,
    meta_name: Option<&'a dyn Fn(crate::raw::ids::MetaVarId) -> String>,
}
impl<'a> Printer<'a> {
    pub fn new(
        env: &'a CrateEnv,
        meta_name: &'a dyn Fn(crate::raw::ids::MetaVarId) -> String,
    ) -> Self {
        Self {
            env,
            meta_name: Some(meta_name),
        }
    }
    fn debug(env: &'a CrateEnv) -> Self {
        Self {
            env,
            meta_name: None,
        }
    }
    fn format_meta(&self, id: crate::raw::ids::MetaVarId, category: &str) -> String {
        self.meta_name
            .map_or_else(|| format!("?{category}{}", id.0), |name| name(id))
    }
    fn format_named_var(&self, var: SymbolId) -> String {
        let env = self.env;
        env.symbol(var).to_string()
    }

    fn format_var(&self, var: ModuleParamId) -> String {
        let env = self.env;
        let name = env
            .module(var.module)
            .parameters()
            .get(var.position as usize)
            .map(|parameter| env.symbol(parameter.name))
            .unwrap_or("?");
        format!(
            "{}[{}:{}]",
            name,
            self.format_module(var.module),
            var.position
        )
    }

    fn format_app_operand(&self, exp: Exp) -> String {
        let env = self.env;
        let formatted = self.format_exp(exp);
        match env.arena().get(exp) {
            ExpNode::Sort(_)
            | ExpNode::Bound(_)
            | ExpNode::ModuleParam(_)
            | ExpNode::ReflectedProgramParam(_)
            | ExpNode::Meta { .. }
            | ExpNode::DefinedConstant(_) => formatted,
            _ => format!("({formatted})"),
        }
    }

    pub fn format_exp(&self, exp: Exp) -> String {
        let env = self.env;
        let arena = env.arena();
        let child = |exp| self.format_exp(exp);
        match arena.get(exp) {
            ExpNode::Sort(sort) => format_sort(&sort),
            ExpNode::Bound(index) => format!("#{index}"),
            ExpNode::ModuleParam(var) => self.format_var(var),
            ExpNode::ReflectedProgramParam(var) => format!("rf({})", self.format_var(var)),
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                let arguments = spine.into_iter().map(child).collect::<Vec<_>>().join(", ");
                if arguments.is_empty() {
                    self.format_meta(metavariable, "m")
                } else {
                    format!("{}[{}]", self.format_meta(metavariable, "m"), arguments)
                }
            }
            ExpNode::Prod { var, ty, body } => {
                format!(
                    "({}: {}) -> {}",
                    self.format_named_var(var),
                    child(ty),
                    child(body)
                )
            }
            ExpNode::Lam { var, ty, body } => {
                format!(
                    "({}: {}) => {}",
                    self.format_named_var(var),
                    child(ty),
                    child(body)
                )
            }
            ExpNode::App { func, arg } => {
                format!(
                    "{} {}",
                    self.format_app_operand(func),
                    self.format_app_operand(arg)
                )
            }
            ExpNode::DefinedConstant(definition) => definition_name(env, definition),
            ExpNode::IndType {
                indspec,
                parameters,
            } => with_parameters(
                inductive_name(env, indspec, None),
                parameters.into_iter().map(child).collect(),
            ),
            ExpNode::IndCtor {
                indspec,
                parameters,
                idx,
            } => with_constructor_parameters(
                inductive_name(env, indspec, None),
                inductive_name(env, indspec, Some(idx)),
                parameters.into_iter().map(child).collect(),
            ),
            ExpNode::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => format!(
                "elim {} \\in ind({}:{}) \\return {} with {{{}}}",
                child(elim),
                self.format_module(indspec.module),
                indspec.index,
                child(return_type),
                cases.into_iter().map(child).collect::<Vec<_>>().join(", ")
            ),
            ExpNode::IndCase {
                indspec,
                scrutinee,
                return_type,
                branches,
            } => format!(
                "case {} \\in ind({}:{}) \\return {} with {{{}}}",
                child(scrutinee),
                self.format_module(indspec.module),
                indspec.index,
                child(return_type),
                branches
                    .into_iter()
                    .map(child)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee,
                branches,
            } => format!(
                "\\match(reflected vind({}:{}), {}) {{{}}}",
                self.format_module(indspec.module),
                indspec.index,
                child(scrutinee),
                branches
                    .into_iter()
                    .enumerate()
                    .map(|(idx, branch)| format!("| {idx} => {}", child(branch.body)))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => format!("\\RunStep[{}, {}]", child(state_ty), child(result_ty)),
            ExpNode::Continue {
                state_ty,
                result_ty,
                next,
            } => format!(
                "\\continue[{}, {}]({})",
                child(state_ty),
                child(result_ty),
                child(next)
            ),
            ExpNode::Finish {
                state_ty,
                result_ty,
                output,
            } => format!(
                "\\finish[{}, {}]({})",
                child(state_ty),
                child(result_ty),
                child(output)
            ),
            ExpNode::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => format!(
                "\\Acc[{}, {}]({}, {})",
                child(state_ty),
                child(result_ty),
                child(step),
                child(state)
            ),
            ExpNode::SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => format!(
                "stepMatchSet[{}, {}]({}, {}, {})",
                child(state_ty),
                child(result_ty),
                child(motive),
                child(on_continue),
                child(on_finish)
            ),
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => format!(
                "\\run[{}, {}]({}, {}) \\by {{ {} }}",
                child(state_ty),
                child(result_ty),
                child(step),
                child(initial),
                child(accessibility)
            ),
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => format!(
                "\\runCase[{}, {}]({}, {}, {}) \\by {{ accessibility: {}, equality: {} }}",
                child(state_ty),
                child(result_ty),
                child(step),
                child(initial),
                child(transition),
                child(accessibility),
                child(transition_equality)
            ),
            ExpNode::BoxType { program_ty } => {
                format!("\\Box[{}]", self.format_computation_type(program_ty))
            }
            ExpNode::BoxProgram {
                program_ty,
                program,
            } => format!(
                "\\box[{}]({})",
                self.format_computation_type(program_ty),
                self.format_computation(program)
            ),
            ExpNode::ForceBox { program_ty, boxed } => {
                format!(
                    "\\squash[{}]({})",
                    self.format_computation_type(program_ty),
                    child(boxed)
                )
            }
            ExpNode::BoxApp { function, argument } => {
                format!("\\boxapp({}, {})", child(function), child(argument))
            }
            ExpNode::Prove(Prove::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            }) => format!(
                "\\accintro[{}, {}]({}, {}, {})",
                child(state_ty),
                child(result_ty),
                child(step),
                child(state),
                child(predecessors)
            ),
            ExpNode::Prove(Prove::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            }) => format!(
                "\\accdescent[{}, {}]({}, {}, {}, {}, {})",
                child(state_ty),
                child(result_ty),
                child(step),
                child(from),
                child(to),
                child(accessibility),
                child(transition)
            ),
            ExpNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => format!(
                "\\into[{}]({}, {}) \\by {{ {} }}",
                child(superset),
                child(element),
                child(subset),
                child(proof)
            ),
            ExpNode::PowerSet { set } => format!("\\Pow {}", child(set)),
            ExpNode::SubSet {
                var,
                set,
                predicate,
            } => format!(
                "{{ {} : {} \\where {} }}",
                self.format_named_var(var),
                child(set),
                child(predicate)
            ),
            ExpNode::Pred {
                superset,
                subset,
                element,
            } => format!(
                "\\In[{}] ({}) ({})",
                child(superset),
                child(subset),
                child(element)
            ),
            ExpNode::TypeLift { superset, subset } => {
                format!("\\Cast[{}] ({})", child(superset), child(subset))
            }
            ExpNode::Equal { left, right } => format!("{} = {}", child(left), child(right)),
            ExpNode::Exists { set } => format!("\\exists {}", child(set)),
            ExpNode::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => format!(
                "\\Take({}, {}, {}) \\by {{ existence: {}, uniqueness: {} }}",
                child(domain),
                child(codomain),
                child(map),
                child(existence),
                child(uniqueness)
            ),
            ExpNode::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => format!(
                "\\TakeProp({}, {}, {}) \\by {{ {} }}",
                child(domain),
                child(proposition),
                child(map),
                child(existence)
            ),
            ExpNode::Prove(Prove::ExistsIntro { element, set }) => {
                format!("exact({}, {})", child(element), child(set))
            }
            ExpNode::Prove(Prove::SubsetElim {
                element,
                subset,
                superset,
            }) => format!(
                "subset_elim({}, {}, {})",
                child(superset),
                child(subset),
                child(element)
            ),
            ExpNode::Prove(Prove::IdRefl { element }) => format!("refl({})", child(element)),
            ExpNode::Prove(Prove::IdElim {
                left,
                right,
                ty,
                var,
                predicate,
                base,
                equality,
            }) => format!(
                "\\idelim {} = {} \\with {}: {} => {} \\by {{ base: {}, equality: {} }}",
                child(left),
                child(right),
                self.format_named_var(var),
                child(ty),
                child(predicate),
                child(base),
                child(equality)
            ),
            ExpNode::Prove(Prove::Axiom(Axiom::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            })) => format!(
                "\\axiom:setext({}, {}, {}, {})",
                child(left),
                child(right),
                child(left_to_right),
                child(right_to_left)
            ),
            ExpNode::Prove(Prove::Axiom(Axiom::FunExt {
                left,
                right,
                pointwise,
            })) => format!(
                "\\axiom:funext({}, {}, {})",
                child(left),
                child(right),
                child(pointwise)
            ),
            ExpNode::Prove(Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            })) => format!(
                "\\axiom:classicalIndefiniteChoice({}, {}, {})",
                child(domain),
                child(family),
                child(inhabited)
            ),
            ExpNode::Prove(Prove::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            }) => format!(
                "\\takeelim({}, {}, {}, {}) \\by {{ existence: {}, uniqueness: {} }}",
                child(func),
                child(element),
                child(domain),
                child(codomain),
                child(existence),
                child(uniqueness)
            ),
        }
    }

    pub fn format_ctx(&self, ctx: &ExpContext) -> String {
        let env = self.env;
        ctx.iter()
            .map(|entry| format!("{}: {}", env.symbol(entry.var), self.format_exp(entry.ty)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    pub fn format_value_type(&self, ty: ValueType) -> String {
        let env = self.env;
        let arena = env.arena();
        match arena.get(ty) {
            ValueTypeNode::Bound(index) => format!("#T{index}"),
            ValueTypeNode::ModuleParam(id) => self.format_var(id),
            ValueTypeNode::Meta { metavariable, .. } => self.format_meta(metavariable, "vt"),
            ValueTypeNode::Thunk { computation_ty } => {
                format!("\\U({})", self.format_computation_type(computation_ty))
            }
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => format!(
                "\\RunStep[{}, {}]",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty)
            ),
            ValueTypeNode::Inductive {
                indspec,
                parameters,
            } => with_parameters(
                datatype_name(env, indspec, None),
                parameters
                    .into_iter()
                    .map(|ty| self.format_value_type(ty))
                    .collect(),
            ),
        }
    }

    pub fn format_computation_type(&self, ty: ComputationType) -> String {
        let env = self.env;
        match env.arena().get(ty) {
            ComputationTypeNode::Meta { metavariable, .. } => self.format_meta(metavariable, "ct"),
            ComputationTypeNode::Return { value_ty } => {
                format!("\\F({})", self.format_value_type(value_ty))
            }
            ComputationTypeNode::Function { domain, codomain } => format!(
                "{} => {}",
                self.format_value_type(domain),
                self.format_computation_type(codomain)
            ),
        }
    }

    #[cfg(test)]
    pub fn format_program(&self, program: ProgramTerm) -> String {
        match program {
            ProgramTerm::ValueTerm(value) => self.format_value(value),
            ProgramTerm::ComputationTerm(term) => self.format_computation(term),
        }
    }

    pub fn format_value(&self, value: ValueTerm) -> String {
        let env = self.env;
        match env.arena().get(value) {
            ValueTermNode::Bound(index) => format!("#v{index}"),
            ValueTermNode::ModuleParam(id) => self.format_var(id),
            ValueTermNode::Meta { metavariable, .. } => self.format_meta(metavariable, "v"),
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => with_parameters(
                definition_name(env, definition),
                parameters
                    .into_iter()
                    .map(|ty| self.format_value_type(ty))
                    .collect(),
            ),
            ValueTermNode::DefinedConstant(id) => definition_name(env, id),
            ValueTermNode::Thunk { computation } => {
                format!("\\thunk({})", self.format_computation(computation))
            }
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => format!(
                "\\continue[{}, {}]({})",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty),
                self.format_value(next)
            ),
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => format!(
                "\\finish[{}, {}]({})",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty),
                self.format_value(output)
            ),
            ValueTermNode::InductiveConstructor {
                indspec,
                idx,
                fields,
                parameters,
            } => {
                let name = with_constructor_parameters(
                    datatype_name(env, indspec, None),
                    datatype_name(env, indspec, Some(idx)),
                    parameters
                        .into_iter()
                        .map(|ty| self.format_value_type(ty))
                        .collect(),
                );
                if fields.is_empty() {
                    name
                } else {
                    format!(
                        "{name}({})",
                        fields
                            .into_iter()
                            .map(|v| self.format_value(v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
        }
    }

    pub fn format_computation(&self, term: ComputationTerm) -> String {
        let env = self.env;
        match env.arena().get(term) {
            ComputationTermNode::Meta { metavariable, .. } => self.format_meta(metavariable, "c"),
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => with_parameters(
                definition_name(env, definition),
                parameters
                    .into_iter()
                    .map(|ty| self.format_value_type(ty))
                    .collect(),
            ),
            ComputationTermNode::DefinedConstant(id) => definition_name(env, id),
            ComputationTermNode::Return { value } => {
                format!("\\return({})", self.format_value(value))
            }
            ComputationTermNode::Force { value } => {
                format!("\\force({})", self.format_value(value))
            }
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => format!(
                "({}: {}) =>c {}",
                env.symbol(var),
                self.format_value_type(value_ty),
                self.format_computation(body)
            ),
            ComputationTermNode::Application { computation, value } => format!(
                "({}) @c ({})",
                self.format_computation(computation),
                self.format_value(value)
            ),
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => format!(
                "{} to {}: {} in {}",
                self.format_computation(computation),
                env.symbol(var),
                self.format_value_type(value_ty),
                self.format_computation(body)
            ),
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => format!(
                "letv {}: {} = {} in {}",
                env.symbol(var),
                self.format_value_type(value_ty),
                self.format_value(value),
                self.format_computation(body)
            ),
            ComputationTermNode::Case {
                indspec, scrutinee, ..
            } => format!(
                "case vind({}:{}) {}",
                self.format_module(indspec.module),
                indspec.index,
                self.format_value(scrutinee)
            ),
            ComputationTermNode::StepMatch {
                state_ty,
                result_ty,
                computation_ty,
                scrutinee,
                ..
            } => format!(
                "stepRec[{}, {}]({}) : {}",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty),
                self.format_value(scrutinee),
                self.format_computation_type(computation_ty)
            ),
            ComputationTermNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => format!(
                "\\run[{}, {}]({}, {}) \\by {{ {} }}",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty),
                self.format_value(step),
                self.format_value(initial),
                self.format_exp(accessibility)
            ),
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => format!(
                "\\runCase[{}, {}]({}, {}, {}) \\by {{ accessibility: {}, equality: {} }}",
                self.format_value_type(state_ty),
                self.format_value_type(result_ty),
                self.format_value(step),
                self.format_value(initial),
                self.format_computation(transition),
                self.format_exp(accessibility),
                self.format_exp(transition_equality)
            ),
        }
    }

    /// Names in semantic output remain stable when unrelated modules are omitted
    /// from an incremental checking batch.
    pub fn format_module(&self, module: crate::raw::ids::ModuleId) -> String {
        let env = self.env;
        if env.namespace_binding_id(module).is_some() {
            let binding = env.binding(module);
            let source = self.format_module(binding.source);
            if binding.arguments.is_empty() {
                return source;
            }
            let arguments = binding
                .arguments
                .iter()
                .map(|(parameter, argument)| {
                    let name = env
                        .module(parameter.module)
                        .parameters()
                        .get(parameter.position as usize)
                        .map(|parameter| env.symbol(parameter.name))
                        .unwrap_or("?");
                    let value = match argument {
                        crate::raw::environment::ModuleArgument::Pts(term) => {
                            self.format_exp(*term)
                        }
                        crate::raw::environment::ModuleArgument::ProgramType(ty) => {
                            self.format_value_type(*ty)
                        }
                        crate::raw::environment::ModuleArgument::ProgramValue(value) => {
                            self.format_value(*value)
                        }
                    };
                    format!("{name} := {value}")
                })
                .collect::<Vec<_>>()
                .join(", ");
            return format!("{source}[{arguments}]");
        }
        let current = env.module(module);
        match current.parent() {
            Some(parent) => format!(
                "{}.{}",
                self.format_module(parent),
                module_component(env, module)
            ),
            None => "root".into(),
        }
    }
}
pub(crate) fn module_component(env: &CrateEnv, module: crate::raw::ids::ModuleId) -> String {
    let current = env.module(module);
    let preceding = current.parent().map_or(0, |parent| {
        env.module(parent)
            .children()
            .iter()
            .filter(|&&child| child.0 < module.0 && env.module(child).name() == current.name())
            .count()
    });
    if preceding == 0 {
        current.name().to_owned()
    } else {
        format!("{}#{}", current.name(), preceding + 1)
    }
}

pub(crate) fn definition_name(env: &CrateEnv, id: crate::raw::ids::DefId) -> String {
    use crate::raw::environment::ModuleItem;
    for item in env.module(id.module).items() {
        let associated = match item {
            ModuleItem::Definition { name, definition } => {
                if *definition == id {
                    return format!("\\{}.{}", format_module(env, id.module), name);
                }
                continue;
            }
            ModuleItem::Inductive {
                associated_definitions,
                ..
            }
            | ModuleItem::Record {
                associated_definitions,
                ..
            }
            | ModuleItem::ProgramInductive {
                associated_definitions,
                ..
            } => associated_definitions,
        };
        for (name, definition) in associated {
            if *definition == id {
                return format!(
                    "\\{}.{}::{name}",
                    format_module(env, id.module),
                    item.name()
                );
            }
        }
    }
    format!("def({}:{})", format_module(env, id.module), id.index)
}

pub(crate) fn inductive_name(
    env: &CrateEnv,
    id: crate::raw::ids::InductiveId,
    constructor: Option<usize>,
) -> String {
    use crate::raw::environment::ModuleItem;
    for item in env.module(id.module).items() {
        let (constructors, reflected) = match item {
            ModuleItem::Inductive {
                inductive,
                constructor_names,
                ..
            } if *inductive == id => (constructor_names.as_slice(), false),
            ModuleItem::Record { inductive, .. } if *inductive == id => (&[][..], false),
            ModuleItem::ProgramInductive {
                reflected,
                constructor_names,
                ..
            } if *reflected == id => (constructor_names.as_slice(), true),
            _ => continue,
        };
        let reflection = if reflected { "^" } else { "" };
        let mut name = format!(
            "\\{}.{}{reflection}",
            format_module(env, id.module),
            item.name()
        );
        if let Some(index) = constructor {
            let ctor = constructors
                .get(index)
                .cloned()
                .unwrap_or_else(|| format!("constructor#{index}"));
            name.push_str(&format!("::{ctor}"));
        }
        return name;
    }
    let name = format!("ind({}:{})", format_module(env, id.module), id.index);
    constructor.map_or(name.clone(), |i| format!("{name}.{i}"))
}

pub(crate) fn datatype_name(
    env: &CrateEnv,
    id: crate::raw::ids::ProgramInductiveId,
    constructor: Option<usize>,
) -> String {
    use crate::raw::environment::ModuleItem;
    for item in env.module(id.module).items() {
        if let ModuleItem::ProgramInductive {
            inductive,
            constructor_names,
            ..
        } = item
            && *inductive == id
        {
            let mut name = format!("\\{}.{}", format_module(env, id.module), item.name());
            if let Some(index) = constructor {
                let ctor = constructor_names
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| format!("constructor#{index}"));
                name.push_str(&format!("::{ctor}"));
            }
            return name;
        }
    }
    let name = format!("vind({}:{})", format_module(env, id.module), id.index);
    constructor.map_or(name.clone(), |i| format!("{name}.{i}"))
}

fn with_parameters(name: String, parameters: Vec<String>) -> String {
    if parameters.is_empty() {
        name
    } else {
        format!("{name}[{}]", parameters.join(", "))
    }
}

fn with_constructor_parameters(
    owner: String,
    constructor: String,
    parameters: Vec<String>,
) -> String {
    let suffix = &constructor[owner.len()..];
    format!("{}{suffix}", with_parameters(owner, parameters))
}

pub fn format_exp(env: &CrateEnv, value: Exp) -> String {
    Printer::debug(env).format_exp(value)
}
pub fn format_value_type(env: &CrateEnv, value: ValueType) -> String {
    Printer::debug(env).format_value_type(value)
}
pub fn format_computation_type(env: &CrateEnv, value: ComputationType) -> String {
    Printer::debug(env).format_computation_type(value)
}
pub fn format_computation(env: &CrateEnv, value: ComputationTerm) -> String {
    Printer::debug(env).format_computation(value)
}
pub fn format_module(env: &CrateEnv, value: crate::raw::ids::ModuleId) -> String {
    Printer::debug(env).format_module(value)
}
#[cfg(test)]
pub fn format_program(env: &CrateEnv, value: ProgramTerm) -> String {
    Printer::debug(env).format_program(value)
}
