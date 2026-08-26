//! Human-readable formatting for kernel expressions.

use crate::{
    environment::{CrateEnv, DefinedConstant},
    exp::{Context, ContextEntry, Exp, Node},
    ids::{ModuleParamId, SymbolId},
    sort::Sort,
};

fn format_named_var(env: &CrateEnv, var: SymbolId) -> String {
    env.symbol(var).to_string()
}

fn format_var(env: &CrateEnv, var: ModuleParamId) -> String {
    let name = env
        .module(var.module)
        .parameters()
        .get(var.position as usize)
        .map(|parameter| env.symbol(parameter.name))
        .unwrap_or("?");
    format!("{}[{}:{}]", name, var.module.0, var.position)
}

pub fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Prop => "\\Prop".to_string(),
        Sort::PropKind => "\\PropKind".to_string(),
        Sort::Set(level) => format!("\\Set({level})"),
        Sort::SetKind(level) => format!("\\SetKind({level})"),
    }
}

pub fn format_exp(env: &CrateEnv, exp: Exp) -> String {
    let arena = env.arena();
    let child = |exp| format_exp(env, exp);
    match arena.get(exp) {
        Node::Sort(sort) => format_sort(&sort),
        Node::Bound(index) => format!("#{index}"),
        Node::ModuleParam(var) => format_var(env, var),
        Node::Prod { var, ty, body } => {
            format!(
                "({}: {}) -> {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        Node::Lam { var, ty, body } => {
            format!(
                "({}: {}) => {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        Node::App { func, arg } => format!("({}) ({})", child(func), child(arg)),
        Node::DefinedConstant(definition) => format!(
            "def({}:{}){}",
            definition.module.0,
            definition.index,
            format_defined_constant(env, env.definition(definition))
        ),
        Node::IndType {
            indspec,
            parameters,
        } => format!(
            "ind({}:{})[{}]",
            indspec.module.0,
            indspec.index,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Node::IndCtor {
            indspec,
            parameters,
            idx,
        } => format!(
            "ind({}:{}).{}[{}]",
            indspec.module.0,
            indspec.index,
            idx,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => format!(
            "elim {} \\in ind({}:{}) \\return {} with {{{}}}",
            child(elim),
            indspec.module.0,
            indspec.index,
            child(return_type),
            cases.into_iter().map(child).collect::<Vec<_>>().join(", ")
        ),
        Node::ThunkType { computation_ty } => format!("\\U({})", child(computation_ty)),
        Node::ReturnType { value_ty } => format!("\\F({})", child(value_ty)),
        Node::ComputationFunction { domain, codomain } => {
            format!("\\CFun({}, {})", child(domain), child(codomain))
        }
        Node::RunStep {
            state_ty,
            result_ty,
        } => format!("\\RunStep({}, {})", child(state_ty), child(result_ty)),
        Node::ProgramIndType {
            indspec,
            parameters,
        } => format!(
            "vind({}:{})[{}]",
            indspec.module.0,
            indspec.index,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Node::Thunk { computation } => format!("\\thunk({})", child(computation)),
        Node::Continue {
            state_ty,
            result_ty,
            next,
        } => format!(
            "\\continue({}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(next)
        ),
        Node::Finish {
            state_ty,
            result_ty,
            output,
        } => format!(
            "\\finish({}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(output)
        ),
        Node::ProgramIndCtor {
            indspec,
            parameters,
            idx,
            fields,
        } => format!(
            "vind({}:{}).{}[{}]({})",
            indspec.module.0,
            indspec.index,
            idx,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", "),
            fields.into_iter().map(child).collect::<Vec<_>>().join(", ")
        ),
        Node::Return { value } => format!("\\return({})", child(value)),
        Node::Force { value } => format!("\\force({})", child(value)),
        Node::ComputationLam {
            var,
            value_ty,
            body,
        } => format!(
            "\\clam({}, {}, {})",
            format_named_var(env, var),
            child(value_ty),
            child(body)
        ),
        Node::ComputationApp { computation, value } => {
            format!("\\capp({}, {})", child(computation), child(value))
        }
        Node::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => format!(
            "\\sequence({}, {}, {}, {})",
            child(computation),
            format_named_var(env, var),
            child(value_ty),
            child(body)
        ),
        Node::ValueLet { var, value, body } => format!(
            "\\vlet({}, {}, {})",
            format_named_var(env, var),
            child(value),
            child(body)
        ),
        Node::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => format!(
            "\\vcase(vind({}:{}), {}) {{{}}}",
            indspec.module.0,
            indspec.index,
            child(scrutinee),
            branches
                .into_iter()
                .enumerate()
                .map(|(idx, branch)| format!(
                    "| {idx}({}) => {}",
                    branch
                        .binders
                        .into_iter()
                        .map(|binder| format_named_var(env, binder))
                        .collect::<Vec<_>>()
                        .join(", "),
                    child(branch.body)
                ))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Node::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => format!(
            "\\Acc({}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(state)
        ),
        Node::RfType { compute_ty } => format!("\\RfType({})", child(compute_ty)),
        Node::RfTerm { compute_ty, term } => {
            format!("\\RfTerm({}, {})", child(compute_ty), child(term))
        }
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            termination,
        } => format!(
            "\\run({}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial),
            child(termination)
        ),
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        } => format!(
            "\\runCase({}, {}, {}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial),
            child(transition),
            child(termination),
            child(invariant)
        ),
        Node::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => format!(
            "\\accintro({}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(state),
            child(predecessors)
        ),
        Node::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => format!(
            "\\accdescent({}, {}, {}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(from),
            child(to),
            child(accessibility),
            child(transition)
        ),
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => format!(
            "subset_intro({}, {}, {}, {})",
            child(superset),
            child(subset),
            child(element),
            child(proof)
        ),
        Node::PowerSet { set } => format!("Pow({})", child(set)),
        Node::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_named_var(env, var),
            child(set),
            child(predicate)
        ),
        Node::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            child(element),
            child(subset),
            child(superset)
        ),
        Node::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", child(superset), child(subset))
        }
        Node::Equal { left, right } => format!("{} = {}", child(left), child(right)),
        Node::Exists { set } => format!("\\exists {}", child(set)),
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => format!(
            "\\Take({}, {}, {}) by ({}, {})",
            child(domain),
            child(codomain),
            child(map),
            child(existence),
            child(uniqueness)
        ),
        Node::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => format!(
            "\\TakeProp({}, {}, {}) by ({})",
            child(domain),
            child(proposition),
            child(map),
            child(existence)
        ),
        Node::ExistsIntro { element, set } => {
            format!("exact({}, {})", child(element), child(set))
        }
        Node::SubsetElim {
            element,
            subset,
            superset,
        } => format!(
            "subset_elim({}, {}, {})",
            child(superset),
            child(subset),
            child(element)
        ),
        Node::IdRefl { element } => format!("refl({})", child(element)),
        Node::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => format!(
            "\\idelim({} = {} \\with {}: {} => {}) \\by ({}, {})",
            child(left),
            child(right),
            format_named_var(env, var),
            child(ty),
            child(predicate),
            child(base),
            child(equality)
        ),
        Node::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => format!(
            "\\takeelim({}, {}, {}, {}) \\by ({}, {})",
            child(func),
            child(element),
            child(domain),
            child(codomain),
            child(existence),
            child(uniqueness)
        ),
    }
}

pub fn format_ctx(env: &CrateEnv, ctx: &Context) -> String {
    ctx.iter()
        .map(|entry| match entry {
            ContextEntry::Pts { var, ty } => {
                format!("{}: {}", env.symbol(*var), format_exp(env, *ty))
            }
            ContextEntry::ProgramType { var } => format!("{}: vtype", env.symbol(*var)),
            ContextEntry::ProgramValue { var, ty } => {
                format!("{}: {}: value", env.symbol(*var), format_exp(env, *ty))
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_defined_constant(env: &CrateEnv, definition: &DefinedConstant) -> String {
    format!(
        "[: {} := {}]",
        format_exp(env, definition.ty),
        format_exp(env, definition.body)
    )
}
