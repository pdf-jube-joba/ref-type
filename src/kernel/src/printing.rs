//! Human-readable formatting for kernel expressions.

use crate::{
    environment::CrateEnv,
    exp::{Context, ContextEntry, RawExp, RawNode},
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

pub fn format_exp(env: &CrateEnv, exp: RawExp) -> String {
    let arena = env.arena();
    let child = |exp| format_exp(env, exp);
    match arena.get(exp) {
        RawNode::Sort(sort) => format_sort(&sort),
        RawNode::ValueType => "\\Type".to_string(),
        RawNode::Bound(index) => format!("#{index}"),
        RawNode::ModuleParam(var) => format_var(env, var),
        RawNode::ReflectedProgramParam(var) => format!("rf({})", format_var(env, var)),
        RawNode::Meta {
            metavariable,
            spine,
        } => {
            let arguments = spine.into_iter().map(child).collect::<Vec<_>>().join(", ");
            if arguments.is_empty() {
                format!("?m{}", metavariable.0)
            } else {
                format!("?m{}[{}]", metavariable.0, arguments)
            }
        }
        RawNode::Prod { var, ty, body } => {
            format!(
                "({}: {}) -> {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        RawNode::Lam { var, ty, body } => {
            format!(
                "({}: {}) => {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        RawNode::App { func, arg } => format!("({}) ({})", child(func), child(arg)),
        RawNode::DefinedConstant(definition) => {
            format!("def({}:{})", definition.module.0, definition.index)
        }
        RawNode::IndType {
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
        RawNode::IndCtor {
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
        RawNode::IndElim {
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
        RawNode::IndProjection {
            indspec,
            parameters,
            value,
            field,
        } => format!(
            "proj ind({}:{})[{}].{} ({})",
            indspec.module.0,
            indspec.index,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", "),
            field,
            child(value),
        ),
        RawNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => format!(
            "\\case(reflected vind({}:{}), {}) {{{}}}",
            indspec.module.0,
            indspec.index,
            child(scrutinee),
            branches
                .into_iter()
                .enumerate()
                .map(|(idx, branch)| format!("| {idx} => {}", child(branch.body)))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        RawNode::ThunkType { computation_ty } => format!("\\U({})", child(computation_ty)),
        RawNode::ReturnType { value_ty } => format!("\\F({})", child(value_ty)),
        RawNode::ComputationFunction { domain, codomain } => {
            format!("\\CFun({}, {})", child(domain), child(codomain))
        }
        RawNode::RunStep {
            state_ty,
            result_ty,
        } => format!("\\RunStep({}, {})", child(state_ty), child(result_ty)),
        RawNode::ProgramIndType {
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
        RawNode::Thunk { computation } => format!("\\thunk({})", child(computation)),
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => format!(
            "\\continue({}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(next)
        ),
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => format!(
            "\\finish({}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(output)
        ),
        RawNode::ProgramIndCtor {
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
        RawNode::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => format!(
            "vproj pind({}:{})[{}].{} ({})",
            indspec.module.0,
            indspec.index,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", "),
            field,
            child(value),
        ),
        RawNode::Return { value } => format!("\\return({})", child(value)),
        RawNode::Force { value } => format!("\\force({})", child(value)),
        RawNode::ComputationLam {
            var,
            value_ty,
            body,
        } => format!(
            "\\clam({}, {}, {})",
            format_named_var(env, var),
            child(value_ty),
            child(body)
        ),
        RawNode::ComputationApp { computation, value } => {
            format!("\\capp({}, {})", child(computation), child(value))
        }
        RawNode::Sequence {
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
        RawNode::ValueLet { var, value, body } => format!(
            "\\vlet({}, {}, {})",
            format_named_var(env, var),
            child(value),
            child(body)
        ),
        RawNode::ProgramCase {
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
        RawNode::Acc {
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
        RawNode::Proof { proposition } => format!("\\Proof {}", child(proposition)),
        RawNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => format!(
            "\\runStepRec({}, {}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(motive),
            child(on_continue),
            child(on_finish),
            child(scrutinee)
        ),
        RawNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => format!(
            "\\run({}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial)
        ),
        RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => format!(
            "\\runCase({}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial),
            child(transition)
        ),
        RawNode::BoxType { program_ty } => format!("\\Box({})", child(program_ty)),
        RawNode::BoxProgram {
            program_ty,
            program,
        } => format!("\\box({}, {})", child(program_ty), child(program)),
        RawNode::ForceBox { program_ty, boxed } => {
            format!("\\Force({}, {})", child(program_ty), child(boxed))
        }
        RawNode::BoxApp { function, argument } => {
            format!("\\boxapp({}, {})", child(function), child(argument))
        }
        RawNode::RfType { compute_ty } => format!("\\RfType({})", child(compute_ty)),
        RawNode::RfTerm { compute_ty, term } => {
            format!("\\RfTerm({}, {})", child(compute_ty), child(term))
        }
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => format!(
            "\\run({}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial)
        ),
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => format!(
            "\\runCase({}, {}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(initial),
            child(transition)
        ),
        RawNode::AccIntro {
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
        RawNode::AccDescent {
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
        RawNode::SubsetIntro {
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
        RawNode::PowerSet { set } => format!("Pow({})", child(set)),
        RawNode::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_named_var(env, var),
            child(set),
            child(predicate)
        ),
        RawNode::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            child(element),
            child(subset),
            child(superset)
        ),
        RawNode::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", child(superset), child(subset))
        }
        RawNode::Equal { left, right } => format!("{} = {}", child(left), child(right)),
        RawNode::Exists { set } => format!("\\exists {}", child(set)),
        RawNode::TakeSet {
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
        RawNode::TakeProp {
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
        RawNode::ExistsIntro { element, set } => {
            format!("exact({}, {})", child(element), child(set))
        }
        RawNode::SubsetElim {
            element,
            subset,
            superset,
        } => format!(
            "subset_elim({}, {}, {})",
            child(superset),
            child(subset),
            child(element)
        ),
        RawNode::IdRefl { element } => format!("refl({})", child(element)),
        RawNode::IdElim {
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
        RawNode::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => format!(
            "\\axiom:setext({}, {}, {}, {})",
            child(left),
            child(right),
            child(left_to_right),
            child(right_to_left)
        ),
        RawNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => format!(
            "\\axiom:funext({}, {}, {})",
            child(left),
            child(right),
            child(pointwise)
        ),
        RawNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => format!(
            "\\axiom:classicalIndefiniteChoice({}, {}, {})",
            child(domain),
            child(family),
            child(inhabited)
        ),
        RawNode::TakeEq {
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
