//! Human-readable formatting for kernel expressions.

use crate::{
    environment::CrateEnv,
    exp::{Exp, ExpContext, ExpNode},
    ids::{ModuleParamId, SymbolId},
    program::{
        Computation, ComputationNode, ComputationType, ComputationTypeNode, Program,
        ProgramContext, ProgramContextEntry, ProgramType, Value, ValueNode, ValueType,
        ValueTypeNode,
    },
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
        ExpNode::Sort(sort) => format_sort(&sort),
        ExpNode::Bound(index) => format!("#{index}"),
        ExpNode::ModuleParam(var) => format_var(env, var),
        ExpNode::ReflectedProgramParam(var) => format!("rf({})", format_var(env, var)),
        ExpNode::Meta {
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
        ExpNode::Prod { var, ty, body } => {
            format!(
                "({}: {}) -> {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        ExpNode::Lam { var, ty, body } => {
            format!(
                "({}: {}) => {}",
                format_named_var(env, var),
                child(ty),
                child(body)
            )
        }
        ExpNode::App { func, arg } => format!("({}) ({})", child(func), child(arg)),
        ExpNode::DefinedConstant(definition) => {
            format!("def({}:{})", definition.module.0, definition.index)
        }
        ExpNode::IndType {
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
        ExpNode::IndCtor {
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
        ExpNode::IndElim {
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
        ExpNode::IndProjection {
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
        ExpNode::ReflectedProgramCase {
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
        ExpNode::RunStep {
            state_ty,
            result_ty,
        } => format!("\\RunStep({}, {})", child(state_ty), child(result_ty)),
        ExpNode::Continue {
            state_ty,
            result_ty,
            next,
        } => format!(
            "\\continue({}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(next)
        ),
        ExpNode::Finish {
            state_ty,
            result_ty,
            output,
        } => format!(
            "\\finish({}, {}, {})",
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
            "\\Acc({}, {}, {}, {})",
            child(state_ty),
            child(result_ty),
            child(step),
            child(state)
        ),
        ExpNode::Proof { proposition } => format!("\\Proof {}", child(proposition)),
        ExpNode::RunStepRec {
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
        ExpNode::SetRun {
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
        ExpNode::SetRunCase {
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
        ExpNode::BoxType { program_ty } => {
            format!("\\Box({})", format_program_type(env, program_ty))
        }
        ExpNode::BoxProgram {
            program_ty,
            program,
        } => format!(
            "\\box({}, {})",
            format_program_type(env, program_ty),
            format_program(env, program)
        ),
        ExpNode::ForceBox { program_ty, boxed } => {
            format!(
                "\\Force({}, {})",
                format_program_type(env, program_ty),
                child(boxed)
            )
        }
        ExpNode::BoxApp { function, argument } => {
            format!("\\boxapp({}, {})", child(function), child(argument))
        }
        ExpNode::RfType { program_ty } => {
            format!("\\RfType({})", format_program_type(env, program_ty))
        }
        ExpNode::RfTerm {
            program_ty,
            program,
        } => {
            format!(
                "\\RfTerm({}, {})",
                format_program_type(env, program_ty),
                format_program(env, program)
            )
        }
        ExpNode::AccIntro {
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
        ExpNode::AccDescent {
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
        ExpNode::SubsetIntro {
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
        ExpNode::PowerSet { set } => format!("Pow({})", child(set)),
        ExpNode::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_named_var(env, var),
            child(set),
            child(predicate)
        ),
        ExpNode::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            child(element),
            child(subset),
            child(superset)
        ),
        ExpNode::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", child(superset), child(subset))
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
            "\\Take({}, {}, {}) by ({}, {})",
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
            "\\TakeProp({}, {}, {}) by ({})",
            child(domain),
            child(proposition),
            child(map),
            child(existence)
        ),
        ExpNode::ExistsIntro { element, set } => {
            format!("exact({}, {})", child(element), child(set))
        }
        ExpNode::SubsetElim {
            element,
            subset,
            superset,
        } => format!(
            "subset_elim({}, {}, {})",
            child(superset),
            child(subset),
            child(element)
        ),
        ExpNode::IdRefl { element } => format!("refl({})", child(element)),
        ExpNode::IdElim {
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
        ExpNode::AxiomSetExt {
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
        ExpNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => format!(
            "\\axiom:funext({}, {}, {})",
            child(left),
            child(right),
            child(pointwise)
        ),
        ExpNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => format!(
            "\\axiom:classicalIndefiniteChoice({}, {}, {})",
            child(domain),
            child(family),
            child(inhabited)
        ),
        ExpNode::TakeEq {
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

pub fn format_ctx(env: &CrateEnv, ctx: &ExpContext) -> String {
    ctx.iter()
        .map(|entry| format!("{}: {}", env.symbol(entry.var), format_exp(env, entry.ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn format_program_type(env: &CrateEnv, ty: ProgramType) -> String {
    match ty {
        ProgramType::Value(ty) => format_value_type(env, ty),
        ProgramType::Computation(ty) => format_computation_type(env, ty),
    }
}

pub fn format_value_type(env: &CrateEnv, ty: ValueType) -> String {
    let arena = env.arena();
    match arena.get(ty) {
        ValueTypeNode::Bound(index) => format!("#T{index}"),
        ValueTypeNode::ModuleParam(id) => format_var(env, id),
        ValueTypeNode::Meta { metavariable, .. } => format!("?vt{}", metavariable.0),
        ValueTypeNode::Thunk { computation_ty } => {
            format!("\\U({})", format_computation_type(env, computation_ty))
        }
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => format!(
            "\\PRunStep({}, {})",
            format_value_type(env, state_ty),
            format_value_type(env, result_ty)
        ),
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => format!(
            "vind({}:{})[{}]",
            indspec.module.0,
            indspec.index,
            parameters
                .into_iter()
                .map(|p| format_value_type(env, p))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub fn format_computation_type(env: &CrateEnv, ty: ComputationType) -> String {
    match env.arena().get(ty) {
        ComputationTypeNode::Meta { metavariable, .. } => format!("?ct{}", metavariable.0),
        ComputationTypeNode::Return { value_ty } => {
            format!("\\F({})", format_value_type(env, value_ty))
        }
        ComputationTypeNode::Function { domain, codomain } => format!(
            "{} => {}",
            format_value_type(env, domain),
            format_computation_type(env, codomain)
        ),
    }
}

pub fn format_program(env: &CrateEnv, program: Program) -> String {
    match program {
        Program::Value(value) => format_value(env, value),
        Program::Computation(term) => format_computation(env, term),
    }
}

pub fn format_value(env: &CrateEnv, value: Value) -> String {
    match env.arena().get(value) {
        ValueNode::Bound(index) => format!("#v{index}"),
        ValueNode::ModuleParam(id) => format_var(env, id),
        ValueNode::Meta { metavariable, .. } => format!("?v{}", metavariable.0),
        ValueNode::DefinedConstant(id) => format!("vdef({}:{})", id.module.0, id.index),
        ValueNode::Thunk { computation } => {
            format!("\\thunk({})", format_computation(env, computation))
        }
        ValueNode::Continue {
            state_ty,
            result_ty,
            next,
        } => format!(
            "\\Pcontinue({}, {}, {})",
            format_value_type(env, state_ty),
            format_value_type(env, result_ty),
            format_value(env, next)
        ),
        ValueNode::Finish {
            state_ty,
            result_ty,
            output,
        } => format!(
            "\\Pfinish({}, {}, {})",
            format_value_type(env, state_ty),
            format_value_type(env, result_ty),
            format_value(env, output)
        ),
        ValueNode::InductiveConstructor {
            indspec,
            idx,
            fields,
            ..
        } => format!(
            "vind({}:{}).{}({})",
            indspec.module.0,
            indspec.index,
            idx,
            fields
                .into_iter()
                .map(|v| format_value(env, v))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ValueNode::InductiveProjection {
            indspec,
            value,
            field,
            ..
        } => format!(
            "vproj({}:{}).{}({})",
            indspec.module.0,
            indspec.index,
            field,
            format_value(env, value)
        ),
    }
}

pub fn format_computation(env: &CrateEnv, term: Computation) -> String {
    match env.arena().get(term) {
        ComputationNode::Meta { metavariable, .. } => format!("?c{}", metavariable.0),
        ComputationNode::DefinedConstant(id) => format!("cdef({}:{})", id.module.0, id.index),
        ComputationNode::Return { value } => format!("\\return({})", format_value(env, value)),
        ComputationNode::Force { value } => format!("\\force({})", format_value(env, value)),
        ComputationNode::Lambda {
            var,
            value_ty,
            body,
        } => format!(
            "({}: {}) =>c {}",
            env.symbol(var),
            format_value_type(env, value_ty),
            format_computation(env, body)
        ),
        ComputationNode::Application { computation, value } => format!(
            "({}) @c ({})",
            format_computation(env, computation),
            format_value(env, value)
        ),
        ComputationNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => format!(
            "{} to {}: {} in {}",
            format_computation(env, computation),
            env.symbol(var),
            format_value_type(env, value_ty),
            format_computation(env, body)
        ),
        ComputationNode::ValueLet { var, value, body } => format!(
            "letv {} = {} in {}",
            env.symbol(var),
            format_value(env, value),
            format_computation(env, body)
        ),
        ComputationNode::Case {
            indspec, scrutinee, ..
        } => format!(
            "case vind({}:{}) {}",
            indspec.module.0,
            indspec.index,
            format_value(env, scrutinee)
        ),
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => format!(
            "\\Prun({}, {}, {}, {})",
            format_value_type(env, state_ty),
            format_value_type(env, result_ty),
            format_value(env, step),
            format_value(env, initial)
        ),
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => format!(
            "\\PrunCase({}, {}, {}, {}, {})",
            format_value_type(env, state_ty),
            format_value_type(env, result_ty),
            format_value(env, step),
            format_value(env, initial),
            format_computation(env, transition)
        ),
    }
}

pub fn format_program_ctx(env: &CrateEnv, context: &ProgramContext) -> String {
    context
        .iter()
        .map(|entry| match entry {
            ProgramContextEntry::Type { var } => format!("{}: vtype", env.symbol(*var)),
            ProgramContextEntry::Value { var, ty } => {
                format!("{}: {}", env.symbol(*var), format_value_type(env, *ty))
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}
