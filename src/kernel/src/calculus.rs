use crate::environment::CrateEnv;
use crate::ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId};
use crate::inductive::inductive_type_elim_reduce;
use std::collections::HashMap;

use super::exp::*;

pub fn exp_contains_module_param(env: &CrateEnv, exp: RawExp, parameter: ModuleParamId) -> bool {
    let arena = env.arena();
    match arena.get(exp) {
        RawNode::Sort(_) | RawNode::ValueType | RawNode::Bound(_) => false,
        RawNode::ModuleParam(candidate) | RawNode::ReflectedProgramParam(candidate) => {
            candidate == parameter
        }
        RawNode::Meta { spine, .. } => spine
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::Prod { ty, body, .. } | RawNode::Lam { ty, body, .. } => {
            exp_contains_module_param(env, ty, parameter)
                || exp_contains_module_param(env, body, parameter)
        }
        RawNode::App { func, arg } => {
            exp_contains_module_param(env, func, parameter)
                || exp_contains_module_param(env, arg, parameter)
        }
        RawNode::DefinedConstant(definition) => {
            let definition = env.definition(definition);
            exp_contains_module_param(env, definition.ty, parameter)
                || exp_contains_module_param(env, definition.body, parameter)
        }
        RawNode::IndType { parameters, .. } | RawNode::IndCtor { parameters, .. } => parameters
            .into_iter()
            .any(|argument| exp_contains_module_param(env, argument, parameter)),
        RawNode::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            exp_contains_module_param(env, elim, parameter)
                || exp_contains_module_param(env, return_type, parameter)
                || cases
                    .into_iter()
                    .any(|case| exp_contains_module_param(env, case, parameter))
        }
        RawNode::IndProjection {
            parameters, value, ..
        }
        | RawNode::ProgramIndProjection {
            parameters, value, ..
        } => parameters
            .into_iter()
            .chain([value])
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ThunkType { computation_ty } => {
            exp_contains_module_param(env, computation_ty, parameter)
        }
        RawNode::ReturnType { value_ty }
        | RawNode::Thunk {
            computation: value_ty,
        }
        | RawNode::Return { value: value_ty }
        | RawNode::Force { value: value_ty } => exp_contains_module_param(env, value_ty, parameter),
        RawNode::ComputationFunction { domain, codomain }
        | RawNode::ComputationApp {
            computation: domain,
            value: codomain,
        } => [domain, codomain]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ComputationLam { value_ty, body, .. } => [value_ty, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => [computation, value_ty, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ValueLet { value, body, .. } => [value, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ProgramIndType { parameters, .. } => parameters
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ProgramIndCtor {
            parameters, fields, ..
        } => parameters
            .into_iter()
            .chain(fields)
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ProgramCase {
            scrutinee,
            branches,
            ..
        }
        | RawNode::ReflectedProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            exp_contains_module_param(env, scrutinee, parameter)
                || branches
                    .into_iter()
                    .any(|branch| exp_contains_module_param(env, branch.body, parameter))
        }
        RawNode::RunStep {
            state_ty,
            result_ty,
        }
        | RawNode::RfTerm {
            compute_ty: state_ty,
            term: result_ty,
        } => [state_ty, result_ty]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        }
        | RawNode::Finish {
            state_ty,
            result_ty,
            output: next,
        } => [state_ty, result_ty, next]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => [state_ty, result_ty, step, state]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::Proof { proposition } => exp_contains_module_param(env, proposition, parameter),
        RawNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => [
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        ]
        .into_iter()
        .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::BoxType { program_ty } => exp_contains_module_param(env, program_ty, parameter),
        RawNode::BoxProgram {
            program_ty,
            program,
        } => [program_ty, program]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ForceBox { program_ty, boxed } => [program_ty, boxed]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::BoxApp { function, argument } => [function, argument]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::RfType { compute_ty } => exp_contains_module_param(env, compute_ty, parameter),
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        }
        | RawNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => [state_ty, result_ty, step, initial]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        }
        | RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => [state_ty, result_ty, step, initial, transition]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => [state_ty, result_ty, step, state, predecessors]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => [
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        ]
        .into_iter()
        .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::PowerSet { set } | RawNode::Exists { set } | RawNode::IdRefl { element: set } => {
            exp_contains_module_param(env, set, parameter)
        }
        RawNode::SubSet { set, predicate, .. } => {
            exp_contains_module_param(env, set, parameter)
                || exp_contains_module_param(env, predicate, parameter)
        }
        RawNode::Pred {
            superset,
            subset,
            element,
        }
        | RawNode::SubsetElim {
            superset,
            subset,
            element,
        } => [superset, subset, element]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::TypeLift { superset, subset }
        | RawNode::Equal {
            left: superset,
            right: subset,
        } => {
            exp_contains_module_param(env, superset, parameter)
                || exp_contains_module_param(env, subset, parameter)
        }
        RawNode::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        }
        | RawNode::TakeProp {
            domain: superset,
            proposition: subset,
            map: element,
            existence: proof,
        } => [superset, subset, element, proof]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => [domain, codomain, map, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::ExistsIntro { element, set } => {
            exp_contains_module_param(env, element, parameter)
                || exp_contains_module_param(env, set, parameter)
        }
        RawNode::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => [left, right, ty, predicate, base, equality]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => [left, right, left_to_right, right_to_left]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => [left, right, pointwise]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => [domain, family, inhabited]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        RawNode::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => [func, domain, codomain, element, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
    }
}

pub fn exp_contains_inductive(arena: &Arena, exp: RawExp, inductive: InductiveId) -> bool {
    fn contains(arena: &Arena, exp: RawExp, inductive: InductiveId) -> bool {
        let node = arena.get(exp);
        if matches!(
            node,
            RawNode::IndType { indspec, .. }
                | RawNode::IndCtor { indspec, .. }
                | RawNode::IndElim { indspec, .. }
                if indspec == inductive
        ) {
            return true;
        }
        let mut found = false;
        let _ = map_children(node, |child| {
            found |= contains(arena, child, inductive);
            child
        });
        found
    }

    contains(arena, exp, inductive)
}

#[derive(Clone, Copy)]
struct EqualityMode {
    proof_irrelevant: bool,
    reduce_to_whnf: bool,
    erase_subset_intro: bool,
}

fn is_alpha_eq_rec(env: &CrateEnv, left: RawExp, right: RawExp, mode: EqualityMode) -> bool {
    let arena = env.arena();
    let left = if mode.reduce_to_whnf {
        exp_whnf_with_mode(env, left, mode.erase_subset_intro)
    } else {
        left
    };
    let right = if mode.reduce_to_whnf {
        exp_whnf_with_mode(env, right, mode.erase_subset_intro)
    } else {
        right
    };
    if left == right {
        return true;
    }

    match (arena.get(left), arena.get(right)) {
        (RawNode::Sort(left), RawNode::Sort(right)) => left == right,
        (RawNode::ValueType, RawNode::ValueType) => true,
        (RawNode::Bound(left), RawNode::Bound(right)) => left == right,
        (RawNode::ModuleParam(left), RawNode::ModuleParam(right)) => left == right,
        (RawNode::ReflectedProgramParam(left), RawNode::ReflectedProgramParam(right)) => {
            left == right
        }
        (
            RawNode::Meta {
                metavariable: left_meta,
                spine: left_spine,
            },
            RawNode::Meta {
                metavariable: right_meta,
                spine: right_spine,
            },
        ) => left_meta == right_meta && eq_slices(env, &left_spine, &right_spine, mode),
        (
            RawNode::Prod {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            RawNode::Prod {
                var: right_var,
                ty: right_ty,
                body: right_body,
            },
        )
        | (
            RawNode::Lam {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            RawNode::Lam {
                var: right_var,
                ty: right_ty,
                body: right_body,
            },
        ) => {
            let _ = (left_var, right_var);
            is_alpha_eq_rec(env, left_ty, right_ty, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            RawNode::App {
                func: left_func,
                arg: left_arg,
            },
            RawNode::App {
                func: right_func,
                arg: right_arg,
            },
        ) => {
            is_alpha_eq_rec(env, left_func, right_func, mode)
                && is_alpha_eq_rec(env, left_arg, right_arg, mode)
        }
        (RawNode::DefinedConstant(left), RawNode::DefinedConstant(right)) => left == right,
        (
            RawNode::IndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            RawNode::IndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => left_spec == right_spec && eq_slices(env, &left_parameters, &right_parameters, mode),
        (
            RawNode::IndCtor {
                indspec: left_spec,
                parameters: left_parameters,
                idx: left_idx,
            },
            RawNode::IndCtor {
                indspec: right_spec,
                parameters: right_parameters,
                idx: right_idx,
            },
        ) => {
            left_idx == right_idx
                && left_spec == right_spec
                && eq_slices(env, &left_parameters, &right_parameters, mode)
        }
        (
            RawNode::IndElim {
                indspec: left_spec,
                elim: left_elim,
                return_type: left_return,
                cases: left_cases,
            },
            RawNode::IndElim {
                indspec: right_spec,
                elim: right_elim,
                return_type: right_return,
                cases: right_cases,
            },
        ) => {
            left_spec == right_spec
                && is_alpha_eq_rec(env, left_elim, right_elim, mode)
                && is_alpha_eq_rec(env, left_return, right_return, mode)
                && eq_slices(env, &left_cases, &right_cases, mode)
        }
        (
            RawNode::ThunkType {
                computation_ty: left,
            },
            RawNode::ThunkType {
                computation_ty: right,
            },
        )
        | (RawNode::ReturnType { value_ty: left }, RawNode::ReturnType { value_ty: right })
        | (RawNode::Thunk { computation: left }, RawNode::Thunk { computation: right })
        | (RawNode::Return { value: left }, RawNode::Return { value: right })
        | (RawNode::Force { value: left }, RawNode::Force { value: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            RawNode::ComputationFunction {
                domain: left_domain,
                codomain: left_codomain,
            },
            RawNode::ComputationFunction {
                domain: right_domain,
                codomain: right_codomain,
            },
        )
        | (
            RawNode::ComputationApp {
                computation: left_domain,
                value: left_codomain,
            },
            RawNode::ComputationApp {
                computation: right_domain,
                value: right_codomain,
            },
        ) => eq_slices(
            env,
            &[left_domain, left_codomain],
            &[right_domain, right_codomain],
            mode,
        ),
        (
            RawNode::ProgramIndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            RawNode::ProgramIndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => left_spec == right_spec && eq_slices(env, &left_parameters, &right_parameters, mode),
        (
            RawNode::ProgramIndCtor {
                indspec: left_spec,
                parameters: left_parameters,
                idx: left_idx,
                fields: left_fields,
            },
            RawNode::ProgramIndCtor {
                indspec: right_spec,
                parameters: right_parameters,
                idx: right_idx,
                fields: right_fields,
            },
        ) => {
            left_spec == right_spec
                && left_idx == right_idx
                && eq_slices(env, &left_parameters, &right_parameters, mode)
                && eq_slices(env, &left_fields, &right_fields, mode)
        }
        (
            RawNode::IndProjection {
                indspec: left_spec,
                parameters: left_parameters,
                value: left_value,
                field: left_field,
            },
            RawNode::IndProjection {
                indspec: right_spec,
                parameters: right_parameters,
                value: right_value,
                field: right_field,
            },
        ) => {
            left_spec == right_spec
                && left_field == right_field
                && eq_slices(env, &left_parameters, &right_parameters, mode)
                && is_alpha_eq_rec(env, left_value, right_value, mode)
        }
        (
            RawNode::ProgramIndProjection {
                indspec: left_spec,
                parameters: left_parameters,
                value: left_value,
                field: left_field,
            },
            RawNode::ProgramIndProjection {
                indspec: right_spec,
                parameters: right_parameters,
                value: right_value,
                field: right_field,
            },
        ) => {
            left_spec == right_spec
                && left_field == right_field
                && eq_slices(env, &left_parameters, &right_parameters, mode)
                && is_alpha_eq_rec(env, left_value, right_value, mode)
        }
        (
            RawNode::ComputationLam {
                value_ty: left_ty,
                body: left_body,
                ..
            },
            RawNode::ComputationLam {
                value_ty: right_ty,
                body: right_body,
                ..
            },
        ) => {
            is_alpha_eq_rec(env, left_ty, right_ty, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            RawNode::Sequence {
                computation: left_computation,
                value_ty: left_ty,
                body: left_body,
                ..
            },
            RawNode::Sequence {
                computation: right_computation,
                value_ty: right_ty,
                body: right_body,
                ..
            },
        ) => eq_slices(
            env,
            &[left_computation, left_ty, left_body],
            &[right_computation, right_ty, right_body],
            mode,
        ),
        (
            RawNode::ValueLet {
                value: left_value,
                body: left_body,
                ..
            },
            RawNode::ValueLet {
                value: right_value,
                body: right_body,
                ..
            },
        ) => {
            is_alpha_eq_rec(env, left_value, right_value, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            RawNode::ProgramCase {
                indspec: left_spec,
                scrutinee: left_scrutinee,
                branches: left_branches,
            },
            RawNode::ProgramCase {
                indspec: right_spec,
                scrutinee: right_scrutinee,
                branches: right_branches,
            },
        ) => {
            left_spec == right_spec
                && is_alpha_eq_rec(env, left_scrutinee, right_scrutinee, mode)
                && left_branches.len() == right_branches.len()
                && left_branches
                    .iter()
                    .zip(&right_branches)
                    .all(|(left, right)| {
                        left.binders.len() == right.binders.len()
                            && is_alpha_eq_rec(env, left.body, right.body, mode)
                    })
        }
        (
            RawNode::RunStep {
                state_ty: left_first,
                result_ty: left_second,
            },
            RawNode::RunStep {
                state_ty: right_first,
                result_ty: right_second,
            },
        )
        | (
            RawNode::RfTerm {
                compute_ty: left_first,
                term: left_second,
            },
            RawNode::RfTerm {
                compute_ty: right_first,
                term: right_second,
            },
        ) => {
            is_alpha_eq_rec(env, left_first, right_first, mode)
                && is_alpha_eq_rec(env, left_second, right_second, mode)
        }
        (
            RawNode::Continue {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                next: left_value,
            },
            RawNode::Continue {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                next: right_value,
            },
        )
        | (
            RawNode::Finish {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                output: left_value,
            },
            RawNode::Finish {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                output: right_value,
            },
        ) => eq_slices(
            env,
            &[left_state_ty, left_result_ty, left_value],
            &[right_state_ty, right_result_ty, right_value],
            mode,
        ),
        (
            RawNode::Acc {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                state: left_state,
            },
            RawNode::Acc {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                state: right_state,
            },
        ) => eq_slices(
            env,
            &[left_state_ty, left_result_ty, left_step, left_state],
            &[right_state_ty, right_result_ty, right_step, right_state],
            mode,
        ),
        (RawNode::RfType { compute_ty: left }, RawNode::RfType { compute_ty: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            RawNode::Run {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
            },
            RawNode::Run {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
            },
        ) => eq_slices(
            env,
            &[left_state_ty, left_result_ty, left_step, left_initial],
            &[right_state_ty, right_result_ty, right_step, right_initial],
            mode,
        ),
        (
            RawNode::SetRun {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
            },
            RawNode::SetRun {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
            },
        ) => eq_slices(
            env,
            &[left_state_ty, left_result_ty, left_step, left_initial],
            &[right_state_ty, right_result_ty, right_step, right_initial],
            mode,
        ),
        (
            RawNode::RunCase {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
                transition: left_transition,
            },
            RawNode::RunCase {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
                transition: right_transition,
            },
        ) => eq_slices(
            env,
            &[
                left_state_ty,
                left_result_ty,
                left_step,
                left_initial,
                left_transition,
            ],
            &[
                right_state_ty,
                right_result_ty,
                right_step,
                right_initial,
                right_transition,
            ],
            mode,
        ),
        (
            RawNode::SetRunCase {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
                transition: left_transition,
            },
            RawNode::SetRunCase {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
                transition: right_transition,
            },
        ) => eq_slices(
            env,
            &[
                left_state_ty,
                left_result_ty,
                left_step,
                left_initial,
                left_transition,
            ],
            &[
                right_state_ty,
                right_result_ty,
                right_step,
                right_initial,
                right_transition,
            ],
            mode,
        ),
        (RawNode::Proof { proposition: left }, RawNode::Proof { proposition: right }) => {
            mode.proof_irrelevant || is_alpha_eq_rec(env, left, right, mode)
        }
        (
            RawNode::RunStepRec {
                state_ty: ls,
                result_ty: lr,
                motive: lm,
                on_continue: lc,
                on_finish: lf,
                scrutinee: lx,
            },
            RawNode::RunStepRec {
                state_ty: rs,
                result_ty: rr,
                motive: rm,
                on_continue: rc,
                on_finish: rf,
                scrutinee: rx,
            },
        ) => eq_slices(
            env,
            &[ls, lr, lm, lc, lf, lx],
            &[rs, rr, rm, rc, rf, rx],
            mode,
        ),
        (RawNode::BoxType { program_ty: left }, RawNode::BoxType { program_ty: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            RawNode::BoxProgram {
                program_ty: lt,
                program: lp,
            },
            RawNode::BoxProgram {
                program_ty: rt,
                program: rp,
            },
        ) => eq_slices(env, &[lt, lp], &[rt, rp], mode),
        (
            RawNode::ForceBox {
                program_ty: lt,
                boxed: lb,
            },
            RawNode::ForceBox {
                program_ty: rt,
                boxed: rb,
            },
        ) => eq_slices(env, &[lt, lb], &[rt, rb], mode),
        (
            RawNode::BoxApp {
                function: lf,
                argument: la,
            },
            RawNode::BoxApp {
                function: rf,
                argument: ra,
            },
        ) => eq_slices(env, &[lf, la], &[rf, ra], mode),
        (
            RawNode::ReflectedProgramCase {
                indspec: li,
                scrutinee: ls,
                branches: lb,
            },
            RawNode::ReflectedProgramCase {
                indspec: ri,
                scrutinee: rs,
                branches: rb,
            },
        ) => {
            li == ri
                && is_alpha_eq_rec(env, ls, rs, mode)
                && lb.len() == rb.len()
                && lb.iter().zip(&rb).all(|(left, right)| {
                    left.binders.len() == right.binders.len()
                        && is_alpha_eq_rec(env, left.body, right.body, mode)
                })
        }
        (
            RawNode::AccIntro {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                state: left_state,
                predecessors: left_predecessors,
            },
            RawNode::AccIntro {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                state: right_state,
                predecessors: right_predecessors,
            },
        ) => eq_slices(
            env,
            &[
                left_state_ty,
                left_result_ty,
                left_step,
                left_state,
                left_predecessors,
            ],
            &[
                right_state_ty,
                right_result_ty,
                right_step,
                right_state,
                right_predecessors,
            ],
            mode,
        ),
        (
            RawNode::AccDescent {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                from: left_from,
                to: left_to,
                accessibility: left_accessibility,
                transition: left_transition,
            },
            RawNode::AccDescent {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                from: right_from,
                to: right_to,
                accessibility: right_accessibility,
                transition: right_transition,
            },
        ) => eq_slices(
            env,
            &[
                left_state_ty,
                left_result_ty,
                left_step,
                left_from,
                left_to,
                left_accessibility,
                left_transition,
            ],
            &[
                right_state_ty,
                right_result_ty,
                right_step,
                right_from,
                right_to,
                right_accessibility,
                right_transition,
            ],
            mode,
        ),
        (
            RawNode::SubsetIntro {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
                proof: left_proof,
            },
            RawNode::SubsetIntro {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
                proof: right_proof,
            },
        ) => {
            is_alpha_eq_rec(env, left_superset, right_superset, mode)
                && is_alpha_eq_rec(env, left_subset, right_subset, mode)
                && is_alpha_eq_rec(env, left_element, right_element, mode)
                && (mode.proof_irrelevant || is_alpha_eq_rec(env, left_proof, right_proof, mode))
        }
        (RawNode::PowerSet { set: left }, RawNode::PowerSet { set: right })
        | (RawNode::Exists { set: left }, RawNode::Exists { set: right })
        | (RawNode::IdRefl { element: left }, RawNode::IdRefl { element: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            RawNode::SubSet {
                var: left_var,
                set: left_set,
                predicate: left_predicate,
            },
            RawNode::SubSet {
                var: right_var,
                set: right_set,
                predicate: right_predicate,
            },
        ) => {
            let _ = (left_var, right_var);
            is_alpha_eq_rec(env, left_set, right_set, mode)
                && is_alpha_eq_rec(env, left_predicate, right_predicate, mode)
        }
        (
            RawNode::Pred {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            RawNode::Pred {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
            },
        )
        | (
            RawNode::SubsetElim {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            RawNode::SubsetElim {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
            },
        ) => {
            is_alpha_eq_rec(env, left_superset, right_superset, mode)
                && is_alpha_eq_rec(env, left_subset, right_subset, mode)
                && is_alpha_eq_rec(env, left_element, right_element, mode)
        }
        (
            RawNode::TypeLift {
                superset: left_first,
                subset: left_second,
            },
            RawNode::TypeLift {
                superset: right_first,
                subset: right_second,
            },
        )
        | (
            RawNode::Equal {
                left: left_first,
                right: left_second,
            },
            RawNode::Equal {
                left: right_first,
                right: right_second,
            },
        )
        | (
            RawNode::ExistsIntro {
                element: left_first,
                set: left_second,
            },
            RawNode::ExistsIntro {
                element: right_first,
                set: right_second,
            },
        ) => {
            is_alpha_eq_rec(env, left_first, right_first, mode)
                && is_alpha_eq_rec(env, left_second, right_second, mode)
        }
        (
            RawNode::TakeSet {
                domain: left_domain,
                codomain: left_codomain,
                map: left_map,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            RawNode::TakeSet {
                domain: right_domain,
                codomain: right_codomain,
                map: right_map,
                existence: right_existence,
                uniqueness: right_uniqueness,
            },
        ) => {
            is_alpha_eq_rec(env, left_domain, right_domain, mode)
                && is_alpha_eq_rec(env, left_codomain, right_codomain, mode)
                && is_alpha_eq_rec(env, left_map, right_map, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(env, left_existence, right_existence, mode)
                        && is_alpha_eq_rec(env, left_uniqueness, right_uniqueness, mode)))
        }
        (
            RawNode::TakeProp {
                domain: left_domain,
                proposition: left_proposition,
                map: left_map,
                existence: left_existence,
            },
            RawNode::TakeProp {
                domain: right_domain,
                proposition: right_proposition,
                map: right_map,
                existence: right_existence,
            },
        ) => {
            is_alpha_eq_rec(env, left_proposition, right_proposition, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(env, left_domain, right_domain, mode)
                        && is_alpha_eq_rec(env, left_map, right_map, mode)
                        && is_alpha_eq_rec(env, left_existence, right_existence, mode)))
        }
        (
            RawNode::IdElim {
                left: left_left,
                right: left_right,
                ty: left_ty,
                var: left_var,
                predicate: left_predicate,
                base: left_base,
                equality: left_equality,
                ..
            },
            RawNode::IdElim {
                left: right_left,
                right: right_right,
                ty: right_ty,
                var: right_var,
                predicate: right_predicate,
                base: right_base,
                equality: right_equality,
                ..
            },
        ) => {
            let _ = (left_var, right_var);
            eq_slices(
                env,
                &[
                    left_left,
                    left_right,
                    left_ty,
                    left_predicate,
                    left_base,
                    left_equality,
                ],
                &[
                    right_left,
                    right_right,
                    right_ty,
                    right_predicate,
                    right_base,
                    right_equality,
                ],
                mode,
            )
        }
        (
            RawNode::TakeEq {
                func: left_func,
                domain: left_domain,
                codomain: left_codomain,
                element: left_element,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            RawNode::TakeEq {
                func: right_func,
                domain: right_domain,
                codomain: right_codomain,
                element: right_element,
                existence: right_existence,
                uniqueness: right_uniqueness,
            },
        ) => {
            eq_slices(
                env,
                &[left_func, left_domain, left_codomain, left_element],
                &[right_func, right_domain, right_codomain, right_element],
                mode,
            ) && (mode.proof_irrelevant
                || (is_alpha_eq_rec(env, left_existence, right_existence, mode)
                    && is_alpha_eq_rec(env, left_uniqueness, right_uniqueness, mode)))
        }
        (
            RawNode::AxiomSetExt {
                left: left_left,
                right: left_right,
                left_to_right: left_left_to_right,
                right_to_left: left_right_to_left,
            },
            RawNode::AxiomSetExt {
                left: right_left,
                right: right_right,
                left_to_right: right_left_to_right,
                right_to_left: right_right_to_left,
            },
        ) => eq_slices(
            env,
            &[
                left_left,
                left_right,
                left_left_to_right,
                left_right_to_left,
            ],
            &[
                right_left,
                right_right,
                right_left_to_right,
                right_right_to_left,
            ],
            mode,
        ),
        (
            RawNode::AxiomFunExt {
                left: left_left,
                right: left_right,
                pointwise: left_pointwise,
            },
            RawNode::AxiomFunExt {
                left: right_left,
                right: right_right,
                pointwise: right_pointwise,
            },
        ) => eq_slices(
            env,
            &[left_left, left_right, left_pointwise],
            &[right_left, right_right, right_pointwise],
            mode,
        ),
        (
            RawNode::AxiomClassicalIndefiniteChoice {
                domain: left_domain,
                family: left_family,
                inhabited: left_inhabited,
            },
            RawNode::AxiomClassicalIndefiniteChoice {
                domain: right_domain,
                family: right_family,
                inhabited: right_inhabited,
            },
        ) => eq_slices(
            env,
            &[left_domain, left_family, left_inhabited],
            &[right_domain, right_family, right_inhabited],
            mode,
        ),
        _ => false,
    }
}

fn eq_slices(env: &CrateEnv, left: &[RawExp], right: &[RawExp], mode: EqualityMode) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| is_alpha_eq_rec(env, *left, *right, mode))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: RawExp, right: RawExp) -> bool {
    is_alpha_eq_rec(
        env,
        left,
        right,
        EqualityMode {
            proof_irrelevant: false,
            reduce_to_whnf: false,
            erase_subset_intro: false,
        },
    )
}

fn exp_is_convertible_with_mode(
    env: &CrateEnv,
    left: RawExp,
    right: RawExp,
    erase_proofs: bool,
) -> bool {
    is_alpha_eq_rec(
        env,
        left,
        right,
        EqualityMode {
            proof_irrelevant: erase_proofs,
            reduce_to_whnf: true,
            erase_subset_intro: erase_proofs,
        },
    )
}

fn transform<F>(arena: &Arena, exp: RawExp, depth: usize, operation: &mut F) -> RawExp
where
    F: FnMut(&RawNode, usize) -> Option<RawExp>,
{
    let node = arena.get(exp);
    if let Some(replacement) = operation(&node, depth) {
        return replacement;
    }

    let mut changed = false;
    let mut child = |child: RawExp, child_depth: usize| {
        let transformed = transform(arena, child, child_depth, operation);
        changed |= transformed != child;
        transformed
    };
    let transformed = match node {
        RawNode::Sort(_) | RawNode::Bound(_) | RawNode::ModuleParam(_) => return exp,
        RawNode::Prod { var, ty, body } => RawNode::Prod {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        RawNode::Lam { var, ty, body } => RawNode::Lam {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        RawNode::ComputationLam {
            var,
            value_ty,
            body,
        } => RawNode::ComputationLam {
            var,
            value_ty: child(value_ty, depth),
            body: child(body, depth + 1),
        },
        RawNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => RawNode::Sequence {
            computation: child(computation, depth),
            var,
            value_ty: child(value_ty, depth),
            body: child(body, depth + 1),
        },
        RawNode::ValueLet { var, value, body } => RawNode::ValueLet {
            var,
            value: child(value, depth),
            body: child(body, depth + 1),
        },
        RawNode::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => RawNode::ProgramCase {
            indspec,
            scrutinee: child(scrutinee, depth),
            branches: branches
                .into_iter()
                .map(|branch| ProgramCaseBranch {
                    body: child(branch.body, depth + branch.binders.len()),
                    binders: branch.binders,
                })
                .collect(),
        },
        RawNode::SubSet {
            var,
            set,
            predicate,
        } => RawNode::SubSet {
            var,
            set: child(set, depth),
            predicate: child(predicate, depth + 1),
        },
        RawNode::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => RawNode::IdElim {
            left: child(left, depth),
            right: child(right, depth),
            ty: child(ty, depth),
            var,
            predicate: child(predicate, depth + 1),
            base: child(base, depth),
            equality: child(equality, depth),
        },
        RawNode::DefinedConstant(_) => return exp,
        other => map_children(other, |id| child(id, depth)),
    };
    if changed {
        arena.alloc(transformed)
    } else {
        exp
    }
}

pub fn map_children(mut node: RawNode, mut map: impl FnMut(RawExp) -> RawExp) -> RawNode {
    match &mut node {
        RawNode::Sort(_)
        | RawNode::ValueType
        | RawNode::Bound(_)
        | RawNode::ModuleParam(_)
        | RawNode::ReflectedProgramParam(_) => {}
        RawNode::Meta { spine, .. } => {
            for argument in spine {
                *argument = map(*argument);
            }
        }
        RawNode::Prod { ty, body, .. } | RawNode::Lam { ty, body, .. } => {
            *ty = map(*ty);
            *body = map(*body);
        }
        RawNode::App { func, arg } => {
            *func = map(*func);
            *arg = map(*arg);
        }
        RawNode::DefinedConstant(_) => {}
        RawNode::IndType { parameters, .. } | RawNode::IndCtor { parameters, .. } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
        }
        RawNode::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            *elim = map(*elim);
            *return_type = map(*return_type);
            for case in cases {
                *case = map(*case);
            }
        }
        RawNode::IndProjection {
            parameters, value, ..
        }
        | RawNode::ProgramIndProjection {
            parameters, value, ..
        } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
            *value = map(*value);
        }
        RawNode::ThunkType { computation_ty } => *computation_ty = map(*computation_ty),
        RawNode::ReturnType { value_ty } => *value_ty = map(*value_ty),
        RawNode::ComputationFunction { domain, codomain } => {
            *domain = map(*domain);
            *codomain = map(*codomain);
        }
        RawNode::ProgramIndType { parameters, .. } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
        }
        RawNode::Thunk { computation } => *computation = map(*computation),
        RawNode::RunStep {
            state_ty,
            result_ty,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
        }
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *next = map(*next);
        }
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *output = map(*output);
        }
        RawNode::ProgramIndCtor {
            parameters, fields, ..
        } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
            for field in fields {
                *field = map(*field);
            }
        }
        RawNode::Return { value } | RawNode::Force { value } => *value = map(*value),
        RawNode::ComputationLam { value_ty, body, .. } => {
            *value_ty = map(*value_ty);
            *body = map(*body);
        }
        RawNode::ComputationApp { computation, value } => {
            *computation = map(*computation);
            *value = map(*value);
        }
        RawNode::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => {
            *computation = map(*computation);
            *value_ty = map(*value_ty);
            *body = map(*body);
        }
        RawNode::ValueLet { value, body, .. } => {
            *value = map(*value);
            *body = map(*body);
        }
        RawNode::ProgramCase {
            scrutinee,
            branches,
            ..
        }
        | RawNode::ReflectedProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            *scrutinee = map(*scrutinee);
            for branch in branches {
                branch.body = map(branch.body);
            }
        }
        RawNode::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *state = map(*state);
        }
        RawNode::Proof { proposition } => *proposition = map(*proposition),
        RawNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *motive = map(*motive);
            *on_continue = map(*on_continue);
            *on_finish = map(*on_finish);
            *scrutinee = map(*scrutinee);
        }
        RawNode::BoxType { program_ty } => *program_ty = map(*program_ty),
        RawNode::BoxProgram {
            program_ty,
            program,
        } => {
            *program_ty = map(*program_ty);
            *program = map(*program);
        }
        RawNode::ForceBox { program_ty, boxed } => {
            *program_ty = map(*program_ty);
            *boxed = map(*boxed);
        }
        RawNode::BoxApp { function, argument } => {
            *function = map(*function);
            *argument = map(*argument);
        }
        RawNode::RfType { compute_ty } => *compute_ty = map(*compute_ty),
        RawNode::RfTerm { compute_ty, term } => {
            *compute_ty = map(*compute_ty);
            *term = map(*term);
        }
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        }
        | RawNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *initial = map(*initial);
        }
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        }
        | RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *initial = map(*initial);
            *transition = map(*transition);
        }
        RawNode::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *state = map(*state);
            *predecessors = map(*predecessors);
        }
        RawNode::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *from = map(*from);
            *to = map(*to);
            *accessibility = map(*accessibility);
            *transition = map(*transition);
        }
        RawNode::PowerSet { set } | RawNode::Exists { set } | RawNode::IdRefl { element: set } => {
            *set = map(*set);
        }
        RawNode::SubSet { set, predicate, .. } => {
            *set = map(*set);
            *predicate = map(*predicate);
        }
        RawNode::Pred {
            superset,
            subset,
            element,
        }
        | RawNode::SubsetElim {
            superset,
            subset,
            element,
        } => {
            *superset = map(*superset);
            *subset = map(*subset);
            *element = map(*element);
        }
        RawNode::TypeLift { superset, subset } => {
            *superset = map(*superset);
            *subset = map(*subset);
        }
        RawNode::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            *superset = map(*superset);
            *subset = map(*subset);
            *element = map(*element);
            *proof = map(*proof);
        }
        RawNode::Equal { left, right } => {
            *left = map(*left);
            *right = map(*right);
        }
        RawNode::TakeSet {
            domain,
            codomain,
            map: function,
            existence,
            uniqueness,
        } => {
            *domain = map(*domain);
            *codomain = map(*codomain);
            *function = map(*function);
            *existence = map(*existence);
            *uniqueness = map(*uniqueness);
        }
        RawNode::TakeProp {
            domain,
            proposition,
            map: function,
            existence,
        } => {
            *domain = map(*domain);
            *proposition = map(*proposition);
            *function = map(*function);
            *existence = map(*existence);
        }
        RawNode::ExistsIntro { element, set } => {
            *element = map(*element);
            *set = map(*set);
        }
        RawNode::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => {
            *left = map(*left);
            *right = map(*right);
            *ty = map(*ty);
            *predicate = map(*predicate);
            *base = map(*base);
            *equality = map(*equality);
        }
        RawNode::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => {
            *left = map(*left);
            *right = map(*right);
            *left_to_right = map(*left_to_right);
            *right_to_left = map(*right_to_left);
        }
        RawNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => {
            *left = map(*left);
            *right = map(*right);
            *pointwise = map(*pointwise);
        }
        RawNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            *domain = map(*domain);
            *family = map(*family);
            *inhabited = map(*inhabited);
        }
        RawNode::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            *func = map(*func);
            *domain = map(*domain);
            *codomain = map(*codomain);
            *element = map(*element);
            *existence = map(*existence);
            *uniqueness = map(*uniqueness);
        }
    }
    node
}

/// Rebind references to module-owned entities while materializing a generative
/// module instance. IDs absent from the maps refer outside the source module
/// and remain unchanged.
pub fn remap_global_ids(
    arena: &Arena,
    exp: RawExp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
) -> RawExp {
    remap_all_global_ids(arena, exp, definitions, inductives, &HashMap::new())
}

pub fn remap_all_global_ids(
    arena: &Arena,
    exp: RawExp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> RawExp {
    fn remap(
        arena: &Arena,
        exp: RawExp,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
        program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    ) -> RawExp {
        let node = arena.get(exp);
        match node {
            RawNode::DefinedConstant(id) => definitions
                .get(&id)
                .copied()
                .filter(|mapped| *mapped != id)
                .map(|mapped| arena.alloc(RawNode::DefinedConstant(mapped)))
                .unwrap_or(exp),
            RawNode::IndType {
                indspec,
                parameters,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec && mapped_parameters == parameters {
                    exp
                } else {
                    arena.alloc(RawNode::IndType {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                    })
                }
            }
            RawNode::IndCtor {
                indspec,
                parameters,
                idx,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec && mapped_parameters == parameters {
                    exp
                } else {
                    arena.alloc(RawNode::IndCtor {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        idx,
                    })
                }
            }
            RawNode::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_elim = remap(arena, elim, definitions, inductives, program_inductives);
                let mapped_return = remap(
                    arena,
                    return_type,
                    definitions,
                    inductives,
                    program_inductives,
                );
                let mapped_cases = cases
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec
                    && mapped_elim == elim
                    && mapped_return == return_type
                    && mapped_cases == cases
                {
                    exp
                } else {
                    arena.alloc(RawNode::IndElim {
                        indspec: mapped_spec,
                        elim: mapped_elim,
                        return_type: mapped_return,
                        cases: mapped_cases,
                    })
                }
            }
            RawNode::IndProjection {
                indspec,
                parameters,
                value,
                field,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                let mapped_value = remap(arena, value, definitions, inductives, program_inductives);
                if mapped_spec == indspec
                    && mapped_parameters == parameters
                    && mapped_value == value
                {
                    exp
                } else {
                    arena.alloc(RawNode::IndProjection {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        value: mapped_value,
                        field,
                    })
                }
            }
            RawNode::ProgramIndType {
                indspec,
                parameters,
            } => {
                let mapped_spec = program_inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec && mapped_parameters == parameters {
                    exp
                } else {
                    arena.alloc(RawNode::ProgramIndType {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                    })
                }
            }
            RawNode::ProgramIndCtor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let mapped_spec = program_inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                let mapped_fields = fields
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec
                    && mapped_parameters == parameters
                    && mapped_fields == fields
                {
                    exp
                } else {
                    arena.alloc(RawNode::ProgramIndCtor {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        idx,
                        fields: mapped_fields,
                    })
                }
            }
            RawNode::ProgramIndProjection {
                indspec,
                parameters,
                value,
                field,
            } => {
                let mapped_spec = program_inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives, program_inductives))
                    .collect::<Vec<_>>();
                let mapped_value = remap(arena, value, definitions, inductives, program_inductives);
                if mapped_spec == indspec
                    && mapped_parameters == parameters
                    && mapped_value == value
                {
                    exp
                } else {
                    arena.alloc(RawNode::ProgramIndProjection {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        value: mapped_value,
                        field,
                    })
                }
            }
            RawNode::ProgramCase {
                indspec,
                scrutinee,
                branches,
            } => {
                let mapped_spec = program_inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_scrutinee = remap(
                    arena,
                    scrutinee,
                    definitions,
                    inductives,
                    program_inductives,
                );
                let mapped_branches = branches
                    .iter()
                    .map(|branch| ProgramCaseBranch {
                        binders: branch.binders.clone(),
                        body: remap(
                            arena,
                            branch.body,
                            definitions,
                            inductives,
                            program_inductives,
                        ),
                    })
                    .collect::<Vec<_>>();
                if mapped_spec == indspec
                    && mapped_scrutinee == scrutinee
                    && mapped_branches == branches
                {
                    exp
                } else {
                    arena.alloc(RawNode::ProgramCase {
                        indspec: mapped_spec,
                        scrutinee: mapped_scrutinee,
                        branches: mapped_branches,
                    })
                }
            }
            other => {
                let mut changed = false;
                let mapped = map_children(other, |child| {
                    let result = remap(arena, child, definitions, inductives, program_inductives);
                    changed |= result != child;
                    result
                });
                if changed { arena.alloc(mapped) } else { exp }
            }
        }
    }

    remap(arena, exp, definitions, inductives, program_inductives)
}

pub fn exp_subst_module_param(
    arena: &Arena,
    exp: RawExp,
    parameter: ModuleParamId,
    replacement: RawExp,
) -> RawExp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        RawNode::ModuleParam(candidate) if *candidate == parameter => {
            Some(shift_bound_indices(arena, replacement, depth, 0))
        }
        _ => None,
    })
}

pub fn shift_bound_indices(arena: &Arena, exp: RawExp, amount: usize, cutoff: usize) -> RawExp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        RawNode::Bound(index) if *index >= cutoff + depth => {
            Some(arena.alloc(RawNode::Bound(index + amount)))
        }
        _ => None,
    })
}

/// Replace the outermost locally bound variable in `body` with `argument`.
pub fn instantiate(arena: &Arena, body: RawExp, argument: RawExp) -> RawExp {
    instantiate_at(arena, body, argument, 0)
}

/// Instantiate one binder in the ambient context, leaving `inner` more recent
/// ambient binders in place.
pub fn instantiate_at(arena: &Arena, body: RawExp, argument: RawExp, inner: usize) -> RawExp {
    instantiate_telescope_at(arena, body, std::slice::from_ref(&argument), inner)
}

/// Instantiate an expression whose ambient telescope consists of `arguments`
/// in declaration order. `Bound(0)` denotes the last telescope entry.
pub fn instantiate_telescope(arena: &Arena, exp: RawExp, arguments: &[RawExp]) -> RawExp {
    instantiate_telescope_at(arena, exp, arguments, 0)
}

pub fn instantiate_outer_telescope(
    arena: &Arena,
    exp: RawExp,
    arguments: &[RawExp],
    inner: usize,
) -> RawExp {
    instantiate_telescope_at(arena, exp, arguments, inner)
}

fn instantiate_telescope_at(
    arena: &Arena,
    exp: RawExp,
    arguments: &[RawExp],
    inner: usize,
) -> RawExp {
    if arguments.is_empty() {
        return exp;
    }

    transform(arena, exp, 0, &mut |node, depth| match node {
        RawNode::Bound(index) if *index >= depth + inner => {
            let ambient = *index - depth;
            let telescope_index = ambient - inner;
            if telescope_index < arguments.len() {
                let argument = arguments[arguments.len() - 1 - telescope_index];
                Some(shift_bound_indices(arena, argument, depth + inner, 0))
            } else {
                Some(arena.alloc(RawNode::Bound(index - arguments.len())))
            }
        }
        _ => None,
    })
}

/// Rebase references to an implicit ambient context. `mapping[i]` is the new
/// de Bruijn index for the old ambient index `i`; syntactic binders inside the
/// expression are preserved.
pub fn remap_ambient_indices(arena: &Arena, exp: RawExp, mapping: &[usize]) -> RawExp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        RawNode::Bound(index) if *index >= depth => {
            let ambient = *index - depth;
            mapping
                .get(ambient)
                .filter(|mapped| **mapped != ambient)
                .map(|mapped| arena.alloc(RawNode::Bound(depth + *mapped)))
        }
        _ => None,
    })
}

/// Remove `count` innermost ambient binders from an expression which does not
/// depend on them. References to older ambient entries are rebased.
pub fn remove_unused_ambient_binders(arena: &Arena, exp: RawExp, count: usize) -> Option<RawExp> {
    if count == 0 {
        return Some(exp);
    }
    let mut depends = false;
    let result = transform(arena, exp, 0, &mut |node, depth| match node {
        RawNode::Bound(index) if *index >= depth && *index < depth + count => {
            depends = true;
            None
        }
        RawNode::Bound(index) if *index >= depth + count => {
            Some(arena.alloc(RawNode::Bound(index - count)))
        }
        _ => None,
    });
    (!depends).then_some(result)
}

pub fn exp_contains_bound(arena: &Arena, exp: RawExp, target: usize) -> bool {
    fn contains(arena: &Arena, exp: RawExp, target: usize, depth: usize) -> bool {
        match arena.get(exp) {
            RawNode::Bound(index) => index == target + depth,
            RawNode::Sort(_) | RawNode::ModuleParam(_) | RawNode::DefinedConstant(_) => false,
            RawNode::Prod { ty, body, .. }
            | RawNode::Lam { ty, body, .. }
            | RawNode::SubSet {
                set: ty,
                predicate: body,
                ..
            } => contains(arena, ty, target, depth) || contains(arena, body, target, depth + 1),
            RawNode::IdElim {
                left,
                right,
                ty,
                predicate,
                base,
                equality,
                ..
            } => {
                [left, right, ty, base, equality]
                    .into_iter()
                    .any(|child| contains(arena, child, target, depth))
                    || contains(arena, predicate, target, depth + 1)
            }
            other => {
                let mut found = false;
                let _ = map_children(other, |child| {
                    found |= contains(arena, child, target, depth);
                    child
                });
                found
            }
        }
    }
    contains(arena, exp, target, 0)
}

pub fn exp_subst_map(
    arena: &Arena,
    mut exp: RawExp,
    substitutions: &[(ModuleParamId, RawExp)],
) -> RawExp {
    for (parameter, replacement) in substitutions {
        exp = exp_subst_module_param(arena, exp, *parameter, *replacement);
    }
    exp
}

pub fn erase(env: &CrateEnv, exp: RawExp) -> RawExp {
    let arena = env.arena();
    match arena.get(exp) {
        RawNode::SubsetIntro { element, .. } => erase(env, element),
        RawNode::DefinedConstant(definition) => erase(env, env.definition(definition).body),
        node => {
            let mut changed = false;
            let erased = map_children(node, |child| {
                let result = erase(env, child);
                changed |= result != child;
                result
            });
            if changed { arena.alloc(erased) } else { exp }
        }
    }
}

fn unfold_program_value_head(env: &CrateEnv, mut value: RawExp) -> RawExp {
    loop {
        let RawNode::DefinedConstant(definition) = env.arena().get(value) else {
            return value;
        };
        let definition = env.definition(definition);
        if definition.kind != crate::environment::DefinitionKind::ProgramValue {
            return value;
        }
        value = definition.body;
    }
}

/// Perform one weak call-by-value CBPV computation step.
pub fn reduce_computation_once(env: &CrateEnv, computation: RawExp) -> Option<RawExp> {
    let arena = env.arena();
    match arena.get(computation) {
        RawNode::DefinedConstant(definition) => {
            let definition = env.definition(definition);
            (definition.kind == crate::environment::DefinitionKind::ProgramComputation)
                .then_some(definition.body)
        }
        RawNode::Force { value } => match arena.get(unfold_program_value_head(env, value)) {
            RawNode::Thunk { computation } => Some(computation),
            _ => None,
        },
        RawNode::ComputationApp {
            computation: function,
            value,
        } => {
            if let Some(reduced) = reduce_computation_once(env, function) {
                return Some(arena.alloc(RawNode::ComputationApp {
                    computation: reduced,
                    value,
                }));
            }
            match arena.get(function) {
                RawNode::ComputationLam { body, .. } => Some(instantiate(arena, body, value)),
                _ => None,
            }
        }
        RawNode::Sequence {
            computation: source,
            var,
            value_ty,
            body,
        } => {
            if let Some(reduced) = reduce_computation_once(env, source) {
                return Some(arena.alloc(RawNode::Sequence {
                    computation: reduced,
                    var,
                    value_ty,
                    body,
                }));
            }
            match arena.get(source) {
                RawNode::Return { value } => Some(instantiate(arena, body, value)),
                _ => None,
            }
        }
        RawNode::ValueLet { value, body, .. } => Some(instantiate(arena, body, value)),
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        }
        | RawNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            let forced = arena.alloc(RawNode::Force { value: step });
            let transition = arena.alloc(RawNode::ComputationApp {
                computation: forced,
                value: initial,
            });
            Some(arena.alloc(RawNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            }))
        }
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        }
        | RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            if let Some(reduced) = reduce_computation_once(env, transition) {
                return Some(arena.alloc(RawNode::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition: reduced,
                }));
            }
            let RawNode::Return { value } = arena.get(transition) else {
                return None;
            };
            match arena.get(unfold_program_value_head(env, value)) {
                RawNode::Continue { next, .. } => Some(arena.alloc(RawNode::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial: next,
                })),
                RawNode::Finish { output, .. } => {
                    Some(arena.alloc(RawNode::Return { value: output }))
                }
                _ => None,
            }
        }
        RawNode::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let scrutinee = unfold_program_value_head(env, scrutinee);
            let RawNode::ProgramIndCtor {
                indspec: constructor_spec,
                idx,
                fields,
                ..
            } = arena.get(scrutinee)
            else {
                return None;
            };
            if constructor_spec != indspec {
                return None;
            }
            let branch = branches.get(idx)?;
            (branch.binders.len() == fields.len())
                .then(|| instantiate_telescope(arena, branch.body, &fields))
        }
        _ => None,
    }
}

pub const DEFAULT_REDUCTION_FUEL: usize = 100_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(RawExp),
    OutOfFuel(RawExp),
}

/// Evaluate a CBPV computation to a weak normal form with an explicit step
/// budget.  Ordinary Program typing does not imply termination, so an
/// unbounded evaluator would make the checker/CLI hang on a valid term.
pub fn evaluate_computation_with_fuel(
    env: &CrateEnv,
    computation: RawExp,
    fuel: usize,
) -> Evaluation {
    let mut current = computation;
    for _ in 0..fuel {
        let Some(next) = reduce_computation_once(env, current) else {
            return Evaluation::Normal(current);
        };
        current = next;
    }
    if reduce_computation_once(env, current).is_some() {
        Evaluation::OutOfFuel(current)
    } else {
        Evaluation::Normal(current)
    }
}

pub fn evaluate_computation(env: &CrateEnv, computation: RawExp) -> Evaluation {
    evaluate_computation_with_fuel(env, computation, DEFAULT_REDUCTION_FUEL)
}

pub fn exp_reduce_if_top(env: &CrateEnv, exp: RawExp) -> Option<RawExp> {
    let arena = env.arena();
    match arena.get(exp) {
        RawNode::App { func, arg } => match arena.get(func) {
            RawNode::Lam { body, .. } => Some(instantiate(arena, body, arg)),
            _ => None,
        },
        RawNode::DefinedConstant(definition) => Some(env.definition(definition).body),
        RawNode::Pred {
            subset, element, ..
        } => match arena.get(subset) {
            RawNode::SubSet { predicate, .. } => Some(instantiate(arena, predicate, element)),
            _ => None,
        },
        RawNode::IndElim { .. } => inductive_type_elim_reduce(env, exp).ok(),
        RawNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let reduced = whnf(env, scrutinee);
            let (head, fields) = crate::utils::decompose_app(arena, reduced);
            let RawNode::IndCtor {
                indspec: reflected,
                idx,
                ..
            } = arena.get(head)
            else {
                return (reduced != scrutinee).then(|| {
                    arena.alloc(RawNode::ReflectedProgramCase {
                        indspec,
                        scrutinee: reduced,
                        branches,
                    })
                });
            };
            if reflected != env.program_inductive(indspec).reflected() {
                return None;
            }
            let branch = branches.get(idx)?;
            (branch.binders.len() == fields.len())
                .then(|| instantiate_telescope(arena, branch.body, &fields))
        }
        RawNode::IndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let reduced = whnf(env, value);
            let (head, arguments) = crate::utils::decompose_app(arena, reduced);
            match arena.get(head) {
                RawNode::IndCtor {
                    indspec: constructor,
                    parameters: constructor_parameters,
                    idx: 0,
                } if constructor == indspec
                    && constructor_parameters.len() == parameters.len()
                    && constructor_parameters
                        .iter()
                        .zip(&parameters)
                        .all(|(left, right)| exp_is_alpha_eq(env, *left, *right)) =>
                {
                    arguments.get(field).copied()
                }
                _ if reduced != value => Some(arena.alloc(RawNode::IndProjection {
                    indspec,
                    parameters,
                    value: reduced,
                    field,
                })),
                _ => None,
            }
        }
        RawNode::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let reduced = unfold_program_value_head(env, value);
            match arena.get(reduced) {
                RawNode::ProgramIndCtor {
                    indspec: constructor,
                    parameters: constructor_parameters,
                    idx: 0,
                    fields,
                } if constructor == indspec
                    && constructor_parameters.len() == parameters.len()
                    && constructor_parameters
                        .iter()
                        .zip(&parameters)
                        .all(|(left, right)| exp_is_alpha_eq(env, *left, *right)) =>
                {
                    fields.get(field).copied()
                }
                _ if reduced != value => Some(arena.alloc(RawNode::ProgramIndProjection {
                    indspec,
                    parameters,
                    value: reduced,
                    field,
                })),
                _ => None,
            }
        }
        RawNode::RunStepRec {
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => match arena.get(scrutinee) {
            RawNode::Continue { next, .. } => Some(arena.alloc(RawNode::App {
                func: on_continue,
                arg: next,
            })),
            RawNode::Finish { output, .. } => Some(arena.alloc(RawNode::App {
                func: on_finish,
                arg: output,
            })),
            _ => None,
        },
        RawNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => Some(arena.alloc(RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition: arena.alloc(RawNode::App {
                func: step,
                arg: initial,
            }),
        })),
        RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial: _,
            transition,
        } => match arena.get(transition) {
            RawNode::Continue { next, .. } => Some(arena.alloc(RawNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial: next,
            })),
            RawNode::Finish { output, .. } => Some(output),
            _ => None,
        },
        RawNode::BoxProgram {
            program_ty,
            program,
        } => reduce_computation_once(env, program).map(|program| {
            arena.alloc(RawNode::BoxProgram {
                program_ty,
                program,
            })
        }),
        RawNode::ForceBox { program_ty, boxed } => {
            let RawNode::BoxProgram {
                program_ty: boxed_ty,
                program,
            } = arena.get(boxed)
            else {
                return None;
            };
            if !exp_is_alpha_eq(env, program_ty, boxed_ty)
                || reduce_computation_once(env, program).is_some()
            {
                return None;
            }
            crate::reflection::reflect_term(env, crate::ids::ModuleId(0), &Vec::new(), program).ok()
        }
        RawNode::BoxApp { function, argument } => {
            let RawNode::BoxProgram {
                program_ty: function_ty,
                program: function,
            } = arena.get(function)
            else {
                return None;
            };
            let RawNode::ComputationFunction { codomain, .. } = arena.get(function_ty) else {
                return None;
            };
            let RawNode::BoxProgram {
                program: argument, ..
            } = arena.get(argument)
            else {
                return None;
            };
            Some(arena.alloc(RawNode::BoxProgram {
                program_ty: codomain,
                program: arena.alloc(RawNode::ComputationApp {
                    computation: function,
                    value: argument,
                }),
            }))
        }
        _ => None,
    }
}

fn exp_reduce_head_once_with_cache(
    env: &CrateEnv,
    exp: RawExp,
    erase_subset_intro: bool,
    cache: &mut HashMap<RawExp, RawExp>,
) -> Option<RawExp> {
    let arena = env.arena();
    if erase_subset_intro && let RawNode::SubsetIntro { element, .. } = arena.get(exp) {
        return Some(element);
    }

    // Set/Prop uses ordinary beta reduction.  Weak-head normalization exposes
    // the function and contracts immediately; full normalization below walks
    // every compatible subterm, including neutral arguments.
    match arena.get(exp) {
        RawNode::App { func, arg } => {
            let reduced_func = exp_whnf_with_mode_and_cache(env, func, erase_subset_intro, cache);
            if reduced_func != func {
                return Some(arena.alloc(RawNode::App {
                    func: reduced_func,
                    arg,
                }));
            }
        }
        RawNode::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            let reduced_elim = exp_whnf_with_mode_and_cache(env, elim, erase_subset_intro, cache);
            if reduced_elim != elim {
                return Some(arena.alloc(RawNode::IndElim {
                    indspec,
                    elim: reduced_elim,
                    return_type,
                    cases,
                }));
            }
        }
        RawNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let reduced = exp_whnf_with_mode_and_cache(env, scrutinee, erase_subset_intro, cache);
            if reduced != scrutinee {
                return Some(arena.alloc(RawNode::ReflectedProgramCase {
                    indspec,
                    scrutinee: reduced,
                    branches,
                }));
            }
        }
        RawNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => {
            let reduced = exp_whnf_with_mode_and_cache(env, scrutinee, erase_subset_intro, cache);
            if reduced != scrutinee {
                return Some(arena.alloc(RawNode::RunStepRec {
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
                    scrutinee: reduced,
                }));
            }
        }
        RawNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            let reduced = exp_whnf_with_mode_and_cache(env, transition, erase_subset_intro, cache);
            if reduced != transition {
                return Some(arena.alloc(RawNode::SetRunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition: reduced,
                }));
            }
        }
        RawNode::ForceBox { program_ty, boxed } => {
            let reduced = exp_whnf_with_mode_and_cache(env, boxed, erase_subset_intro, cache);
            if reduced != boxed {
                return Some(arena.alloc(RawNode::ForceBox {
                    program_ty,
                    boxed: reduced,
                }));
            }
        }
        RawNode::BoxApp { function, argument } => {
            let reduced_function =
                exp_whnf_with_mode_and_cache(env, function, erase_subset_intro, cache);
            if reduced_function != function {
                return Some(arena.alloc(RawNode::BoxApp {
                    function: reduced_function,
                    argument,
                }));
            }
            let reduced_argument =
                exp_whnf_with_mode_and_cache(env, argument, erase_subset_intro, cache);
            if reduced_argument != argument {
                return Some(arena.alloc(RawNode::BoxApp {
                    function,
                    argument: reduced_argument,
                }));
            }
        }
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            let reduced_next = exp_whnf_with_mode_and_cache(env, next, erase_subset_intro, cache);
            if reduced_next != next {
                return Some(arena.alloc(RawNode::Continue {
                    state_ty,
                    result_ty,
                    next: reduced_next,
                }));
            }
        }
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            let reduced_output =
                exp_whnf_with_mode_and_cache(env, output, erase_subset_intro, cache);
            if reduced_output != output {
                return Some(arena.alloc(RawNode::Finish {
                    state_ty,
                    result_ty,
                    output: reduced_output,
                }));
            }
        }
        _ => {}
    }

    if let Some(reduced) = exp_reduce_if_top(env, exp) {
        return Some(reduced);
    }

    match arena.get(exp) {
        RawNode::Pred {
            superset,
            subset,
            element,
        } => {
            let reduced_subset =
                exp_whnf_with_mode_and_cache(env, subset, erase_subset_intro, cache);
            (reduced_subset != subset).then(|| {
                arena.alloc(RawNode::Pred {
                    superset,
                    subset: reduced_subset,
                    element,
                })
            })
        }
        _ => None,
    }
}

fn exp_whnf_with_mode_and_cache(
    env: &CrateEnv,
    exp: RawExp,
    erase_subset_intro: bool,
    cache: &mut HashMap<RawExp, RawExp>,
) -> RawExp {
    if let Some(normal) = cache.get(&exp) {
        return *normal;
    }
    let mut current = exp;
    while let Some(next) = exp_reduce_head_once_with_cache(env, current, erase_subset_intro, cache)
    {
        current = next;
    }
    cache.insert(exp, current);
    current
}

fn exp_whnf_with_mode(env: &CrateEnv, exp: RawExp, erase_subset_intro: bool) -> RawExp {
    let mut cache = HashMap::new();
    exp_whnf_with_mode_and_cache(env, exp, erase_subset_intro, &mut cache)
}

pub fn whnf(env: &CrateEnv, exp: RawExp) -> RawExp {
    exp_whnf_with_mode(env, exp, false)
}

pub fn normalize(env: &CrateEnv, exp: RawExp) -> RawExp {
    normalize_with_cache(env, exp, &mut HashMap::new())
}

fn normalize_with_cache(
    env: &CrateEnv,
    exp: RawExp,
    cache: &mut HashMap<RawExp, RawExp>,
) -> RawExp {
    if let Some(normal) = cache.get(&exp) {
        return *normal;
    }
    let arena = env.arena();
    let head = whnf(env, exp);
    let node = arena.get(head);
    if let RawNode::Run {
        state_ty,
        result_ty,
        step,
        initial,
    } = node
    {
        // `normalize` is primarily the Set normalizer, but keeping Program
        // run children structurally normalized preserves the old raw CLI
        // normalization behavior without invoking the Program evaluator.
        let normalized_state_ty = normalize_with_cache(env, state_ty, cache);
        let normalized_result_ty = normalize_with_cache(env, result_ty, cache);
        let normalized_step = normalize_with_cache(env, step, cache);
        let normalized_initial = normalize_with_cache(env, initial, cache);
        let changed = normalized_state_ty != state_ty
            || normalized_result_ty != result_ty
            || normalized_step != step
            || normalized_initial != initial;
        let candidate = if changed {
            arena.alloc(RawNode::Run {
                state_ty: normalized_state_ty,
                result_ty: normalized_result_ty,
                step: normalized_step,
                initial: normalized_initial,
            })
        } else {
            head
        };
        let reduced = whnf(env, candidate);
        let result = if reduced == candidate {
            candidate
        } else {
            normalize_with_cache(env, reduced, cache)
        };
        cache.insert(exp, result);
        return result;
    }
    let mut changed = false;
    let normalized = map_children(node, |child| {
        let result = normalize_with_cache(env, child, cache);
        changed |= result != child;
        result
    });
    let candidate = if changed {
        arena.alloc(normalized)
    } else {
        head
    };
    let reduced = whnf(env, candidate);
    let result = if reduced == candidate {
        candidate
    } else {
        normalize_with_cache(env, reduced, cache)
    };
    cache.insert(exp, result);
    result
}

pub fn reduce_one(env: &CrateEnv, exp: RawExp) -> Option<RawExp> {
    if let Some(reduced) = exp_reduce_head_once_with_cache(env, exp, false, &mut HashMap::new()) {
        return Some(reduced);
    }
    let normalized = normalize(env, exp);
    (normalized != exp).then_some(normalized)
}

pub fn convertible(env: &CrateEnv, left: RawExp, right: RawExp) -> bool {
    exp_is_convertible_with_mode(env, left, right, false)
}

pub fn erased_normal(env: &CrateEnv, exp: RawExp) -> RawExp {
    let erased = erase(env, exp);
    normalize(env, erased)
}

pub fn erased_convertible(env: &CrateEnv, left: RawExp, right: RawExp) -> bool {
    exp_is_convertible_with_mode(env, left, right, true)
}

pub(crate) fn type_head_normal(env: &CrateEnv, ty: RawExp) -> RawExp {
    exp_whnf_with_mode(env, ty, true)
}

pub(crate) fn expose_product(env: &CrateEnv, ty: RawExp) -> Option<(SymbolId, RawExp, RawExp)> {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            RawNode::Prod { var, ty, body } => return Some((var, ty, body)),
            RawNode::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return None,
        }
    }
}

pub(crate) fn base_carrier(env: &CrateEnv, ty: RawExp) -> RawExp {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            RawNode::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return current,
        }
    }
}

pub fn common_ambient_carrier(env: &CrateEnv, left_ty: RawExp, right_ty: RawExp) -> Option<RawExp> {
    let left_carrier = base_carrier(env, left_ty);
    let right_carrier = base_carrier(env, right_ty);
    erased_convertible(env, left_carrier, right_carrier).then_some(left_carrier)
}

pub fn can_weaken_to(env: &CrateEnv, inferred: RawExp, expected: RawExp) -> bool {
    if erased_convertible(env, inferred, expected) {
        return true;
    }
    let arena = env.arena();
    let inferred = type_head_normal(env, inferred);
    let expected = type_head_normal(env, expected);
    match (arena.get(inferred), arena.get(expected)) {
        (RawNode::TypeLift { superset, .. }, _) => can_weaken_to(env, superset, expected),
        (
            RawNode::Prod {
                ty: inferred_domain,
                body: inferred_body,
                ..
            },
            RawNode::Prod {
                ty: expected_domain,
                body: expected_body,
                ..
            },
        ) if erased_convertible(env, inferred_domain, expected_domain) => {
            can_weaken_to(env, inferred_body, expected_body)
        }
        _ => false,
    }
}
