use crate::environment::CrateEnv;
use crate::ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId};
use crate::inductive::inductive_type_elim_reduce;
use std::collections::HashMap;

use super::exp::*;

pub fn exp_contains_module_param(env: &CrateEnv, exp: Exp, parameter: ModuleParamId) -> bool {
    let arena = env.arena();
    match arena.get(exp) {
        Node::Sort(_) | Node::ValueType | Node::Bound(_) => false,
        Node::ModuleParam(candidate) => candidate == parameter,
        Node::Meta { spine, .. } => spine
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            exp_contains_module_param(env, ty, parameter)
                || exp_contains_module_param(env, body, parameter)
        }
        Node::App { func, arg } => {
            exp_contains_module_param(env, func, parameter)
                || exp_contains_module_param(env, arg, parameter)
        }
        Node::DefinedConstant(definition) => {
            let definition = env.definition(definition);
            exp_contains_module_param(env, definition.ty, parameter)
                || exp_contains_module_param(env, definition.body, parameter)
        }
        Node::IndType { parameters, .. } | Node::IndCtor { parameters, .. } => parameters
            .into_iter()
            .any(|argument| exp_contains_module_param(env, argument, parameter)),
        Node::IndElim {
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
        Node::IndProjection {
            parameters, value, ..
        }
        | Node::ProgramIndProjection {
            parameters, value, ..
        } => parameters
            .into_iter()
            .chain([value])
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ThunkType { computation_ty } => {
            exp_contains_module_param(env, computation_ty, parameter)
        }
        Node::ReturnType { value_ty }
        | Node::Thunk {
            computation: value_ty,
        }
        | Node::Return { value: value_ty }
        | Node::Force { value: value_ty } => exp_contains_module_param(env, value_ty, parameter),
        Node::ComputationFunction { domain, codomain }
        | Node::ComputationApp {
            computation: domain,
            value: codomain,
        } => [domain, codomain]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ComputationLam { value_ty, body, .. } => [value_ty, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => [computation, value_ty, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ValueLet { value, body, .. } => [value, body]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ProgramIndType { parameters, .. } => parameters
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ProgramIndCtor {
            parameters, fields, ..
        } => parameters
            .into_iter()
            .chain(fields)
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            exp_contains_module_param(env, scrutinee, parameter)
                || branches
                    .into_iter()
                    .any(|branch| exp_contains_module_param(env, branch.body, parameter))
        }
        Node::RunStep {
            state_ty,
            result_ty,
        }
        | Node::RfTerm {
            compute_ty: state_ty,
            term: result_ty,
        } => [state_ty, result_ty]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::Continue {
            state_ty,
            result_ty,
            next,
        }
        | Node::Finish {
            state_ty,
            result_ty,
            output: next,
        } => [state_ty, result_ty, next]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => [state_ty, result_ty, step, state]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::RfType { compute_ty } => exp_contains_module_param(env, compute_ty, parameter),
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            termination,
        } => [state_ty, result_ty, step, initial, termination]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        } => [
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        ]
        .into_iter()
        .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => [state_ty, result_ty, step, state, predecessors]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::AccDescent {
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
        Node::PowerSet { set } | Node::Exists { set } | Node::IdRefl { element: set } => {
            exp_contains_module_param(env, set, parameter)
        }
        Node::SubSet { set, predicate, .. } => {
            exp_contains_module_param(env, set, parameter)
                || exp_contains_module_param(env, predicate, parameter)
        }
        Node::Pred {
            superset,
            subset,
            element,
        }
        | Node::SubsetElim {
            superset,
            subset,
            element,
        } => [superset, subset, element]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TypeLift { superset, subset }
        | Node::Equal {
            left: superset,
            right: subset,
        } => {
            exp_contains_module_param(env, superset, parameter)
                || exp_contains_module_param(env, subset, parameter)
        }
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        }
        | Node::TakeProp {
            domain: superset,
            proposition: subset,
            map: element,
            existence: proof,
        } => [superset, subset, element, proof]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => [domain, codomain, map, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ExistsIntro { element, set } => {
            exp_contains_module_param(env, element, parameter)
                || exp_contains_module_param(env, set, parameter)
        }
        Node::IdElim {
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
        Node::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => [left, right, left_to_right, right_to_left]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::AxiomFunExt {
            left,
            right,
            pointwise,
        } => [left, right, pointwise]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => [domain, family, inhabited]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TakeEq {
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

pub fn exp_contains_inductive(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
    fn contains(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
        let node = arena.get(exp);
        if matches!(
            node,
            Node::IndType { indspec, .. }
                | Node::IndCtor { indspec, .. }
                | Node::IndElim { indspec, .. }
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

fn is_alpha_eq_rec(env: &CrateEnv, left: Exp, right: Exp, mode: EqualityMode) -> bool {
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
        (Node::Sort(left), Node::Sort(right)) => left == right,
        (Node::ValueType, Node::ValueType) => true,
        (Node::Bound(left), Node::Bound(right)) => left == right,
        (Node::ModuleParam(left), Node::ModuleParam(right)) => left == right,
        (
            Node::Meta {
                metavariable: left_meta,
                spine: left_spine,
            },
            Node::Meta {
                metavariable: right_meta,
                spine: right_spine,
            },
        ) => left_meta == right_meta && eq_slices(env, &left_spine, &right_spine, mode),
        (
            Node::Prod {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            Node::Prod {
                var: right_var,
                ty: right_ty,
                body: right_body,
            },
        )
        | (
            Node::Lam {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            Node::Lam {
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
            Node::App {
                func: left_func,
                arg: left_arg,
            },
            Node::App {
                func: right_func,
                arg: right_arg,
            },
        ) => {
            is_alpha_eq_rec(env, left_func, right_func, mode)
                && is_alpha_eq_rec(env, left_arg, right_arg, mode)
        }
        (Node::DefinedConstant(left), Node::DefinedConstant(right)) => left == right,
        (
            Node::IndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            Node::IndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => left_spec == right_spec && eq_slices(env, &left_parameters, &right_parameters, mode),
        (
            Node::IndCtor {
                indspec: left_spec,
                parameters: left_parameters,
                idx: left_idx,
            },
            Node::IndCtor {
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
            Node::IndElim {
                indspec: left_spec,
                elim: left_elim,
                return_type: left_return,
                cases: left_cases,
            },
            Node::IndElim {
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
            Node::ThunkType {
                computation_ty: left,
            },
            Node::ThunkType {
                computation_ty: right,
            },
        )
        | (Node::ReturnType { value_ty: left }, Node::ReturnType { value_ty: right })
        | (Node::Thunk { computation: left }, Node::Thunk { computation: right })
        | (Node::Return { value: left }, Node::Return { value: right })
        | (Node::Force { value: left }, Node::Force { value: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            Node::ComputationFunction {
                domain: left_domain,
                codomain: left_codomain,
            },
            Node::ComputationFunction {
                domain: right_domain,
                codomain: right_codomain,
            },
        )
        | (
            Node::ComputationApp {
                computation: left_domain,
                value: left_codomain,
            },
            Node::ComputationApp {
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
            Node::ProgramIndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            Node::ProgramIndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => left_spec == right_spec && eq_slices(env, &left_parameters, &right_parameters, mode),
        (
            Node::ProgramIndCtor {
                indspec: left_spec,
                parameters: left_parameters,
                idx: left_idx,
                fields: left_fields,
            },
            Node::ProgramIndCtor {
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
            Node::IndProjection {
                indspec: left_spec,
                parameters: left_parameters,
                value: left_value,
                field: left_field,
            },
            Node::IndProjection {
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
            Node::ProgramIndProjection {
                indspec: left_spec,
                parameters: left_parameters,
                value: left_value,
                field: left_field,
            },
            Node::ProgramIndProjection {
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
            Node::ComputationLam {
                value_ty: left_ty,
                body: left_body,
                ..
            },
            Node::ComputationLam {
                value_ty: right_ty,
                body: right_body,
                ..
            },
        ) => {
            is_alpha_eq_rec(env, left_ty, right_ty, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            Node::Sequence {
                computation: left_computation,
                value_ty: left_ty,
                body: left_body,
                ..
            },
            Node::Sequence {
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
            Node::ValueLet {
                value: left_value,
                body: left_body,
                ..
            },
            Node::ValueLet {
                value: right_value,
                body: right_body,
                ..
            },
        ) => {
            is_alpha_eq_rec(env, left_value, right_value, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            Node::ProgramCase {
                indspec: left_spec,
                scrutinee: left_scrutinee,
                branches: left_branches,
            },
            Node::ProgramCase {
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
            Node::RunStep {
                state_ty: left_first,
                result_ty: left_second,
            },
            Node::RunStep {
                state_ty: right_first,
                result_ty: right_second,
            },
        )
        | (
            Node::RfTerm {
                compute_ty: left_first,
                term: left_second,
            },
            Node::RfTerm {
                compute_ty: right_first,
                term: right_second,
            },
        ) => {
            is_alpha_eq_rec(env, left_first, right_first, mode)
                && is_alpha_eq_rec(env, left_second, right_second, mode)
        }
        (
            Node::Continue {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                next: left_value,
            },
            Node::Continue {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                next: right_value,
            },
        )
        | (
            Node::Finish {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                output: left_value,
            },
            Node::Finish {
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
            Node::Acc {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                state: left_state,
            },
            Node::Acc {
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
        (Node::RfType { compute_ty: left }, Node::RfType { compute_ty: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            Node::Run {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
                termination: left_termination,
            },
            Node::Run {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
                termination: right_termination,
            },
        ) => {
            eq_slices(
                env,
                &[left_state_ty, left_result_ty, left_step, left_initial],
                &[right_state_ty, right_result_ty, right_step, right_initial],
                mode,
            ) && (mode.proof_irrelevant
                || is_alpha_eq_rec(env, left_termination, right_termination, mode))
        }
        (
            Node::RunCase {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                initial: left_initial,
                transition: left_transition,
                termination: left_termination,
                invariant: left_invariant,
            },
            Node::RunCase {
                state_ty: right_state_ty,
                result_ty: right_result_ty,
                step: right_step,
                initial: right_initial,
                transition: right_transition,
                termination: right_termination,
                invariant: right_invariant,
            },
        ) => {
            eq_slices(
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
            ) && (mode.proof_irrelevant
                || (is_alpha_eq_rec(env, left_termination, right_termination, mode)
                    && is_alpha_eq_rec(env, left_invariant, right_invariant, mode)))
        }
        (
            Node::AccIntro {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                state: left_state,
                predecessors: left_predecessors,
            },
            Node::AccIntro {
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
            Node::AccDescent {
                state_ty: left_state_ty,
                result_ty: left_result_ty,
                step: left_step,
                from: left_from,
                to: left_to,
                accessibility: left_accessibility,
                transition: left_transition,
            },
            Node::AccDescent {
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
            Node::SubsetIntro {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
                proof: left_proof,
            },
            Node::SubsetIntro {
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
        (Node::PowerSet { set: left }, Node::PowerSet { set: right })
        | (Node::Exists { set: left }, Node::Exists { set: right })
        | (Node::IdRefl { element: left }, Node::IdRefl { element: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            Node::SubSet {
                var: left_var,
                set: left_set,
                predicate: left_predicate,
            },
            Node::SubSet {
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
            Node::Pred {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            Node::Pred {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
            },
        )
        | (
            Node::SubsetElim {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            Node::SubsetElim {
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
            Node::TypeLift {
                superset: left_first,
                subset: left_second,
            },
            Node::TypeLift {
                superset: right_first,
                subset: right_second,
            },
        )
        | (
            Node::Equal {
                left: left_first,
                right: left_second,
            },
            Node::Equal {
                left: right_first,
                right: right_second,
            },
        )
        | (
            Node::ExistsIntro {
                element: left_first,
                set: left_second,
            },
            Node::ExistsIntro {
                element: right_first,
                set: right_second,
            },
        ) => {
            is_alpha_eq_rec(env, left_first, right_first, mode)
                && is_alpha_eq_rec(env, left_second, right_second, mode)
        }
        (
            Node::TakeSet {
                domain: left_domain,
                codomain: left_codomain,
                map: left_map,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            Node::TakeSet {
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
            Node::TakeProp {
                domain: left_domain,
                proposition: left_proposition,
                map: left_map,
                existence: left_existence,
            },
            Node::TakeProp {
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
            Node::IdElim {
                left: left_left,
                right: left_right,
                ty: left_ty,
                var: left_var,
                predicate: left_predicate,
                base: left_base,
                equality: left_equality,
                ..
            },
            Node::IdElim {
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
            Node::TakeEq {
                func: left_func,
                domain: left_domain,
                codomain: left_codomain,
                element: left_element,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            Node::TakeEq {
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
            Node::AxiomSetExt {
                left: left_left,
                right: left_right,
                left_to_right: left_left_to_right,
                right_to_left: left_right_to_left,
            },
            Node::AxiomSetExt {
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
            Node::AxiomFunExt {
                left: left_left,
                right: left_right,
                pointwise: left_pointwise,
            },
            Node::AxiomFunExt {
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
            Node::AxiomClassicalIndefiniteChoice {
                domain: left_domain,
                family: left_family,
                inhabited: left_inhabited,
            },
            Node::AxiomClassicalIndefiniteChoice {
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

fn eq_slices(env: &CrateEnv, left: &[Exp], right: &[Exp], mode: EqualityMode) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| is_alpha_eq_rec(env, *left, *right, mode))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
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

fn exp_is_convertible_with_mode(env: &CrateEnv, left: Exp, right: Exp, erase_proofs: bool) -> bool {
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

fn transform<F>(arena: &Arena, exp: Exp, depth: usize, operation: &mut F) -> Exp
where
    F: FnMut(&Node, usize) -> Option<Exp>,
{
    let node = arena.get(exp);
    if let Some(replacement) = operation(&node, depth) {
        return replacement;
    }

    let mut changed = false;
    let mut child = |child: Exp, child_depth: usize| {
        let transformed = transform(arena, child, child_depth, operation);
        changed |= transformed != child;
        transformed
    };
    let transformed = match node {
        Node::Sort(_) | Node::Bound(_) | Node::ModuleParam(_) => return exp,
        Node::Prod { var, ty, body } => Node::Prod {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        Node::Lam { var, ty, body } => Node::Lam {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        Node::ComputationLam {
            var,
            value_ty,
            body,
        } => Node::ComputationLam {
            var,
            value_ty: child(value_ty, depth),
            body: child(body, depth + 1),
        },
        Node::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => Node::Sequence {
            computation: child(computation, depth),
            var,
            value_ty: child(value_ty, depth),
            body: child(body, depth + 1),
        },
        Node::ValueLet { var, value, body } => Node::ValueLet {
            var,
            value: child(value, depth),
            body: child(body, depth + 1),
        },
        Node::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => Node::ProgramCase {
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
        Node::SubSet {
            var,
            set,
            predicate,
        } => Node::SubSet {
            var,
            set: child(set, depth),
            predicate: child(predicate, depth + 1),
        },
        Node::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => Node::IdElim {
            left: child(left, depth),
            right: child(right, depth),
            ty: child(ty, depth),
            var,
            predicate: child(predicate, depth + 1),
            base: child(base, depth),
            equality: child(equality, depth),
        },
        Node::DefinedConstant(_) => return exp,
        other => map_children(other, |id| child(id, depth)),
    };
    if changed {
        arena.alloc(transformed)
    } else {
        exp
    }
}

pub fn map_children(mut node: Node, mut map: impl FnMut(Exp) -> Exp) -> Node {
    match &mut node {
        Node::Sort(_) | Node::ValueType | Node::Bound(_) | Node::ModuleParam(_) => {}
        Node::Meta { spine, .. } => {
            for argument in spine {
                *argument = map(*argument);
            }
        }
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            *ty = map(*ty);
            *body = map(*body);
        }
        Node::App { func, arg } => {
            *func = map(*func);
            *arg = map(*arg);
        }
        Node::DefinedConstant(_) => {}
        Node::IndType { parameters, .. } | Node::IndCtor { parameters, .. } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
        }
        Node::IndElim {
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
        Node::IndProjection {
            parameters, value, ..
        }
        | Node::ProgramIndProjection {
            parameters, value, ..
        } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
            *value = map(*value);
        }
        Node::ThunkType { computation_ty } => *computation_ty = map(*computation_ty),
        Node::ReturnType { value_ty } => *value_ty = map(*value_ty),
        Node::ComputationFunction { domain, codomain } => {
            *domain = map(*domain);
            *codomain = map(*codomain);
        }
        Node::ProgramIndType { parameters, .. } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
        }
        Node::Thunk { computation } => *computation = map(*computation),
        Node::RunStep {
            state_ty,
            result_ty,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
        }
        Node::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *next = map(*next);
        }
        Node::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *output = map(*output);
        }
        Node::ProgramIndCtor {
            parameters, fields, ..
        } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
            for field in fields {
                *field = map(*field);
            }
        }
        Node::Return { value } | Node::Force { value } => *value = map(*value),
        Node::ComputationLam { value_ty, body, .. } => {
            *value_ty = map(*value_ty);
            *body = map(*body);
        }
        Node::ComputationApp { computation, value } => {
            *computation = map(*computation);
            *value = map(*value);
        }
        Node::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => {
            *computation = map(*computation);
            *value_ty = map(*value_ty);
            *body = map(*body);
        }
        Node::ValueLet { value, body, .. } => {
            *value = map(*value);
            *body = map(*body);
        }
        Node::ProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            *scrutinee = map(*scrutinee);
            for branch in branches {
                branch.body = map(branch.body);
            }
        }
        Node::Acc {
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
        Node::RfType { compute_ty } => *compute_ty = map(*compute_ty),
        Node::RfTerm { compute_ty, term } => {
            *compute_ty = map(*compute_ty);
            *term = map(*term);
        }
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            termination,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *initial = map(*initial);
            *termination = map(*termination);
        }
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        } => {
            *state_ty = map(*state_ty);
            *result_ty = map(*result_ty);
            *step = map(*step);
            *initial = map(*initial);
            *transition = map(*transition);
            *termination = map(*termination);
            *invariant = map(*invariant);
        }
        Node::AccIntro {
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
        Node::AccDescent {
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
        Node::PowerSet { set } | Node::Exists { set } | Node::IdRefl { element: set } => {
            *set = map(*set);
        }
        Node::SubSet { set, predicate, .. } => {
            *set = map(*set);
            *predicate = map(*predicate);
        }
        Node::Pred {
            superset,
            subset,
            element,
        }
        | Node::SubsetElim {
            superset,
            subset,
            element,
        } => {
            *superset = map(*superset);
            *subset = map(*subset);
            *element = map(*element);
        }
        Node::TypeLift { superset, subset } => {
            *superset = map(*superset);
            *subset = map(*subset);
        }
        Node::SubsetIntro {
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
        Node::Equal { left, right } => {
            *left = map(*left);
            *right = map(*right);
        }
        Node::TakeSet {
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
        Node::TakeProp {
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
        Node::ExistsIntro { element, set } => {
            *element = map(*element);
            *set = map(*set);
        }
        Node::IdElim {
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
        Node::AxiomSetExt {
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
        Node::AxiomFunExt {
            left,
            right,
            pointwise,
        } => {
            *left = map(*left);
            *right = map(*right);
            *pointwise = map(*pointwise);
        }
        Node::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            *domain = map(*domain);
            *family = map(*family);
            *inhabited = map(*inhabited);
        }
        Node::TakeEq {
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
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
) -> Exp {
    remap_all_global_ids(arena, exp, definitions, inductives, &HashMap::new())
}

pub fn remap_all_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Exp {
    fn remap(
        arena: &Arena,
        exp: Exp,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
        program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    ) -> Exp {
        let node = arena.get(exp);
        match node {
            Node::DefinedConstant(id) => definitions
                .get(&id)
                .copied()
                .filter(|mapped| *mapped != id)
                .map(|mapped| arena.alloc(Node::DefinedConstant(mapped)))
                .unwrap_or(exp),
            Node::IndType {
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
                    arena.alloc(Node::IndType {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                    })
                }
            }
            Node::IndCtor {
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
                    arena.alloc(Node::IndCtor {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        idx,
                    })
                }
            }
            Node::IndElim {
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
                    arena.alloc(Node::IndElim {
                        indspec: mapped_spec,
                        elim: mapped_elim,
                        return_type: mapped_return,
                        cases: mapped_cases,
                    })
                }
            }
            Node::IndProjection {
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
                    arena.alloc(Node::IndProjection {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        value: mapped_value,
                        field,
                    })
                }
            }
            Node::ProgramIndType {
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
                    arena.alloc(Node::ProgramIndType {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                    })
                }
            }
            Node::ProgramIndCtor {
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
                    arena.alloc(Node::ProgramIndCtor {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        idx,
                        fields: mapped_fields,
                    })
                }
            }
            Node::ProgramIndProjection {
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
                    arena.alloc(Node::ProgramIndProjection {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        value: mapped_value,
                        field,
                    })
                }
            }
            Node::ProgramCase {
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
                    arena.alloc(Node::ProgramCase {
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
    exp: Exp,
    parameter: ModuleParamId,
    replacement: Exp,
) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::ModuleParam(candidate) if *candidate == parameter => {
            Some(shift_bound_indices(arena, replacement, depth, 0))
        }
        _ => None,
    })
}

pub fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= cutoff + depth => {
            Some(arena.alloc(Node::Bound(index + amount)))
        }
        _ => None,
    })
}

/// Replace the outermost locally bound variable in `body` with `argument`.
pub fn instantiate(arena: &Arena, body: Exp, argument: Exp) -> Exp {
    instantiate_at(arena, body, argument, 0)
}

/// Instantiate one binder in the ambient context, leaving `inner` more recent
/// ambient binders in place.
pub fn instantiate_at(arena: &Arena, body: Exp, argument: Exp, inner: usize) -> Exp {
    instantiate_telescope_at(arena, body, std::slice::from_ref(&argument), inner)
}

/// Instantiate an expression whose ambient telescope consists of `arguments`
/// in declaration order. `Bound(0)` denotes the last telescope entry.
pub fn instantiate_telescope(arena: &Arena, exp: Exp, arguments: &[Exp]) -> Exp {
    instantiate_telescope_at(arena, exp, arguments, 0)
}

pub fn instantiate_outer_telescope(
    arena: &Arena,
    exp: Exp,
    arguments: &[Exp],
    inner: usize,
) -> Exp {
    instantiate_telescope_at(arena, exp, arguments, inner)
}

fn instantiate_telescope_at(arena: &Arena, exp: Exp, arguments: &[Exp], inner: usize) -> Exp {
    if arguments.is_empty() {
        return exp;
    }

    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= depth + inner => {
            let ambient = *index - depth;
            let telescope_index = ambient - inner;
            if telescope_index < arguments.len() {
                let argument = arguments[arguments.len() - 1 - telescope_index];
                Some(shift_bound_indices(arena, argument, depth + inner, 0))
            } else {
                Some(arena.alloc(Node::Bound(index - arguments.len())))
            }
        }
        _ => None,
    })
}

/// Rebase references to an implicit ambient context. `mapping[i]` is the new
/// de Bruijn index for the old ambient index `i`; syntactic binders inside the
/// expression are preserved.
pub fn remap_ambient_indices(arena: &Arena, exp: Exp, mapping: &[usize]) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= depth => {
            let ambient = *index - depth;
            mapping
                .get(ambient)
                .filter(|mapped| **mapped != ambient)
                .map(|mapped| arena.alloc(Node::Bound(depth + *mapped)))
        }
        _ => None,
    })
}

/// Remove `count` innermost ambient binders from an expression which does not
/// depend on them. References to older ambient entries are rebased.
pub fn remove_unused_ambient_binders(arena: &Arena, exp: Exp, count: usize) -> Option<Exp> {
    if count == 0 {
        return Some(exp);
    }
    let mut depends = false;
    let result = transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= depth && *index < depth + count => {
            depends = true;
            None
        }
        Node::Bound(index) if *index >= depth + count => {
            Some(arena.alloc(Node::Bound(index - count)))
        }
        _ => None,
    });
    (!depends).then_some(result)
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    fn contains(arena: &Arena, exp: Exp, target: usize, depth: usize) -> bool {
        match arena.get(exp) {
            Node::Bound(index) => index == target + depth,
            Node::Sort(_) | Node::ModuleParam(_) | Node::DefinedConstant(_) => false,
            Node::Prod { ty, body, .. }
            | Node::Lam { ty, body, .. }
            | Node::SubSet {
                set: ty,
                predicate: body,
                ..
            } => contains(arena, ty, target, depth) || contains(arena, body, target, depth + 1),
            Node::IdElim {
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

pub fn exp_subst_map(arena: &Arena, mut exp: Exp, substitutions: &[(ModuleParamId, Exp)]) -> Exp {
    for (parameter, replacement) in substitutions {
        exp = exp_subst_module_param(arena, exp, *parameter, *replacement);
    }
    exp
}

pub fn erase(env: &CrateEnv, exp: Exp) -> Exp {
    let arena = env.arena();
    match arena.get(exp) {
        Node::SubsetIntro { element, .. } => erase(env, element),
        Node::DefinedConstant(definition) => erase(env, env.definition(definition).body),
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

fn reduce_reflected_application(env: &CrateEnv, func: Exp, arg: Exp) -> Option<Exp> {
    let arena = env.arena();
    let Node::RfTerm {
        compute_ty,
        term: reflected_func,
    } = arena.get(func)
    else {
        return None;
    };
    let Node::RfTerm {
        term: reflected_arg,
        ..
    } = arena.get(arg)
    else {
        return None;
    };
    let (codomain, application) = match arena.get(compute_ty) {
        Node::ThunkType { computation_ty } => {
            let Node::ComputationFunction {
                domain: _,
                codomain,
            } = arena.get(computation_ty)
            else {
                return None;
            };
            let forced = arena.alloc(Node::Force {
                value: reflected_func,
            });
            let application = arena.alloc(Node::ComputationApp {
                computation: forced,
                value: reflected_arg,
            });
            (codomain, application)
        }
        Node::ComputationFunction {
            domain: _,
            codomain,
        } => {
            let application = arena.alloc(Node::ComputationApp {
                computation: reflected_func,
                value: reflected_arg,
            });
            (codomain, application)
        }
        _ => return None,
    };
    Some(arena.alloc(Node::RfTerm {
        compute_ty: codomain,
        term: application,
    }))
}

fn unfold_program_value_head(env: &CrateEnv, mut value: Exp) -> Exp {
    loop {
        let Node::DefinedConstant(definition) = env.arena().get(value) else {
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
pub fn reduce_computation_once(env: &CrateEnv, computation: Exp) -> Option<Exp> {
    let arena = env.arena();
    match arena.get(computation) {
        Node::DefinedConstant(definition) => {
            let definition = env.definition(definition);
            (definition.kind == crate::environment::DefinitionKind::ProgramComputation)
                .then_some(definition.body)
        }
        Node::Force { value } => match arena.get(unfold_program_value_head(env, value)) {
            Node::Thunk { computation } => Some(computation),
            _ => None,
        },
        Node::ComputationApp {
            computation: function,
            value,
        } => {
            if let Some(reduced) = reduce_computation_once(env, function) {
                return Some(arena.alloc(Node::ComputationApp {
                    computation: reduced,
                    value,
                }));
            }
            match arena.get(function) {
                Node::ComputationLam { body, .. } => Some(instantiate(arena, body, value)),
                _ => None,
            }
        }
        Node::Sequence {
            computation: source,
            var,
            value_ty,
            body,
        } => {
            if let Some(reduced) = reduce_computation_once(env, source) {
                return Some(arena.alloc(Node::Sequence {
                    computation: reduced,
                    var,
                    value_ty,
                    body,
                }));
            }
            match arena.get(source) {
                Node::Return { value } => Some(instantiate(arena, body, value)),
                _ => None,
            }
        }
        Node::ValueLet { value, body, .. } => Some(instantiate(arena, body, value)),
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            termination,
        } => {
            let forced = arena.alloc(Node::Force { value: step });
            let transition = arena.alloc(Node::ComputationApp {
                computation: forced,
                value: initial,
            });
            let step_result_ty = arena.alloc(Node::ReturnType {
                value_ty: arena.alloc(Node::RunStep {
                    state_ty,
                    result_ty,
                }),
            });
            let reflected_transition = arena.alloc(Node::RfTerm {
                compute_ty: step_result_ty,
                term: transition,
            });
            let invariant = arena.alloc(Node::IdRefl {
                element: reflected_transition,
            });
            Some(arena.alloc(Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                termination,
                invariant,
            }))
        }
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        } => {
            if let Some(reduced) = reduce_computation_once(env, transition) {
                return Some(arena.alloc(Node::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition: reduced,
                    termination,
                    invariant,
                }));
            }
            let Node::Return { value } = arena.get(transition) else {
                return None;
            };
            match arena.get(unfold_program_value_head(env, value)) {
                Node::Continue { next, .. } => {
                    let reflected_from = arena.alloc(Node::RfTerm {
                        compute_ty: state_ty,
                        term: initial,
                    });
                    let reflected_to = arena.alloc(Node::RfTerm {
                        compute_ty: state_ty,
                        term: next,
                    });
                    let next_termination = arena.alloc(Node::AccDescent {
                        state_ty,
                        result_ty,
                        step,
                        from: reflected_from,
                        to: reflected_to,
                        accessibility: termination,
                        transition: invariant,
                    });
                    Some(arena.alloc(Node::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial: next,
                        termination: next_termination,
                    }))
                }
                Node::Finish { output, .. } => Some(arena.alloc(Node::Return { value: output })),
                _ => None,
            }
        }
        Node::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let scrutinee = unfold_program_value_head(env, scrutinee);
            let Node::ProgramIndCtor {
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

/// Evaluate a CBPV computation to a weak normal form.
pub fn evaluate_computation(env: &CrateEnv, computation: Exp) -> Exp {
    let mut current = computation;
    while let Some(next) = reduce_computation_once(env, current) {
        current = next;
    }
    current
}

pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    let arena = env.arena();
    match arena.get(exp) {
        Node::App { func, arg } => match arena.get(func) {
            Node::Lam { body, .. } => Some(instantiate(arena, body, arg)),
            _ => reduce_reflected_application(env, func, arg),
        },
        Node::DefinedConstant(definition) => Some(env.definition(definition).body),
        Node::Pred {
            subset, element, ..
        } => match arena.get(subset) {
            Node::SubSet { predicate, .. } => Some(instantiate(arena, predicate, element)),
            _ => None,
        },
        Node::IndElim { .. } => inductive_type_elim_reduce(env, exp).ok(),
        Node::IndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let reduced = whnf(env, value);
            let (head, arguments) = crate::utils::decompose_app(arena, reduced);
            match arena.get(head) {
                Node::IndCtor {
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
                _ if reduced != value => Some(arena.alloc(Node::IndProjection {
                    indspec,
                    parameters,
                    value: reduced,
                    field,
                })),
                _ => None,
            }
        }
        Node::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let reduced = unfold_program_value_head(env, value);
            match arena.get(reduced) {
                Node::ProgramIndCtor {
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
                _ if reduced != value => Some(arena.alloc(Node::ProgramIndProjection {
                    indspec,
                    parameters,
                    value: reduced,
                    field,
                })),
                _ => None,
            }
        }
        Node::RfType { compute_ty } => match arena.get(compute_ty) {
            Node::ReturnType { value_ty } => Some(arena.alloc(Node::RfType {
                compute_ty: value_ty,
            })),
            Node::ThunkType { computation_ty } => Some(arena.alloc(Node::RfType {
                compute_ty: computation_ty,
            })),
            Node::ComputationFunction { domain, codomain } => {
                let reflected_domain = arena.alloc(Node::RfType { compute_ty: domain });
                let reflected_codomain = arena.alloc(Node::RfType {
                    compute_ty: codomain,
                });
                Some(arena.alloc(Node::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: reflected_domain,
                    body: shift_bound_indices(arena, reflected_codomain, 1, 0),
                }))
            }
            Node::ProgramIndType {
                indspec,
                parameters,
            } => {
                let reflected = env.program_inductive(indspec).reflected();
                let parameters = parameters
                    .into_iter()
                    .map(|parameter| {
                        arena.alloc(Node::RfType {
                            compute_ty: parameter,
                        })
                    })
                    .collect();
                Some(arena.alloc(Node::IndType {
                    indspec: reflected,
                    parameters,
                }))
            }
            _ => None,
        },
        Node::RfTerm { compute_ty, term } => match (arena.get(compute_ty), arena.get(term)) {
            (Node::ReturnType { value_ty }, Node::Return { value }) => {
                Some(arena.alloc(Node::RfTerm {
                    compute_ty: value_ty,
                    term: value,
                }))
            }
            (Node::ThunkType { computation_ty }, Node::Thunk { computation }) => {
                Some(arena.alloc(Node::RfTerm {
                    compute_ty: computation_ty,
                    term: computation,
                }))
            }
            (
                Node::ProgramIndType {
                    indspec: type_spec,
                    parameters: type_parameters,
                },
                Node::ProgramIndCtor {
                    indspec: constructor_spec,
                    parameters: constructor_parameters,
                    idx,
                    fields,
                },
            ) if type_spec == constructor_spec
                && type_parameters.len() == constructor_parameters.len() =>
            {
                let spec = env.program_inductive(type_spec);
                let constructor = spec.constructors().get(idx)?;
                let field_types = constructor.instantiated_fields(arena, &constructor_parameters);
                if field_types.len() != fields.len() {
                    return None;
                }
                let reflected_parameters = constructor_parameters
                    .into_iter()
                    .map(|parameter| {
                        arena.alloc(Node::RfType {
                            compute_ty: parameter,
                        })
                    })
                    .collect::<Vec<_>>();
                let constructor = arena.alloc(Node::IndCtor {
                    indspec: spec.reflected(),
                    parameters: reflected_parameters,
                    idx,
                });
                let reflected_fields = fields
                    .into_iter()
                    .zip(field_types)
                    .map(|(field, (_, field_ty))| {
                        arena.alloc(Node::RfTerm {
                            compute_ty: field_ty,
                            term: field,
                        })
                    })
                    .collect::<Vec<_>>();
                Some(crate::utils::assoc_apply(
                    arena,
                    constructor,
                    reflected_fields,
                ))
            }
            _ => reduce_computation_once(env, term).map(|reduced| {
                arena.alloc(Node::RfTerm {
                    compute_ty,
                    term: reduced,
                })
            }),
        },
        _ => None,
    }
}

fn exp_reduce_head_once_with_cache(
    env: &CrateEnv,
    exp: Exp,
    erase_subset_intro: bool,
    cache: &mut HashMap<Exp, Exp>,
) -> Option<Exp> {
    let arena = env.arena();
    if erase_subset_intro && let Node::SubsetIntro { element, .. } = arena.get(exp) {
        return Some(element);
    }

    // PTS applications use call-by-value: first expose the function,
    // then evaluate the argument, and contract beta only after both are
    // stable.  Evaluating arguments of neutral applications is intentional:
    // constructor values are represented by application spines, so this also
    // evaluates their fields before an eliminator observes them.
    match arena.get(exp) {
        Node::App { func, arg } => {
            let reduced_func = exp_whnf_with_mode_and_cache(env, func, erase_subset_intro, cache);
            if reduced_func != func {
                return Some(arena.alloc(Node::App {
                    func: reduced_func,
                    arg,
                }));
            }
            // Preserve the RfTerm wrapper on the argument until the
            // Rf-C-App/Rf-U-App root rule has had a chance to fire.
            if let Some(reduced) = reduce_reflected_application(env, func, arg) {
                return Some(reduced);
            }
            let reduced_arg = exp_whnf_with_mode_and_cache(env, arg, erase_subset_intro, cache);
            if reduced_arg != arg {
                return Some(arena.alloc(Node::App {
                    func,
                    arg: reduced_arg,
                }));
            }
        }
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            let reduced_elim = exp_whnf_with_mode_and_cache(env, elim, erase_subset_intro, cache);
            if reduced_elim != elim {
                return Some(arena.alloc(Node::IndElim {
                    indspec,
                    elim: reduced_elim,
                    return_type,
                    cases,
                }));
            }
        }
        Node::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            let reduced_next = exp_whnf_with_mode_and_cache(env, next, erase_subset_intro, cache);
            if reduced_next != next {
                return Some(arena.alloc(Node::Continue {
                    state_ty,
                    result_ty,
                    next: reduced_next,
                }));
            }
        }
        Node::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            let reduced_output =
                exp_whnf_with_mode_and_cache(env, output, erase_subset_intro, cache);
            if reduced_output != output {
                return Some(arena.alloc(Node::Finish {
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
        Node::Pred {
            superset,
            subset,
            element,
        } => {
            let reduced_subset =
                exp_whnf_with_mode_and_cache(env, subset, erase_subset_intro, cache);
            (reduced_subset != subset).then(|| {
                arena.alloc(Node::Pred {
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
    exp: Exp,
    erase_subset_intro: bool,
    cache: &mut HashMap<Exp, Exp>,
) -> Exp {
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

fn exp_whnf_with_mode(env: &CrateEnv, exp: Exp, erase_subset_intro: bool) -> Exp {
    let mut cache = HashMap::new();
    exp_whnf_with_mode_and_cache(env, exp, erase_subset_intro, &mut cache)
}

pub fn whnf(env: &CrateEnv, exp: Exp) -> Exp {
    exp_whnf_with_mode(env, exp, false)
}

pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    normalize_with_cache(env, exp, &mut HashMap::new())
}

fn normalize_with_cache(env: &CrateEnv, exp: Exp, cache: &mut HashMap<Exp, Exp>) -> Exp {
    if let Some(normal) = cache.get(&exp) {
        return *normal;
    }
    let arena = env.arena();
    let head = whnf(env, exp);
    let node = arena.get(head);
    if let Node::Run {
        state_ty,
        result_ty,
        step,
        initial,
        termination,
    } = node
    {
        // The certificate is proof-only. In particular, an open/stuck run
        // must not start evaluating its proof while normalizing a function
        // body.
        let normalized_state_ty = normalize_with_cache(env, state_ty, cache);
        let normalized_result_ty = normalize_with_cache(env, result_ty, cache);
        let normalized_step = normalize_with_cache(env, step, cache);
        let normalized_initial = normalize_with_cache(env, initial, cache);
        let changed = normalized_state_ty != state_ty
            || normalized_result_ty != result_ty
            || normalized_step != step
            || normalized_initial != initial;
        let candidate = if changed {
            arena.alloc(Node::Run {
                state_ty: normalized_state_ty,
                result_ty: normalized_result_ty,
                step: normalized_step,
                initial: normalized_initial,
                termination,
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

pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    if let Some(reduced) = exp_reduce_head_once_with_cache(env, exp, false, &mut HashMap::new()) {
        return Some(reduced);
    }
    let normalized = normalize(env, exp);
    (normalized != exp).then_some(normalized)
}

pub fn convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(env, left, right, false)
}

pub fn erased_normal(env: &CrateEnv, exp: Exp) -> Exp {
    let erased = erase(env, exp);
    normalize(env, erased)
}

pub fn erased_convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(env, left, right, true)
}

pub(crate) fn type_head_normal(env: &CrateEnv, ty: Exp) -> Exp {
    exp_whnf_with_mode(env, ty, true)
}

pub(crate) fn expose_product(env: &CrateEnv, ty: Exp) -> Option<(SymbolId, Exp, Exp)> {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            Node::Prod { var, ty, body } => return Some((var, ty, body)),
            Node::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return None,
        }
    }
}

pub(crate) fn base_carrier(env: &CrateEnv, ty: Exp) -> Exp {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            Node::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return current,
        }
    }
}

pub fn common_ambient_carrier(env: &CrateEnv, left_ty: Exp, right_ty: Exp) -> Option<Exp> {
    let left_carrier = base_carrier(env, left_ty);
    let right_carrier = base_carrier(env, right_ty);
    erased_convertible(env, left_carrier, right_carrier).then_some(left_carrier)
}

pub fn can_weaken_to(env: &CrateEnv, inferred: Exp, expected: Exp) -> bool {
    if erased_convertible(env, inferred, expected) {
        return true;
    }
    let arena = env.arena();
    let inferred = type_head_normal(env, inferred);
    let expected = type_head_normal(env, expected);
    match (arena.get(inferred), arena.get(expected)) {
        (Node::TypeLift { superset, .. }, _) => can_weaken_to(env, superset, expected),
        (
            Node::Prod {
                ty: inferred_domain,
                body: inferred_body,
                ..
            },
            Node::Prod {
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
