use crate::{
    calculus::{exp_is_alpha_eq, exp_reduce_if_top, instantiate, normalize},
    derivation::CheckSession,
    environment::{CrateEnv, ModuleArgument},
    exp::{ExpContextEntry, ExpNode},
    ids::{DefId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationNode, Program, ProgramContextEntry, ProgramType, ValueNode, ValueTypeNode,
    },
    program_calculus::{
        Evaluation, evaluate_computation, instantiate_value_type, remap_computation_global_ids,
        remap_value_type_global_ids, shift_computation_indices, shift_value_type_indices,
        strengthen_value_type, subst_computation_module_params, subst_value_type_module_params,
    },
    program_derivation::ProgramCheckSession,
    sort::Sort,
};

#[test]
fn boxed_program_types_compare_structurally() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let left_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    let right_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    assert_ne!(left_state, right_state);
    let left = arena.alloc(ExpNode::BoxType {
        program_ty: ProgramType::Value(left_state),
    });
    let right = arena.alloc(ExpNode::BoxType {
        program_ty: ProgramType::Value(right_state),
    });
    assert!(exp_is_alpha_eq(&env, left, right));

    let output = arena.value_bound(0);
    let program = arena.alloc(ValueNode::Finish {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
        output,
    });
    let boxed = arena.alloc(ExpNode::BoxProgram {
        program_ty: ProgramType::Value(left_state),
        program: Program::Value(program),
    });
    let forced = arena.alloc(ExpNode::ForceBox {
        program_ty: ProgramType::Value(right_state),
        boxed,
    });
    assert!(matches!(
        exp_reduce_if_top(&env, forced).map(|exp| arena.get(exp)),
        Some(ExpNode::Finish { .. })
    ));
}

#[test]
fn beta_reduction_remains_set_only() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let set = arena.sort(Sort::Set(0));
    let body = arena.exp_bound(0);
    let lambda = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty: set,
        body,
    });
    let application = arena.alloc(ExpNode::App {
        func: lambda,
        arg: set,
    });
    assert!(exp_is_alpha_eq(&env, normalize(&env, application), set));
    assert_eq!(instantiate(arena, body, set), set);
}

#[test]
fn set_and_program_contexts_are_distinct() {
    let env = CrateEnv::new();
    let set = env.arena().sort(Sort::Set(0));
    let mut set_context = vec![ExpContextEntry {
        var: SymbolId(2),
        ty: set,
    }];
    CheckSession::new(&env, env.root_module(), &mut set_context)
        .check_wellformed_context()
        .unwrap();

    let value_ty = env.arena().alloc(ValueTypeNode::Bound(0));
    let mut program_context = vec![ProgramContextEntry::Type { var: SymbolId(3) }];
    ProgramCheckSession::new(&env, &mut program_context)
        .check_value_type(value_ty)
        .unwrap();
}

#[test]
fn program_typing_and_evaluation_use_program_handles() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let value = arena.value_bound(0);
    let returned = arena.alloc(ComputationNode::Return { value });
    assert_eq!(
        evaluate_computation(&env, returned),
        Evaluation::Normal(returned)
    );
}

#[test]
fn program_run_has_no_set_exp_node() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let state_ty = arena.alloc(ValueTypeNode::Bound(0));
    let step = arena.alloc(ValueNode::Bound(0));
    let initial = arena.alloc(ValueNode::Bound(1));
    let run = arena.alloc(ComputationNode::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial,
    });
    assert!(matches!(arena.get(run), ComputationNode::Run { .. }));
}

#[test]
fn unchanged_program_transforms_reuse_arena_handles() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let parameter_id = ModuleParamId {
        module: env.root_module(),
        position: 0,
    };
    let parameter = arena.value_type_module_param(parameter_id);
    let returned = arena.alloc(crate::program::ComputationTypeNode::Return {
        value_ty: parameter,
    });
    let thunk = arena.alloc(ValueTypeNode::Thunk {
        computation_ty: returned,
    });
    let inductive_remapping = std::collections::HashMap::from([(
        ProgramInductiveId {
            module: env.root_module(),
            index: 10,
        },
        ProgramInductiveId {
            module: env.root_module(),
            index: 11,
        },
    )]);
    let unrelated_parameter = ModuleParamId {
        module: env.root_module(),
        position: 1,
    };
    let substitutions = [(unrelated_parameter, ModuleArgument::ProgramType(parameter))];

    assert_eq!(shift_value_type_indices(arena, thunk, 1, 0), thunk);
    assert_eq!(instantiate_value_type(arena, thunk, parameter, 0), thunk);
    assert_eq!(
        remap_value_type_global_ids(arena, thunk, &Default::default(), &inductive_remapping),
        thunk
    );
    assert_eq!(
        subst_value_type_module_params(arena, thunk, &substitutions),
        thunk
    );
    assert_eq!(strengthen_value_type(arena, thunk, 0), Some(thunk));

    let value = arena.alloc(ValueNode::ModuleParam(parameter_id));
    let computation = arena.alloc(ComputationNode::Return { value });
    let definition_remapping = std::collections::HashMap::from([(
        DefId {
            module: env.root_module(),
            index: 10,
        },
        DefId {
            module: env.root_module(),
            index: 11,
        },
    )]);
    assert_eq!(
        shift_computation_indices(arena, computation, 1, 0),
        computation
    );
    assert_eq!(
        remap_computation_global_ids(
            arena,
            computation,
            &definition_remapping,
            &inductive_remapping,
        ),
        computation
    );
    assert_eq!(
        subst_computation_module_params(arena, computation, &substitutions),
        computation
    );
}

#[test]
fn strengthening_rejects_a_dependent_program_type() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let dependent = arena.value_type_bound(0);
    assert_eq!(strengthen_value_type(arena, dependent, 0), None);

    let outer = arena.value_type_bound(1);
    let strengthened = strengthen_value_type(arena, outer, 0).unwrap();
    assert!(matches!(arena.get(strengthened), ValueTypeNode::Bound(0)));
}
