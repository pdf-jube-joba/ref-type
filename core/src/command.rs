use crate::{
    ast::{inductives::InductiveDefinitionsSyntax, Exp, Var},
    environment::derivation_tree::*,
    printing::*,
    proving::{ErrProofTree, UserSelect},
};
use std::fmt::Display;

// use self::context::{ResIndDefsError, ResIndDefsOk};

use self::{
    environment::{
        check_well_formed::{ResIndDefsError, ResIndDefsOk},
        tree_node::{LocalContext, ProvableJudgement},
    },
    proving::PartialDerivationTreeProof,
};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandAll {
    ParseCommand {
        exp: Exp,
    },
    SubstCommand {
        e1: Exp,
        x: Var,
        e2: Exp,
    },
    AlphaEq {
        e1: Exp,
        e2: Exp,
        succ_flag: bool,
    },
    BetaEq {
        e1: Exp,
        e2: Exp,
        succ_flag: bool,
    },
    TopReduce {
        e: Exp,
    },
    Reduce {
        e: Exp,
    },
    Normalize {
        process: bool,
        e: Exp,
    },
    Check {
        config: TreeConfig,
        e1: Exp,
        e2: Exp,
    },
    Infer {
        config: TreeConfig,
        e: Exp,
    },
    Theorem {
        config: TreeConfig,
        e: Exp,
    },
    NewDefinition {
        config: TreeConfig,
        x: Var,
        t: Exp,
        e: Exp,
    },
    NewAssumption {
        config: TreeConfig,
        x: Var,
        t: Exp,
    },
    NewInductive {
        config: TreeConfig,
        inddefs: InductiveDefinitionsSyntax,
    },
    ShowGoal,
    ProveGoal {
        user_select: UserSelect,
    },
    Admit,
    AdmitAll,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandAllResultErr {
    NotInProofMode,
    NotInCommandMode,
    AlphaEq {
        expected: bool,
    },
    BetaEq {
        expected: bool,
    },
    CheckFailed {
        result: DerivationFailed,
        config: TreeConfig,
    },
    InferFailed {
        result: DerivationFailed,
        config: TreeConfig,
    },
    TheoremIsNotProp {
        result: DerivationFailed,
        config: TreeConfig,
    },
    NewDefinitionFailed {
        result: DerivationFailed,
        config: TreeConfig,
    },
    NewAssumptionFailed {
        result: DerivationFailed,
        config: TreeConfig,
    },
    NewInductiveFailed {
        result: ResIndDefsError,
        config: TreeConfig,
    },
    ProofErr {
        result: ErrProofTree,
        config: TreeConfig,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandAllResultOk {
    ParseCommandResult,
    SubstCommandResult {
        e: Exp,
    },
    AlphaEqResult {
        expected: bool,
    },
    BetaEqResult {
        expected: bool,
    },
    TopReduceResult {
        e: Option<Exp>,
    },
    ReduceResult {
        e: Option<Exp>,
    },
    NormalizeResult {
        es: Vec<Exp>,
    },
    CheckResult {
        result: PartialDerivationTreeTypeCheck,
        config: TreeConfig,
    },
    InferResult {
        result_exp: Exp,
        result_tree: PartialDerivationTreeTypeCheck,
        config: TreeConfig,
    },
    TheoremIsProp {
        result: PartialDerivationTreeTypeCheck,
        config: TreeConfig,
    },
    NewDefinitionResult {
        result: PartialDerivationTreeTypeCheck,
        config: TreeConfig,
    },
    NewAssumptionResult {
        result: PartialDerivationTreeTypeCheck,
        config: TreeConfig,
    },
    NewInductiveResult {
        result: ResIndDefsOk,
        config: TreeConfig,
    },
    ShowGoalResult {
        goals: Option<GoalTree>,
    },
    ProveGoalResult {
        result: PartialDerivationTreeProof,
        config: TreeConfig,
    },
    AdmitResult {
        proof_judge: ProvableJudgement,
    },
    AdmitAllResult,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpreterError {
    UnprovedState,
    NoNeedToProve,
}

impl Display for InterpreterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpreterError::UnprovedState => write!(f, "UnprovedState"),
            InterpreterError::NoNeedToProve => write!(f, "NoNeedToProve"),
        }
    }
}

impl Display for CommandAll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandAll::ParseCommand { exp } => write!(f, "parse {}", exp),
            CommandAll::SubstCommand { e1, x, e2 } => write!(f, "subst {} {} {}", e1, x, e2),
            CommandAll::AlphaEq { e1, e2, succ_flag } => {
                write!(f, "alpha_eq {} {} {}", e1, e2, succ_flag)
            }
            CommandAll::BetaEq { e1, e2, succ_flag } => {
                write!(f, "beta_eq {} {} {}", e1, e2, succ_flag)
            }
            CommandAll::TopReduce { e } => write!(f, "top_reduce {}", e),
            CommandAll::Reduce { e } => write!(f, "reduce {}", e),
            CommandAll::Normalize { e, process: _ } => write!(f, "normalize {}", e),
            CommandAll::Check { e1, e2, config: _ } => write!(f, "check {} <| {}", e1, e2),
            CommandAll::Infer { config: _, e } => write!(f, "infer {}", e),
            CommandAll::NewDefinition { x, t, e, config: _ } => {
                write!(f, "new_definition {}: {} : {}", x, t, e)
            }
            CommandAll::Theorem { e, config: _ } => write!(f, "theorem {e}"),
            CommandAll::NewAssumption { x, t, config: _ } => {
                write!(f, "new_assumption {}: {}", x, t)
            }
            CommandAll::NewInductive { inddefs, config: _ } => {
                write!(f, "new_inductive {}", inddefs)
            }
            CommandAll::ShowGoal => write!(f, "show_goal"),
            CommandAll::ProveGoal { user_select } => write!(f, "prove_goal {:?}", user_select),
            CommandAll::Admit => write!(f, "admit"),
            CommandAll::AdmitAll => write!(f, "admit_all"),
        }
    }
}

impl Display for CommandAllResultOk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandAllResultOk::ParseCommandResult => write!(f, " ok"),
            CommandAllResultOk::SubstCommandResult { e } => write!(f, " => {}", e),
            CommandAllResultOk::AlphaEqResult { expected } => {
                write!(f, "=~(alpha) ... {}", if *expected { "o" } else { "x" })
            }
            CommandAllResultOk::BetaEqResult { expected } => {
                write!(f, "=~(beta) ... {}", if *expected { "o" } else { "x" })
            }
            CommandAllResultOk::TopReduceResult { e } => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResultOk::ReduceResult { e } => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResultOk::NormalizeResult { es } => {
                for e in es {
                    writeln!(f, " => {}", e)?;
                }
                Ok(())
            }
            CommandAllResultOk::CheckResult { result, config } => {
                write!(f, "{}", print_tree(result, config))
            }
            CommandAllResultOk::InferResult {
                result_exp,
                result_tree,
                config,
            } => {
                write!(
                    f,
                    "infered: {}\n{}",
                    result_exp,
                    print_tree(result_tree, config)
                )
            }
            CommandAllResultOk::TheoremIsProp { result, config } => {
                write!(f, "{}", print_tree(result, config))
            }
            CommandAllResultOk::NewDefinitionResult { result, config } => {
                write!(f, "{}", print_tree(result, config))
            }
            CommandAllResultOk::NewAssumptionResult { result, config } => {
                write!(f, "{}", print_tree(result, config))
            }
            CommandAllResultOk::NewInductiveResult { result, config } => {
                let ResIndDefsOk {
                    arity_well_formed,
                    constructor_wellformed,
                } = result;
                writeln!(f, "{}", print_tree(arity_well_formed, config))?;
                for tree in constructor_wellformed {
                    writeln!(f, "{}", print_tree(tree, config))?;
                }
                Ok(())
            }
            CommandAllResultOk::ShowGoalResult { goals } => {
                if let Some(goals) = goals {
                    match goals {
                        GoalTree::UnSolved(prop) => {
                            writeln!(f, "?{prop}")?;
                        }
                        GoalTree::Branch(goals) => {
                            for goal in goals {
                                writeln!(f, " ?{}", into_printing_tree(goal))?;
                            }
                        }
                    }
                } else {
                    writeln!(f, "no goal")?;
                }
                Ok(())
            }
            CommandAllResultOk::ProveGoalResult { result, config } => {
                write!(f, "prove ok\n{}", print_proof_tree(result, config))
            }
            CommandAllResultOk::AdmitResult { proof_judge } => write!(f, "ADMIT {proof_judge}"),
            CommandAllResultOk::AdmitAllResult => write!(f, "admit_all ok"),
        }
    }
}

impl Display for CommandAllResultErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandAllResultErr::NotInProofMode => write!(f, "NotInProofMode"),
            CommandAllResultErr::NotInCommandMode => write!(f, "NotInCommandMode"),
            CommandAllResultErr::AlphaEq { expected } => {
                write!(f, "expected: {}", expected)
            }
            CommandAllResultErr::BetaEq { expected } => {
                write!(f, "expected: {}", expected)
            }
            CommandAllResultErr::CheckFailed { result, config } => {
                write!(f, "{}", print_fail_tree(result, config))
            }
            CommandAllResultErr::InferFailed { result, config } => {
                write!(f, "{}", print_fail_tree(result, config))
            }
            CommandAllResultErr::TheoremIsNotProp { result, config } => {
                write!(f, "{}", print_fail_tree(result, config))
            }
            CommandAllResultErr::NewDefinitionFailed { result, config } => {
                write!(f, "{}", print_fail_tree(result, config))
            }
            CommandAllResultErr::NewAssumptionFailed { result, config } => {
                write!(f, "{}", print_fail_tree(result, config))
            }
            CommandAllResultErr::NewInductiveFailed { result, config } => match result {
                ResIndDefsError::AlreadyDefinedType => write!(f, "AlreadyDefinedType"),
                ResIndDefsError::SyntaxError(err) => write!(f, "{err}"),
                ResIndDefsError::ArityNotWellformed(err) => write!(
                    f,
                    "arity not wellformed \n {}",
                    print_fail_tree(err, config)
                ),
                ResIndDefsError::ConstructorNotWellFormed(err) => {
                    writeln!(f, "constructor not wellformed ",)?;
                    for tree in err {
                        match tree {
                            Ok(tree) => writeln!(f, "{}", print_tree(tree, config))?,
                            Err(tree) => writeln!(f, "{}", print_fail_tree(tree, config))?,
                        }
                    }
                    Ok(())
                }
            },
            CommandAllResultErr::ProofErr { result, config } => match result {
                ErrProofTree::FailTree { fail_tree } => {
                    write!(f, "{}", print_fail_tree(fail_tree, config))
                }
                ErrProofTree::NotAlphaEq => write!(f, "NotAlphaEq"),
                ErrProofTree::FailCondition { condition } => write!(f, "{condition:?}"),
                ErrProofTree::NotReduceble => write!(f, "NotReduceble"),
                ErrProofTree::NotAppropriateForm(err) => write!(f, "{err}"),
            },
        }
    }
}
