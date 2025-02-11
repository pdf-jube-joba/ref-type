use crate::{
    ast::{Exp, Var},
    environment::{
        printing::{print_fail_tree, print_tree, TreeConfig},
        DerivationFailed, GlobalContext, LocalContext, PartialDerivationTreeTypeCheck,
        ProvableJudgement,
    },
    interpreter::GoalTree,
    lambda_calculus,
    parse::{check_inductive_syntax, InductiveDefinitionsSyntax},
    proving::{proof_tree, ErrProofTree, PartialDerivationTreeProof, UserSelect},
    typing::{type_check, type_infer},
};
use std::fmt::Display;

use self::context::{ResIndDefsError, ResIndDefsOk};

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
        e: Exp,
    },
    Check {
        e1: Exp,
        e2: Exp,
        config: TreeConfig,
    },
    Infer {
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
pub enum CommandAllResult {
    ParseCommandResult,
    SubstCommandResult {
        e: Exp,
    },
    AlphaEqResult {
        eq: bool,
    },
    BetaEqResult {
        eq: bool,
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
    NeedProve,
    CheckResult {
        result: Result<PartialDerivationTreeTypeCheck, DerivationFailed>,
        config: TreeConfig,
    },
    InferResult {
        result: Result<Exp, DerivationFailed>,
        config: TreeConfig,
    },
    NewDefinitionResult {
        result: Result<PartialDerivationTreeTypeCheck, DerivationFailed>,
        config: TreeConfig,
    },
    NewAssumptionResult {
        result: Result<PartialDerivationTreeTypeCheck, DerivationFailed>,
        config: TreeConfig,
    },
    NewInductiveResult {
        result: Result<ResIndDefsOk, ResIndDefsError>,
        config: TreeConfig,
    },
    ShowGoalResult {
        result: Result<(), ()>,
        goals: Option<Vec<GoalTree>>,
    },
    ProveGoalResult {
        result: Result<(), ErrProofTree>,
    },
    AdmitResult {
        result: Result<(), ()>,
    },
    AdmitAllResult {
        result: Result<(), ()>,
    },
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
            CommandAll::Normalize { e } => write!(f, "normalize {}", e),
            CommandAll::Check { e1, e2, config } => write!(f, "check {} <| {}", e1, e2),
            CommandAll::Infer { e } => write!(f, "infer {}", e),
            CommandAll::NewDefinition { x, t, e, config: _ } => {
                write!(f, "new_definition {} {} {}", x, t, e)
            }
            CommandAll::NewAssumption { x, t, config: _ } => {
                write!(f, "new_assumption {} {}", x, t)
            }
            CommandAll::NewInductive { inddefs, config: _ } => {
                write!(f, "new_inductive {:?}", inddefs)
            }
            CommandAll::ShowGoal => write!(f, "show_goal"),
            CommandAll::ProveGoal { user_select } => write!(f, "prove_goal {:?}", user_select),
            CommandAll::Admit => write!(f, "admit"),
            CommandAll::AdmitAll => write!(f, "admit_all"),
        }
    }
}

impl Display for CommandAllResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandAllResult::NeedProve => write!(f, "NEED PROVE!"),
            CommandAllResult::ParseCommandResult => write!(f, " ok"),
            CommandAllResult::SubstCommandResult { e } => write!(f, " => {}", e),
            CommandAllResult::AlphaEqResult { eq } => write!(f, " =~(alpha) {}", eq),
            CommandAllResult::BetaEqResult { eq } => write!(f, " =~(beta) {}", eq),
            CommandAllResult::TopReduceResult { e } => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResult::ReduceResult { e } => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResult::NormalizeResult { es } => {
                for e in es {
                    writeln!(f, " => {}", e)?;
                }
                Ok(())
            }
            CommandAllResult::CheckResult { result, config } => match result {
                Ok(tree) => write!(f, "{}", print_tree(tree, config)),
                Err(tree) => write!(f, "{}", print_fail_tree(tree, config)),
            },
            CommandAllResult::InferResult { result, config } => match result {
                Ok(exp) => write!(f, " => {}", exp),
                Err(err) => write!(f, "{}", print_fail_tree(err, config)),
            },
            CommandAllResult::NewDefinitionResult { result, config } => match result {
                Ok(tree) => write!(f, "{}", print_tree(tree, config)),
                Err(err) => write!(f, "{}", print_fail_tree(err, config)),
            },
            CommandAllResult::NewAssumptionResult { result, config } => match result {
                Ok(tree) => write!(f, " {}", print_tree(tree, config)),
                Err(err) => write!(f, "{}", print_fail_tree(err, config)),
            },
            CommandAllResult::NewInductiveResult { result, config } => match result {
                Ok(ok) => {
                    let ResIndDefsOk {
                        arity_well_formed,
                        constructor_wellformed,
                    } = ok;
                    write!(f, "{}\n", print_tree(arity_well_formed, config))?;
                    for tree in constructor_wellformed {
                        write!(f, "{}\n", print_tree(tree, config))?;
                    }
                    Ok(())
                }
                Err(err) => match err {
                    ResIndDefsError::AlreadyDefinedType => write!(f, "AlreadyDefinedType"),
                    ResIndDefsError::ArityNotWellformed(err) => write!(
                        f,
                        "arity not wellformed \n {}",
                        print_fail_tree(err, config)
                    ),
                    ResIndDefsError::ConstructorNotWellFormed(err) => {
                        write!(f, "constructor not wellformed \n",)?;
                        for tree in err {
                            match tree {
                                Ok(tree) => writeln!(f, "{}", print_tree(tree, config))?,
                                Err(tree) => writeln!(f, "{}", print_fail_tree(tree, config))?,
                            }
                        }
                        Ok(())
                    }
                },
            },
            CommandAllResult::ShowGoalResult { result, goals } => match result {
                Ok(_) => write!(f, "show_goal ok"),
                Err(_) => {
                    if let Some(goals) = goals {
                        for goal in goals {
                            writeln!(f, " => {:?}", goal)?;
                        }
                    }
                    Ok(())
                }
            },
            CommandAllResult::ProveGoalResult { result } => match result {
                Ok(_) => write!(f, "prove_goal ok"),
                Err(_) => write!(f, "prove_goal err"),
            },
            CommandAllResult::AdmitResult { result } => match result {
                Ok(_) => write!(f, "admit ok"),
                Err(_) => write!(f, "admit no_need_to_prove"),
            },
            CommandAllResult::AdmitAllResult { result } => match result {
                Ok(_) => write!(f, "admit_all ok"),
                Err(_) => write!(f, "admit_all no_need_to_prove"),
            },
        }
    }
}
