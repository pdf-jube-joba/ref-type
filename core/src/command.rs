use crate::{
    ast::{Exp, Var},
    context::{
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
pub struct ParseCommand {
    pub exp: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseCommandResult {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstCommand {
    pub e1: Exp,
    pub x: Var,
    pub e2: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstCommandResult {
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaEq {
    pub e1: Exp,
    pub e2: Exp,
    pub succ_flag: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaEqResult {
    pub eq: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BetaEq {
    pub e1: Exp,
    pub e2: Exp,
    pub succ_flag: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BetaEqResult {
    pub eq: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TopReduce {
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TopReduceResult {
    pub e: Option<Exp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reduce {
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReduceResult {
    pub e: Option<Exp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Normalize {
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizeResult {
    pub es: Vec<Exp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    pub e1: Exp,
    pub e2: Exp,
    pub config: TreeConfig,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    Ok(PartialDerivationTreeTypeCheck, TreeConfig),
    ErrOnTyping(DerivationFailed, TreeConfig),
    ErrOnState(InterpreterError, TreeConfig),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Infer {
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferResult {
    Ok(Exp),
    ErrOnTyping(DerivationFailed, TreeConfig),
    ErrOnState(InterpreterError, TreeConfig),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewDefinition {
    pub config: TreeConfig,
    pub x: Var,
    pub t: Exp,
    pub e: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewDefinitionResult {
    Ok(PartialDerivationTreeTypeCheck, TreeConfig),
    ErrOnTyping(DerivationFailed, TreeConfig),
    ErrOnState(InterpreterError, TreeConfig),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewAssumption {
    pub config: TreeConfig,
    pub x: Var,
    pub t: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewAssumptionResult {
    Ok(PartialDerivationTreeTypeCheck, TreeConfig),
    ErrOnTyping(DerivationFailed, TreeConfig),
    ErrOnState(InterpreterError, TreeConfig),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewInductive {
    pub config: TreeConfig,
    pub inddefs: InductiveDefinitionsSyntax,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewInductiveResult {
    Ok(ResIndDefsOk, TreeConfig),
    Err(ResIndDefsError, TreeConfig),
    ErrOnSyntax(String),
    ErrOnState(InterpreterError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShowGoal {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShowGoalResult {
    Ok,
    Pended(Vec<GoalTree>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProveGoal {
    pub user_select: UserSelect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveGoalResult {
    Ok,
    NoNeedToProve,
    Err(ErrProofTree),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Admit {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmitResult {
    Ok,
    NoNeedToProve,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmitAll {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmitAllResult {
    Ok,
    NoNeedToProve,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandAll {
    ParseCommand(ParseCommand),
    SubstCommand(SubstCommand),
    AlphaEq(AlphaEq),
    BetaEq(BetaEq),
    TopReduce(TopReduce),
    Reduce(Reduce),
    Normalize(Normalize),
    Check(Check),
    Infer(Infer),
    NewDefinition(NewDefinition),
    NewAssumption(NewAssumption),
    NewInductive(NewInductive),
    ShowGoal(ShowGoal),
    ProveGoal(ProveGoal),
    Admit(Admit),
    AdmitAll(AdmitAll),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandAllResult {
    ParseCommandResult(ParseCommandResult),
    SubstCommandResult(SubstCommandResult),
    AlphaEqResult(AlphaEqResult),
    BetaEqResult(BetaEqResult),
    TopReduceResult(TopReduceResult),
    ReduceResult(ReduceResult),
    NormalizeResult(NormalizeResult),
    CheckResult(CheckResult),
    InferResult(InferResult),
    NewDefinitionResult(NewDefinitionResult),
    NewAssumptionResult(NewAssumptionResult),
    NewInductiveResult(NewInductiveResult),
    ShowGoalResult(ShowGoalResult),
    ProveGoalResult(ProveGoalResult),
    AdmitResult(AdmitResult),
    AdmitAllResult(AdmitAllResult),
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
            CommandAll::ParseCommand(ParseCommand { exp }) => write!(f, "parse {}", exp),
            CommandAll::SubstCommand(SubstCommand { e1, x, e2 }) => {
                write!(f, "subst {} {} {}", e1, x, e2)
            }
            CommandAll::AlphaEq(AlphaEq { e1, e2, succ_flag }) => {
                write!(f, "alpha_eq {} {} {}", e1, e2, succ_flag)
            }
            CommandAll::BetaEq(BetaEq { e1, e2, succ_flag }) => {
                write!(f, "beta_eq {} {} {}", e1, e2, succ_flag)
            }
            CommandAll::TopReduce(TopReduce { e }) => write!(f, "top_reduce {}", e),
            CommandAll::Reduce(Reduce { e }) => write!(f, "reduce {}", e),
            CommandAll::Normalize(Normalize { e }) => write!(f, "normalize {}", e),
            CommandAll::Check(Check { e1, e2, config }) => write!(f, "check {} <| {}", e1, e2),
            CommandAll::Infer(Infer { e }) => write!(f, "infer {}", e),
            CommandAll::NewDefinition(NewDefinition { x, t, e, config: _ }) => {
                write!(f, "new_definition {} {} {}", x, t, e)
            }
            CommandAll::NewAssumption(NewAssumption { x, t, config: _ }) => {
                write!(f, "new_assumption {} {}", x, t)
            }
            CommandAll::NewInductive(NewInductive { inddefs, config: _ }) => {
                write!(f, "new_inductive {:?}", inddefs)
            }
            CommandAll::ShowGoal(_) => write!(f, "show_goal"),
            CommandAll::ProveGoal(ProveGoal { user_select }) => {
                write!(f, "prove_goal {:?}", user_select)
            }
            CommandAll::Admit(_) => write!(f, "admit"),
            CommandAll::AdmitAll(_) => write!(f, "admit_all"),
        }
    }
}

impl Display for CommandAllResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandAllResult::ParseCommandResult(ParseCommandResult {}) => write!(f, " ok"),
            CommandAllResult::SubstCommandResult(SubstCommandResult { e }) => {
                write!(f, " => {}", e)
            }
            CommandAllResult::AlphaEqResult(AlphaEqResult { eq }) => {
                write!(f, " =~(alpha) {}", eq)
            }
            CommandAllResult::BetaEqResult(BetaEqResult { eq }) => {
                write!(f, " =~(beta) {}", eq)
            }
            CommandAllResult::TopReduceResult(TopReduceResult { e }) => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResult::ReduceResult(ReduceResult { e }) => match e {
                Some(e) => write!(f, " => {}", e),
                None => write!(f, " => !"),
            },
            CommandAllResult::NormalizeResult(NormalizeResult { es }) => {
                for e in es {
                    writeln!(f, " => {}", e)?;
                }
                Ok(())
            }
            CommandAllResult::CheckResult(result) => match result {
                CheckResult::Ok(tree, tree_config) => {
                    write!(f, "{}", print_tree(tree, tree_config))
                }
                CheckResult::ErrOnTyping(tree, config) => {
                    write!(f, "{}", print_fail_tree(tree, config))
                }
                CheckResult::ErrOnState(err, _) => {
                    write!(f, "{err}")
                }
            },
            CommandAllResult::InferResult(result) => match result {
                InferResult::Ok(exp) => write!(f, " => {}", exp),
                InferResult::ErrOnTyping(err, config) => {
                    write!(f, "{}", print_fail_tree(err, config))
                }
                InferResult::ErrOnState(err, config) => {
                    write!(f, "{err}")
                }
            },
            CommandAllResult::NewDefinitionResult(result) => match result {
                NewDefinitionResult::Ok(tree, config) => {
                    write!(f, "{}", print_tree(tree, config))
                }
                NewDefinitionResult::ErrOnTyping(err, config) => {
                    write!(f, "{}", print_fail_tree(err, config))
                }
                NewDefinitionResult::ErrOnState(err, config) => {
                    write!(f, "{err}")
                }
            },
            CommandAllResult::NewAssumptionResult(result) => match result {
                NewAssumptionResult::Ok(tree, config) => {
                    write!(f, " {}", print_tree(tree, config))
                }
                NewAssumptionResult::ErrOnTyping(err, config) => {
                    write!(f, "{}", print_fail_tree(err, config))
                }
                NewAssumptionResult::ErrOnState(err, config) => {
                    write!(f, "{err}")
                }
            },
            CommandAllResult::NewInductiveResult(result) => match result {
                NewInductiveResult::Ok(ok, config) => {
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
                NewInductiveResult::Err(err, config) => match err {
                    ResIndDefsError::AlreadyDefinedType => {
                        write!(f, "AlreadyDefinedType")
                    }
                    ResIndDefsError::ArityNotWellformed(err) => {
                        write!(
                            f,
                            "arity not wellformed \n {}",
                            print_fail_tree(err, config)
                        )
                    }
                    ResIndDefsError::ConstructorNotWellFormed(err) => {
                        write!(f, "constructor not wellformed \n",)?;
                        for tree in err {
                            match tree {
                                Ok(tree) => {
                                    writeln!(f, "{}", print_tree(tree, config))?;
                                }
                                Err(tree) => {
                                    writeln!(f, "{}", print_fail_tree(tree, config))?;
                                }
                            }
                        }
                        Ok(())
                    }
                },
                NewInductiveResult::ErrOnSyntax(err) => write!(f, "{err}"),
                NewInductiveResult::ErrOnState(err) => write!(f, "{err}"),
            },
            CommandAllResult::ShowGoalResult(result) => match result {
                ShowGoalResult::Ok => write!(f, "show_goal ok"),
                ShowGoalResult::Pended(goals) => {
                    for goal in goals {
                        writeln!(f, " => {:?}", goal)?;
                    }
                    Ok(())
                }
            },
            CommandAllResult::ProveGoalResult(result) => match result {
                ProveGoalResult::Ok => write!(f, "prove_goal ok"),
                ProveGoalResult::NoNeedToProve => write!(f, "prove_goal no_need_to_prove"),
                ProveGoalResult::Err(tree) => {
                    write!(f, "prove_goal") //, print_fail_tree(tree, &TreeConfig::default()))
                }
            },
            CommandAllResult::AdmitResult(result) => match result {
                AdmitResult::Ok => write!(f, "admit ok"),
                AdmitResult::NoNeedToProve => write!(f, "admit no_need_to_prove"),
            },
            CommandAllResult::AdmitAllResult(result) => match result {
                AdmitAllResult::Ok => write!(f, "admit_all ok"),
                AdmitAllResult::NoNeedToProve => write!(f, "admit_all no_need_to_prove"),
            },
        }
    }
}

impl From<Admit> for CommandAll {
    fn from(command: Admit) -> Self {
        CommandAll::Admit(command)
    }
}

impl From<AdmitAll> for CommandAll {
    fn from(command: AdmitAll) -> Self {
        CommandAll::AdmitAll(command)
    }
}

impl From<AdmitResult> for CommandAllResult {
    fn from(result: AdmitResult) -> Self {
        CommandAllResult::AdmitResult(result)
    }
}

impl From<AdmitAllResult> for CommandAllResult {
    fn from(result: AdmitAllResult) -> Self {
        CommandAllResult::AdmitAllResult(result)
    }
}

impl From<ParseCommand> for CommandAll {
    fn from(command: ParseCommand) -> Self {
        CommandAll::ParseCommand(command)
    }
}

impl From<SubstCommand> for CommandAll {
    fn from(command: SubstCommand) -> Self {
        CommandAll::SubstCommand(command)
    }
}

impl From<AlphaEq> for CommandAll {
    fn from(command: AlphaEq) -> Self {
        CommandAll::AlphaEq(command)
    }
}

impl From<BetaEq> for CommandAll {
    fn from(command: BetaEq) -> Self {
        CommandAll::BetaEq(command)
    }
}

impl From<TopReduce> for CommandAll {
    fn from(command: TopReduce) -> Self {
        CommandAll::TopReduce(command)
    }
}

impl From<Reduce> for CommandAll {
    fn from(command: Reduce) -> Self {
        CommandAll::Reduce(command)
    }
}

impl From<Normalize> for CommandAll {
    fn from(command: Normalize) -> Self {
        CommandAll::Normalize(command)
    }
}

impl From<Check> for CommandAll {
    fn from(command: Check) -> Self {
        CommandAll::Check(command)
    }
}

impl From<Infer> for CommandAll {
    fn from(command: Infer) -> Self {
        CommandAll::Infer(command)
    }
}

impl From<NewDefinition> for CommandAll {
    fn from(command: NewDefinition) -> Self {
        CommandAll::NewDefinition(command)
    }
}

impl From<NewAssumption> for CommandAll {
    fn from(command: NewAssumption) -> Self {
        CommandAll::NewAssumption(command)
    }
}

impl From<NewInductive> for CommandAll {
    fn from(command: NewInductive) -> Self {
        CommandAll::NewInductive(command)
    }
}

impl From<ShowGoal> for CommandAll {
    fn from(command: ShowGoal) -> Self {
        CommandAll::ShowGoal(command)
    }
}

impl From<ProveGoal> for CommandAll {
    fn from(command: ProveGoal) -> Self {
        CommandAll::ProveGoal(command)
    }
}

impl From<ParseCommandResult> for CommandAllResult {
    fn from(result: ParseCommandResult) -> Self {
        CommandAllResult::ParseCommandResult(result)
    }
}

impl From<SubstCommandResult> for CommandAllResult {
    fn from(result: SubstCommandResult) -> Self {
        CommandAllResult::SubstCommandResult(result)
    }
}

impl From<AlphaEqResult> for CommandAllResult {
    fn from(result: AlphaEqResult) -> Self {
        CommandAllResult::AlphaEqResult(result)
    }
}

impl From<BetaEqResult> for CommandAllResult {
    fn from(result: BetaEqResult) -> Self {
        CommandAllResult::BetaEqResult(result)
    }
}

impl From<TopReduceResult> for CommandAllResult {
    fn from(result: TopReduceResult) -> Self {
        CommandAllResult::TopReduceResult(result)
    }
}

impl From<ReduceResult> for CommandAllResult {
    fn from(result: ReduceResult) -> Self {
        CommandAllResult::ReduceResult(result)
    }
}

impl From<NormalizeResult> for CommandAllResult {
    fn from(result: NormalizeResult) -> Self {
        CommandAllResult::NormalizeResult(result)
    }
}

impl From<CheckResult> for CommandAllResult {
    fn from(result: CheckResult) -> Self {
        CommandAllResult::CheckResult(result)
    }
}

impl From<InferResult> for CommandAllResult {
    fn from(result: InferResult) -> Self {
        CommandAllResult::InferResult(result)
    }
}

impl From<NewDefinitionResult> for CommandAllResult {
    fn from(result: NewDefinitionResult) -> Self {
        CommandAllResult::NewDefinitionResult(result)
    }
}

impl From<NewAssumptionResult> for CommandAllResult {
    fn from(result: NewAssumptionResult) -> Self {
        CommandAllResult::NewAssumptionResult(result)
    }
}

impl From<NewInductiveResult> for CommandAllResult {
    fn from(result: NewInductiveResult) -> Self {
        CommandAllResult::NewInductiveResult(result)
    }
}

impl From<ShowGoalResult> for CommandAllResult {
    fn from(result: ShowGoalResult) -> Self {
        CommandAllResult::ShowGoalResult(result)
    }
}

impl From<ProveGoalResult> for CommandAllResult {
    fn from(result: ProveGoalResult) -> Self {
        CommandAllResult::ProveGoalResult(result)
    }
}
