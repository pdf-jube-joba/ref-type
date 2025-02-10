use crate::{
    ast::{Exp, Var},
    context::{
        printing::{print_fail_tree, TreeConfig},
        DerivationFailed, GlobalContext, LocalContext, PartialDerivationTreeTypeCheck,
        ProvableJudgement,
    },
    lambda_calculus,
    parse::{check_inductive_syntax, InductiveDefinitionsSyntax},
    proving::{proof_tree, ErrProofTree, PartialDerivationTreeProof, UserSelect},
    typing::{type_check, type_infer},
};
use std::fmt::Display;

use self::command::{CommandAll, CommandAllResult};

pub mod command {
    use crate::context::{printing, ResIndDefsError, ResIndDefsOk};

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
        pub x: Var,
        pub t: Exp,
        pub e: Exp,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum NewDefinitionResult {
        Ok(PartialDerivationTreeTypeCheck),
        ErrOnTyping(DerivationFailed, TreeConfig),
        ErrOnState(InterpreterError, TreeConfig),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct NewAssumption {
        pub x: Var,
        pub t: Exp,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum NewAssumptionResult {
        Ok(PartialDerivationTreeTypeCheck),
        ErrOnTyping(DerivationFailed, TreeConfig),
        ErrOnState(InterpreterError, TreeConfig),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct NewInductive {
        pub inddefs: InductiveDefinitionsSyntax,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum NewInductiveResult {
        Ok(ResIndDefsOk),
        Err(ResIndDefsError),
        ErrOnSyntax(String),
        ErrOnState(InterpreterError),
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
                CommandAll::NewDefinition(NewDefinition { x, t, e }) => {
                    write!(f, "new_definition {} {} {}", x, t, e)
                }
                CommandAll::NewAssumption(NewAssumption { x, t }) => {
                    write!(f, "new_assumption {} {}", x, t)
                }
                CommandAll::NewInductive(NewInductive { inddefs }) => {
                    write!(f, "new_inductive {:?}", inddefs)
                }
            }
        }
    }

    impl Display for CommandAllResult {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                CommandAllResult::ParseCommandResult(ParseCommandResult {}) => write!(f, ""),
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
                        write!(f, "{}", printing::print_tree(tree, tree_config))
                    }
                    CheckResult::ErrOnTyping(tree, config) => {
                        write!(f, "{}", print_fail_tree(tree, config))
                    }
                    CheckResult::ErrOnState(err, config) => {
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
                    NewDefinitionResult::Ok(tree) => write!(f, "{:?}", tree),
                    NewDefinitionResult::ErrOnTyping(err, config) => {
                        write!(f, "{}", print_fail_tree(err, config))
                    }
                    NewDefinitionResult::ErrOnState(err, config) => {
                        write!(f, "{err}")
                    }
                },
                CommandAllResult::NewAssumptionResult(result) => match result {
                    NewAssumptionResult::Ok(tree) => write!(f, " {:?}", tree),
                    NewAssumptionResult::ErrOnTyping(err, config) => {
                        write!(f, "{}", print_fail_tree(err, config))
                    }
                    NewAssumptionResult::ErrOnState(err, config) => {
                        write!(f, "{err}")
                    }
                },
                CommandAllResult::NewInductiveResult(result) => match result {
                    NewInductiveResult::Ok(ok) => write!(f, " => {:?}", ok),
                    NewInductiveResult::Err(err) => write!(f, " => {:?}", err),
                    NewInductiveResult::ErrOnSyntax(err) => write!(f, "{err}"),
                    NewInductiveResult::ErrOnState(err) => write!(f, "{err}"),
                },
            }
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateInterpreter {
    NoGoal,
    Goals(Vec<GoalTree>), // it should be reversed order
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalTree {
    Node(ProvableJudgement),
    Branch(Vec<GoalTree>),
}

impl GoalTree {
    pub fn is_empty(&self) -> bool {
        match self {
            GoalTree::Node(_) => false,
            GoalTree::Branch(v) => v.iter().all(|goal| goal.is_empty()),
        }
    }
    pub fn first(&mut self) -> Option<&mut Self> {
        match self {
            GoalTree::Node(_) => Some(self),
            GoalTree::Branch(v) => v.first_mut().map(|goal| goal.first()).flatten(),
        }
    }
}

fn into_tree(v: Vec<ProvableJudgement>) -> Vec<GoalTree> {
    v.into_iter().map(GoalTree::Node).collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpreter {
    global_context: GlobalContext,
    state: StateInterpreter,
}

use command::*;

impl Interpreter {
    pub fn new(global_context: GlobalContext) -> Self {
        Self {
            global_context,
            state: StateInterpreter::NoGoal,
        }
    }
    pub fn command(&mut self, command: CommandAll) -> CommandAllResult {
        match command {
            CommandAll::ParseCommand(ParseCommand { exp }) => {
                CommandAllResult::ParseCommandResult(ParseCommandResult {})
            }
            CommandAll::SubstCommand(SubstCommand { e1, x, e2 }) => {
                let e = lambda_calculus::subst(e1.clone(), &x, &e2);
                CommandAllResult::SubstCommandResult(SubstCommandResult { e })
            }
            CommandAll::AlphaEq(AlphaEq { e1, e2, succ_flag }) => {
                let res = lambda_calculus::alpha_eq(&e1, &e2);
                CommandAllResult::AlphaEqResult(AlphaEqResult { eq: res })
            }
            CommandAll::BetaEq(BetaEq { e1, e2, succ_flag }) => {
                let res = lambda_calculus::beta_equiv(&self.global_context, e1.clone(), e2.clone());
                CommandAllResult::BetaEqResult(BetaEqResult { eq: res })
            }
            CommandAll::TopReduce(TopReduce { e }) => {
                let res = lambda_calculus::top_reduction(&self.global_context, e.clone());
                CommandAllResult::TopReduceResult(TopReduceResult { e: res })
            }
            CommandAll::Reduce(Reduce { e }) => {
                let res = lambda_calculus::reduce(&self.global_context, e.clone());
                CommandAllResult::ReduceResult(ReduceResult { e: res })
            }
            CommandAll::Normalize(Normalize { e }) => {
                let res = lambda_calculus::normalize_seq(&self.global_context, e.clone());
                CommandAllResult::NormalizeResult(NormalizeResult { es: res })
            }
            CommandAll::Check(Check { e1, e2, config }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::CheckResult(CheckResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        config,
                    ));
                }
                let res = type_check(&self.global_context, LocalContext::default(), e1, e2);

                let res = match res {
                    Ok(tree) => tree,
                    Err(err) => {
                        return CommandAllResult::CheckResult(CheckResult::ErrOnTyping(
                            err, config,
                        ));
                    }
                };

                let mut goals = res.get_goals();
                if goals.is_empty() {
                    self.state = StateInterpreter::NoGoal;
                } else {
                    goals.reverse();
                    self.state = StateInterpreter::Goals(into_tree(goals));
                }

                CommandAllResult::CheckResult(CheckResult::Ok(res, config))
            }
            CommandAll::Infer(Infer { e }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::InferResult(InferResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        TreeConfig::default(),
                    ));
                }
                let res = type_infer(&self.global_context, LocalContext::default(), e);

                match res {
                    Ok(tree) => {
                        let exp = tree.of_type().clone();
                        let mut goals = tree.get_goals();
                        if goals.is_empty() {
                            self.state = StateInterpreter::NoGoal;
                        } else {
                            goals.reverse();
                            self.state = StateInterpreter::Goals(into_tree(goals));
                        }
                        CommandAllResult::InferResult(InferResult::Ok(exp))
                    }
                    Err(err) => CommandAllResult::InferResult(InferResult::ErrOnTyping(
                        err,
                        TreeConfig::default(),
                    )),
                }
            }
            CommandAll::NewDefinition(NewDefinition { x, t, e }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NewDefinitionResult(NewDefinitionResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        TreeConfig::default(),
                    ));
                }
                let res = self.global_context.push_new_defs((x, t, e));
                match res {
                    Ok(tree) => {
                        CommandAllResult::NewDefinitionResult(NewDefinitionResult::Ok(tree))
                    }
                    Err(err) => CommandAllResult::NewDefinitionResult(
                        NewDefinitionResult::ErrOnTyping(err, TreeConfig::default()),
                    ),
                }
            }
            CommandAll::NewAssumption(NewAssumption { x, t }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NewAssumptionResult(NewAssumptionResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        TreeConfig::default(),
                    ));
                }
                let res = self.global_context.push_new_assum((x, t));
                match res {
                    Ok((tree, _sort)) => {
                        CommandAllResult::NewAssumptionResult(NewAssumptionResult::Ok(tree))
                    }
                    Err(err) => CommandAllResult::NewAssumptionResult(
                        NewAssumptionResult::ErrOnTyping(err, TreeConfig::default()),
                    ),
                }
            }
            CommandAll::NewInductive(NewInductive { inddefs }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NewInductiveResult(NewInductiveResult::ErrOnState(
                        InterpreterError::UnprovedState,
                    ));
                }
                let inddefs = match check_inductive_syntax(inddefs) {
                    Ok(inddefs) => inddefs,
                    Err(err) => {
                        return CommandAllResult::NewInductiveResult(
                            NewInductiveResult::ErrOnSyntax(err),
                        );
                    }
                };
                let res = self.global_context.push_new_ind(inddefs);
                match res {
                    Ok(ok) => CommandAllResult::NewInductiveResult(NewInductiveResult::Ok(ok)),
                    Err(err) => CommandAllResult::NewInductiveResult(NewInductiveResult::Err(err)),
                }
            }
        }
    }

    pub fn unproved_goals(&self) -> Vec<GoalTree> {
        match &self.state {
            StateInterpreter::NoGoal => vec![],
            StateInterpreter::Goals(goals) => goals.clone(),
        }
    }

    // pub fn accept_goal(
    //     &mut self,
    //     user_select: UserSelect,
    // ) -> Result<PartialDerivationTreeProof, either::Either<ErrProofTree, InterpreterError>> {
    //     let StateInterpreter::Goals(ref mut goals) = self.state else {
    //         return Err(InterpreterError::NoNeedToProve);
    //     };
    //     assert!(!goals.is_empty());

    //     let Some(goal) = goals.first_mut().unwrap().first() else {
    //         return Err(InterpreterError::NoNeedToProve);
    //     };
    //     let GoalTree::Node(ProvableJudgement {
    //         context,
    //         proposition,
    //     }) = goal
    //     else {
    //         unreachable!("first() should return Node");
    //     };
    //     let res = proof_tree(
    //         &self.global_context,
    //         context.clone(),
    //         proposition.clone(),
    //         user_select,
    //     );
    //     let added_goals = res.get_goals();
    //     if added_goals.is_empty() {
    //         goals.pop();
    //     } else {
    //         goals.push(GoalTree::Branch(into_tree(added_goals)));
    //     }
    //     Ok(res)
    // }
}
