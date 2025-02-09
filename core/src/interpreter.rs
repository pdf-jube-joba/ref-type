use std::fmt::Display;

use crate::{
    ast::{Exp, Var},
    context::{
        printing::TreeConfig, DerivationFailed, GlobalContext, LocalContext,
        PartialDerivationTreeTypeCheck, ProvableJudgement,
    },
    lambda_calculus,
    parse::InductiveDefinitionsSyntax,
    proving::{proof_tree, ErrProofTree, PartialDerivationTreeProof, UserSelect},
    typing::{type_check, type_infer},
};

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    Parse(Exp),
    LambdaCommand(LambdaCommand),
    TypingCommand(TypingCommand, bool, TreeConfig),
    NewCommand(NewCommand, bool, TreeConfig),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LambdaCommand {
    Subst(Exp, Var, Exp),
    AlphaEq(Exp, Exp, bool),
    Reduce(Exp),
    TopReduce(Exp),
    Normalize(Exp),
    BetaEq(Exp, Exp, bool),
}

impl Display for LambdaCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LambdaCommand::Subst(e1, x, e2) => write!(f, "subst ({}) {} ({})", e1, x, e2),
            LambdaCommand::AlphaEq(e1, e2, b) => write!(f, "alpha_eq ({}) ({})", e1, e2),
            LambdaCommand::Reduce(e) => write!(f, "reduce ({})", e),
            LambdaCommand::TopReduce(e) => write!(f, "top_reduce ({})", e),
            LambdaCommand::Normalize(e) => write!(f, "normalize ({})", e),
            LambdaCommand::BetaEq(e1, e2, b) => write!(f, "beta_eq ({}) ({})", e1, e2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LambdaCommandResult {
    Subst(Exp),
    AlphaEq(bool),
    TopReduce(Option<Exp>),
    Reduce(Option<Exp>),
    Normalize(Vec<Exp>),
    BetaEq(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypingCommand {
    Check(Exp, Exp),
    Infer(Exp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewCommand {
    Definition(Var, Exp, Exp),
    Assumption(Var, Exp),
    Inductive(InductiveDefinitionsSyntax),
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
pub enum InterpreterError {
    UnprovedState,
    DerivationFailed(DerivationFailed),
    NoNeedToProve,
    ErrProofTree(ErrProofTree),
}

impl From<DerivationFailed> for InterpreterError {
    fn from(e: DerivationFailed) -> Self {
        InterpreterError::DerivationFailed(e)
    }
}

impl From<ErrProofTree> for InterpreterError {
    fn from(e: ErrProofTree) -> Self {
        InterpreterError::ErrProofTree(e)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpreter {
    global_context: GlobalContext,
    state: StateInterpreter,
}

impl Interpreter {
    pub fn new(global_context: GlobalContext) -> Self {
        Self {
            global_context,
            state: StateInterpreter::NoGoal,
        }
    }
    pub fn command(&mut self, command: Command) {
        todo!()
    }
    pub fn lambda_command(&self, lambda_command: LambdaCommand) -> LambdaCommandResult {
        match lambda_command {
            LambdaCommand::Subst(e1, x, e2) => {
                let e = lambda_calculus::subst(e1.clone(), &x, &e2);
                LambdaCommandResult::Subst(e)
            }
            LambdaCommand::AlphaEq(e1, e2, b) => {
                let res = lambda_calculus::alpha_eq(&e1, &e2);
                LambdaCommandResult::AlphaEq(res)
            }
            LambdaCommand::TopReduce(term) => {
                let res = lambda_calculus::top_reduction(&self.global_context, term.clone());
                LambdaCommandResult::TopReduce(res)
            }
            LambdaCommand::Reduce(term) => {
                let res = lambda_calculus::reduce(&self.global_context, term.clone());
                LambdaCommandResult::Reduce(res)
            }
            LambdaCommand::Normalize(term) => {
                let res = lambda_calculus::normalize_seq(&self.global_context, term.clone());
                LambdaCommandResult::Normalize(res)
            }
            LambdaCommand::BetaEq(e1, e2, b) => {
                let res = lambda_calculus::beta_equiv(&self.global_context, e1.clone(), e2.clone());
                LambdaCommandResult::BetaEq(res)
            }
        }
    }
    pub fn typing_command(
        &mut self,
        typing_command: TypingCommand,
    ) -> Result<PartialDerivationTreeTypeCheck, InterpreterError> {
        match typing_command {
            TypingCommand::Check(e1, e2) => self.type_check(e1, e2),
            TypingCommand::Infer(e1) => self.type_infer(e1),
        }
    }
    pub fn new_command(
        &mut self,
        new_command: NewCommand,
    ) -> Result<PartialDerivationTreeTypeCheck, InterpreterError> {
        todo!()
    }
    pub fn unproved_goals(&self) -> Vec<GoalTree> {
        match &self.state {
            StateInterpreter::NoGoal => vec![],
            StateInterpreter::Goals(goals) => goals.clone(),
        }
    }
    pub fn type_check(
        &mut self,
        term1: Exp,
        expected: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, InterpreterError> {
        if self.state != StateInterpreter::NoGoal {
            return Err(InterpreterError::UnprovedState);
        }

        let res = type_check(
            &self.global_context,
            LocalContext::default(),
            term1,
            expected,
        )?;

        let mut goals = res.get_goals();
        if goals.is_empty() {
            self.state = StateInterpreter::NoGoal;
        } else {
            goals.reverse();
            self.state = StateInterpreter::Goals(into_tree(goals));
        }
        Ok(res)
    }

    pub fn type_infer(
        &mut self,
        term1: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, InterpreterError> {
        if self.state != StateInterpreter::NoGoal {
            return Err(InterpreterError::UnprovedState);
        }

        let res = type_infer(&self.global_context, LocalContext::default(), term1)?;

        let mut goals = res.get_goals();
        if goals.is_empty() {
            self.state = StateInterpreter::NoGoal;
        } else {
            goals.reverse();
            self.state = StateInterpreter::Goals(into_tree(goals));
        }
        Ok(res)
    }
    pub fn accept_goal(
        &mut self,
        user_select: UserSelect,
    ) -> Result<PartialDerivationTreeProof, InterpreterError> {
        let StateInterpreter::Goals(ref mut goals) = self.state else {
            return Err(InterpreterError::NoNeedToProve);
        };
        assert!(!goals.is_empty());

        let Some(goal) = goals.first_mut().unwrap().first() else {
            return Err(InterpreterError::NoNeedToProve);
        };
        let GoalTree::Node(ProvableJudgement {
            context,
            proposition,
        }) = goal
        else {
            unreachable!("first() should return Node");
        };
        let res = proof_tree(
            &self.global_context,
            context.clone(),
            proposition.clone(),
            user_select,
        )?;
        let added_goals = res.get_goals();
        if added_goals.is_empty() {
            goals.pop();
        } else {
            goals.push(GoalTree::Branch(into_tree(added_goals)));
        }
        Ok(res)
    }
}
