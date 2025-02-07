use crate::{
    ast::Exp,
    context::{
        DerivationFailed, GlobalContext, LocalContext, PartialDerivationTreeTypeCheck,
        ProvableJudgement,
    },
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

impl GoalTree {
    fn is_empty(&self) -> bool {
        match self {
            GoalTree::Node(_) => false,
            GoalTree::Branch(v) => v.iter().all(|goal| goal.is_empty()),
        }
    }
    fn first(&mut self) -> Option<&mut Self> {
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
