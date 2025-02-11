use crate::{
    command::*,
    context::{
        printing::TreeConfig, DerivationFailed, GlobalContext, LocalContext,
        PartialDerivationTreeTypeCheck, ProvableJudgement,
    },
    lambda_calculus,
    parse::{check_inductive_syntax, InductiveDefinitionsSyntax},
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
            CommandAll::NewDefinition(NewDefinition { x, t, e, config }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NewDefinitionResult(NewDefinitionResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        TreeConfig::default(),
                    ));
                }
                let res = self.global_context.push_new_defs((x, t, e));
                match res {
                    Ok(tree) => {
                        CommandAllResult::NewDefinitionResult(NewDefinitionResult::Ok(tree, config))
                    }
                    Err(err) => CommandAllResult::NewDefinitionResult(
                        NewDefinitionResult::ErrOnTyping(err, TreeConfig::default()),
                    ),
                }
            }
            CommandAll::NewAssumption(NewAssumption { x, t, config }) => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NewAssumptionResult(NewAssumptionResult::ErrOnState(
                        InterpreterError::UnprovedState,
                        TreeConfig::default(),
                    ));
                }
                let res = self.global_context.push_new_assum((x, t));
                match res {
                    Ok((tree, _sort)) => {
                        CommandAllResult::NewAssumptionResult(NewAssumptionResult::Ok(tree, config))
                    }
                    Err(err) => CommandAllResult::NewAssumptionResult(
                        NewAssumptionResult::ErrOnTyping(err, TreeConfig::default()),
                    ),
                }
            }
            CommandAll::NewInductive(NewInductive { inddefs, config }) => {
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
                    Ok(ok) => {
                        CommandAllResult::NewInductiveResult(NewInductiveResult::Ok(ok, config))
                    }
                    Err(err) => {
                        CommandAllResult::NewInductiveResult(NewInductiveResult::Err(err, config))
                    }
                }
            }
            CommandAll::ShowGoal(_) => match &self.state {
                StateInterpreter::NoGoal => CommandAllResult::ShowGoalResult(ShowGoalResult::Ok),
                StateInterpreter::Goals(goals) => {
                    CommandAllResult::ShowGoalResult(ShowGoalResult::Pended(goals.clone()))
                }
            },
            CommandAll::ProveGoal(ProveGoal { user_select }) => {
                let StateInterpreter::Goals(ref mut goals) = self.state else {
                    return CommandAllResult::ProveGoalResult(ProveGoalResult::NoNeedToProve);
                };
                assert!(!goals.is_empty());

                let Some(goal) = goals.first_mut().unwrap().first() else {
                    return CommandAllResult::ProveGoalResult(ProveGoalResult::NoNeedToProve);
                };
                let GoalTree::Node(ProvableJudgement {
                    context,
                    proposition,
                }) = goal
                else {
                    unreachable!("first() should return Node");
                };
                let res = match proof_tree(
                    &self.global_context,
                    context.clone(),
                    proposition.clone(),
                    user_select,
                ) {
                    Ok(ok) => ok,
                    Err(err) => {
                        return CommandAllResult::ProveGoalResult(ProveGoalResult::Err(err));
                    }
                };
                let added_goals = res.get_goals();
                if added_goals.is_empty() {
                    goals.pop();
                } else {
                    goals.push(GoalTree::Branch(into_tree(added_goals)));
                }
                CommandAllResult::ProveGoalResult(ProveGoalResult::Ok)
            }
            CommandAll::Admit(_) => todo!(),
            CommandAll::AdmitAll(_) => todo!(),
        }
    }

    pub fn unproved_goals(&self) -> Vec<GoalTree> {
        match &self.state {
            StateInterpreter::NoGoal => vec![],
            StateInterpreter::Goals(goals) => goals.clone(),
        }
    }
}
