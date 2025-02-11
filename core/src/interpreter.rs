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
            CommandAll::ParseCommand { exp } => CommandAllResult::ParseCommandResult,
            CommandAll::SubstCommand { e1, x, e2 } => {
                let e = lambda_calculus::subst(e1.clone(), &x, &e2);
                CommandAllResult::SubstCommandResult { e }
            }
            CommandAll::AlphaEq { e1, e2, succ_flag } => {
                let res = lambda_calculus::alpha_eq(&e1, &e2);
                CommandAllResult::AlphaEqResult { eq: res }
            }
            CommandAll::BetaEq { e1, e2, succ_flag } => {
                let res = lambda_calculus::beta_equiv(&self.global_context, e1.clone(), e2.clone());
                CommandAllResult::BetaEqResult { eq: res }
            }
            CommandAll::TopReduce { e } => {
                let res = lambda_calculus::top_reduction(&self.global_context, e.clone());
                CommandAllResult::TopReduceResult { e: res }
            }
            CommandAll::Reduce { e } => {
                let res = lambda_calculus::reduce(&self.global_context, e.clone());
                CommandAllResult::ReduceResult { e: res }
            }
            CommandAll::Normalize { e } => {
                let res = lambda_calculus::normalize_seq(&self.global_context, e.clone());
                CommandAllResult::NormalizeResult { es: res }
            }
            CommandAll::Check { e1, e2, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NeedProve;
                }
                let res = type_check(&self.global_context, LocalContext::default(), e1, e2);

                let res = match res {
                    Ok(tree) => tree,
                    Err(err) => {
                        return CommandAllResult::CheckResult {
                            result: Err(err),
                            config,
                        };
                    }
                };

                let mut goals = res.get_goals();
                if goals.is_empty() {
                    self.state = StateInterpreter::NoGoal;
                } else {
                    goals.reverse();
                    self.state = StateInterpreter::Goals(into_tree(goals));
                }

                CommandAllResult::CheckResult {
                    result: Ok(res),
                    config,
                }
            }
            CommandAll::Infer { e } => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NeedProve;
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
                        CommandAllResult::InferResult {
                            result: Ok(exp),
                            config: TreeConfig::default(),
                        }
                    }
                    Err(err) => CommandAllResult::InferResult {
                        result: Err(err),
                        config: TreeConfig::default(),
                    },
                }
            }
            CommandAll::NewDefinition { x, t, e, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NeedProve;
                }
                let res = self.global_context.push_new_defs((x, t, e));
                match res {
                    Ok(tree) => CommandAllResult::NewDefinitionResult {
                        result: Ok(tree),
                        config,
                    },
                    Err(err) => CommandAllResult::NewDefinitionResult {
                        result: Err(err),
                        config: TreeConfig::default(),
                    },
                }
            }
            CommandAll::NewAssumption { x, t, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NeedProve;
                }
                let res = self.global_context.push_new_assum((x, t));
                match res {
                    Ok((tree, _sort)) => CommandAllResult::NewAssumptionResult {
                        result: Ok(tree),
                        config,
                    },
                    Err(err) => CommandAllResult::NewAssumptionResult {
                        result: Err(err),
                        config: TreeConfig::default(),
                    },
                }
            }
            CommandAll::NewInductive { inddefs, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return CommandAllResult::NeedProve;
                }
                let inddefs = match check_inductive_syntax(inddefs) {
                    Ok(inddefs) => inddefs,
                    Err(err) => {
                        return CommandAllResult::NewInductiveResult {
                            result: Err(ResIndDefsError::SyntaxError(err)),
                            config,
                        };
                    }
                };
                let res = self.global_context.push_new_ind(inddefs);
                match res {
                    Ok(ok) => CommandAllResult::NewInductiveResult {
                        result: Ok(ok),
                        config,
                    },
                    Err(err) => CommandAllResult::NewInductiveResult {
                        result: Err(err),
                        config,
                    },
                }
            }
            CommandAll::ShowGoal => match &self.state {
                StateInterpreter::NoGoal => CommandAllResult::ShowGoalResult {
                    result: Ok(()),
                    goals: None,
                },
                StateInterpreter::Goals(goals) => CommandAllResult::ShowGoalResult {
                    result: Ok(()),
                    goals: Some(goals.clone()),
                },
            },
            CommandAll::ProveGoal { user_select } => {
                let StateInterpreter::Goals(ref mut goals) = self.state else {
                    return CommandAllResult::ProveGoalResult {
                        result: Err(ErrProofTree::NoNeedToProve),
                    };
                };
                assert!(!goals.is_empty());

                let Some(goal) = goals.first_mut().unwrap().first() else {
                    return CommandAllResult::ProveGoalResult {
                        result: Err(ErrProofTree::NoNeedToProve),
                    };
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
                        return CommandAllResult::ProveGoalResult { result: Err(err) };
                    }
                };
                let added_goals = res.get_goals();
                if added_goals.is_empty() {
                    goals.pop();
                } else {
                    goals.push(GoalTree::Branch(into_tree(added_goals)));
                }
                CommandAllResult::ProveGoalResult { result: Ok(()) }
            }
            CommandAll::Admit => todo!(),
            CommandAll::AdmitAll => todo!(),
        }
    }

    pub fn unproved_goals(&self) -> Vec<GoalTree> {
        match &self.state {
            StateInterpreter::NoGoal => vec![],
            StateInterpreter::Goals(goals) => goals.clone(),
        }
    }
}
