use crate::{
    ast::inductives::*,
    command::*,
    environment::{
        derivation_tree::*, derivation_tree::*, global_context::*, inductive::*, printing::*,
        tree_node::*,
    },
    lambda_calculus,
    proving::{proof_tree, ErrProofTree, PartialDerivationTreeProof, UserSelect},
    typing::{type_check, type_infer},
};

use super::check_well_formed::{self, check_well_formedness_new_inddefs, ResIndDefsError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateInterpreter {
    NoGoal,
    Goals(Vec<GoalTree>), // it should be reversed order
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

                match check_well_formed::check_well_formedness_new_definition(
                    &self.global_context,
                    LocalContext::default(),
                    x.clone(),
                    t.clone(),
                    e.clone(),
                ) {
                    Ok(tree) => {
                        self.global_context.push_new_defs((x, t, e));
                        CommandAllResult::NewDefinitionResult {
                            result: Ok(tree),
                            config,
                        }
                    }
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

                match check_well_formed::check_well_formedness_new_assmption(
                    &self.global_context,
                    LocalContext::default(),
                    x.clone(),
                    t.clone(),
                ) {
                    Ok(tree) => {
                        self.global_context.push_new_assum((x, t));
                        CommandAllResult::NewAssumptionResult {
                            result: Ok(tree),
                            config,
                        }
                    }
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
                let inddefs = match IndTypeDefs::new(inddefs) {
                    Ok(inddefs) => inddefs,
                    Err(err) => {
                        return CommandAllResult::NewInductiveResult {
                            result: Err(ResIndDefsError::SyntaxError(err)),
                            config,
                        };
                    }
                };
                match check_well_formedness_new_inddefs(
                    &self.global_context,
                    LocalContext::default(),
                    inddefs.clone(),
                ) {
                    Ok(ok) => {
                        self.global_context.push_new_ind(inddefs);
                        CommandAllResult::NewInductiveResult {
                            result: Ok(ok),
                            config,
                        }
                    }
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
                    return CommandAllResult::NoNeedProve;
                };
                assert!(!goals.is_empty());

                let goal = goals.first_mut().unwrap().first().unwrap();
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
