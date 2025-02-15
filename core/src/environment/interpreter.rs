use crate::{
    command::*,
    environment::{derivation_tree::*, global_context::*, inductive::*, tree_node::*},
    lambda_calculus,
    printing::*,
    proving::{proof_tree, PartialDerivationTreeProof},
    typing::{type_check, type_infer},
};

use super::{
    check_well_formed::{self, check_well_formedness_new_inddefs, ResIndDefsError, ResIndDefsOk},
    Exp, Sort,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateInterpreter {
    NoGoal,
    Goals(GoalTree), // it should be reversed order
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpreter {
    global_context: GlobalContext,
    state: StateInterpreter,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            global_context: GlobalContext::default(),
            state: StateInterpreter::NoGoal,
        }
    }
    pub fn set_goals_type_check(&mut self, tree: &PartialDerivationTreeTypeCheck) {
        let goals = tree.get_goals();
        if goals.is_empty() {
            self.state = StateInterpreter::NoGoal;
        } else {
            self.state = StateInterpreter::Goals(GoalTree::Branch(
                goals.into_iter().map(GoalTree::UnSolved).collect(),
            ));
        }
    }
    pub fn set_goals_proof_check(&mut self, tree: &PartialDerivationTreeProof) {
        let goals = tree.get_goals();
        if goals.is_empty() {
            self.state = StateInterpreter::NoGoal;
        } else {
            self.state = StateInterpreter::Goals(GoalTree::Branch(
                goals.into_iter().map(GoalTree::UnSolved).collect(),
            ));
        }
    }
    pub fn now_state(&self) -> &StateInterpreter {
        &self.state
    }
    pub fn command(
        &mut self,
        command: CommandAll,
    ) -> Result<CommandAllResultOk, CommandAllResultErr> {
        match command {
            CommandAll::ParseCommand { exp: _ } => Ok(CommandAllResultOk::ParseCommandResult),
            CommandAll::SubstCommand { e1, x, e2 } => {
                let e = lambda_calculus::subst(e1.clone(), &x, &e2);
                Ok(CommandAllResultOk::SubstCommandResult { e })
            }
            CommandAll::AlphaEq { e1, e2, succ_flag } => {
                let res = lambda_calculus::alpha_eq(&e1, &e2);
                if succ_flag == res {
                    Ok(CommandAllResultOk::AlphaEqResult {
                        expected: succ_flag,
                    })
                } else {
                    Err(CommandAllResultErr::AlphaEq {
                        expected: succ_flag,
                    })
                }
            }
            CommandAll::BetaEq { e1, e2, succ_flag } => {
                let res = lambda_calculus::beta_equiv(&self.global_context, e1.clone(), e2.clone());
                if succ_flag == res {
                    Ok(CommandAllResultOk::BetaEqResult {
                        expected: succ_flag,
                    })
                } else {
                    Err(CommandAllResultErr::BetaEq {
                        expected: succ_flag,
                    })
                }
            }
            CommandAll::TopReduce { e } => {
                let res = lambda_calculus::top_reduction(&self.global_context, e.clone());
                Ok(CommandAllResultOk::TopReduceResult { e: res })
            }
            CommandAll::Reduce { e } => {
                let res = lambda_calculus::reduce(&self.global_context, e.clone());
                Ok(CommandAllResultOk::ReduceResult { e: res })
            }
            CommandAll::Normalize { e } => {
                let res = lambda_calculus::normalize_seq(&self.global_context, e.clone());
                Ok(CommandAllResultOk::NormalizeResult { es: res })
            }
            CommandAll::Check { e1, e2, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
                }

                let res = type_check(&self.global_context, LocalContext::default(), e1, e2);

                let res = match res {
                    Ok(tree) => tree,
                    Err(err) => {
                        return Err(CommandAllResultErr::CheckFailed {
                            result: err,
                            config,
                        });
                    }
                };

                self.set_goals_type_check(&res);

                Ok(CommandAllResultOk::CheckResult {
                    result: res,
                    config,
                })
            }
            CommandAll::Infer { config, e } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
                }

                let res = type_infer(&self.global_context, LocalContext::default(), e);

                match res {
                    Ok(tree) => {
                        let exp = tree.of_type().clone();
                        self.set_goals_type_check(&tree);
                        Ok(CommandAllResultOk::InferResult {
                            result_exp: exp,
                            result_tree: tree,
                            config,
                        })
                    }
                    Err(err) => Err(CommandAllResultErr::InferFailed {
                        result: err,
                        config,
                    }),
                }
            }
            CommandAll::Theorem { e, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
                }

                match type_check(
                    &self.global_context,
                    LocalContext::default(),
                    e.clone(),
                    Exp::Sort(Sort::Prop),
                ) {
                    Ok(tree) => {
                        self.state =
                            StateInterpreter::Goals(GoalTree::UnSolved(ProvableJudgement {
                                context: LocalContext::default(),
                                proposition: e,
                            }));
                        Ok(CommandAllResultOk::TheoremIsProp {
                            result: tree,
                            config,
                        })
                    }
                    Err(err) => Err(CommandAllResultErr::TheoremIsNotProp {
                        result: err,
                        config,
                    }),
                }
            }
            CommandAll::NewDefinition { x, t, e, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
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
                        self.set_goals_type_check(&tree);
                        Ok(CommandAllResultOk::NewDefinitionResult {
                            result: tree,
                            config,
                        })
                    }
                    Err(err) => Err(CommandAllResultErr::NewDefinitionFailed {
                        result: err,
                        config,
                    }),
                }
            }
            CommandAll::NewAssumption { x, t, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
                }

                match check_well_formed::check_well_formedness_new_assmption(
                    &self.global_context,
                    LocalContext::default(),
                    x.clone(),
                    t.clone(),
                ) {
                    Ok(tree) => {
                        self.global_context.push_new_assum((x, t));
                        self.set_goals_type_check(&tree);
                        Ok(CommandAllResultOk::NewAssumptionResult {
                            result: tree,
                            config,
                        })
                    }
                    Err(err) => Err(CommandAllResultErr::NewAssumptionFailed {
                        result: err,
                        config,
                    }),
                }
            }
            CommandAll::NewInductive { inddefs, config } => {
                if self.state != StateInterpreter::NoGoal {
                    return Err(CommandAllResultErr::NotInCommandMode);
                }

                let inddefs = match IndTypeDefs::new(inddefs) {
                    Ok(inddefs) => inddefs,
                    Err(err) => {
                        return Err(CommandAllResultErr::NewInductiveFailed {
                            result: ResIndDefsError::SyntaxError(err),
                            config,
                        });
                    }
                };
                match check_well_formedness_new_inddefs(&self.global_context, inddefs.clone()) {
                    Ok(ok) => {
                        self.global_context.push_new_ind(inddefs);
                        let ResIndDefsOk {
                            arity_well_formed,
                            constructor_wellformed,
                        } = &ok;
                        self.set_goals_type_check(arity_well_formed);
                        for t in constructor_wellformed {
                            self.set_goals_type_check(t);
                        }
                        Ok(CommandAllResultOk::NewInductiveResult { result: ok, config })
                    }
                    Err(err) => Err(CommandAllResultErr::NewInductiveFailed {
                        result: err,
                        config,
                    }),
                }
            }
            CommandAll::ShowGoal => match &self.state {
                StateInterpreter::NoGoal => Ok(CommandAllResultOk::ShowGoalResult { goals: None }),
                StateInterpreter::Goals(goals) => Ok(CommandAllResultOk::ShowGoalResult {
                    goals: Some(goals.clone()),
                }),
            },
            CommandAll::ProveGoal { user_select } => {
                let StateInterpreter::Goals(ref mut goals) = self.state else {
                    return Err(CommandAllResultErr::NotInProofMode);
                };

                assert!(!goals.is_empty());

                let goal = goals.first_mut().unwrap();
                let GoalTree::UnSolved(ProvableJudgement {
                    context,
                    proposition,
                }) = goal
                else {
                    unreachable!()
                };

                let res = match proof_tree(
                    &self.global_context,
                    context.clone(),
                    proposition.clone(),
                    user_select,
                ) {
                    Ok(ok) => ok,
                    Err(err) => {
                        return Err(CommandAllResultErr::ProofErr {
                            result: err,
                            config: TreeConfig::OnlyGoals,
                        });
                    }
                };

                let added_goals = res.get_goals();
                *goal = GoalTree::Branch(added_goals.into_iter().map(GoalTree::UnSolved).collect());

                if goals.is_empty() {
                    println!("test");
                    self.state = StateInterpreter::NoGoal;
                }

                Ok(CommandAllResultOk::ProveGoalResult {
                    result: res,
                    config: TreeConfig::OnlyGoals,
                })
            }
            CommandAll::Admit => {
                let StateInterpreter::Goals(ref mut goals) = self.state else {
                    return Err(CommandAllResultErr::NotInProofMode);
                };

                assert!(!goals.is_empty());

                let goal = goals.first_mut().unwrap();
                let pred = std::mem::replace(goal, GoalTree::Branch(vec![]));
                let GoalTree::UnSolved(proof_judge) = pred else {
                    unreachable!()
                };

                if goals.is_empty() {
                    println!("test");
                    self.state = StateInterpreter::NoGoal;
                }

                Ok(CommandAllResultOk::AdmitResult { proof_judge })
            }
            CommandAll::AdmitAll => todo!(),
        }
    }

    pub fn unproved_goals(&self) -> Option<GoalTree> {
        match &self.state {
            StateInterpreter::NoGoal => None,
            StateInterpreter::Goals(goals) => Some(goals.clone()),
        }
    }
}
