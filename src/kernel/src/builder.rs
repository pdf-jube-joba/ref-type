// All judgement functions return a Derivation (the trace) plus a payload indicating success/value.
// ? for output value

use std::rc;

use crate::derivation::{check, infer, infer_sort, prove_command};

use crate::calculus::*;
use crate::exp::*;

// 許して
#[derive(Debug, Clone)]
pub struct Builder {
    ctx: Context,
    head: Head,
    premises: Vec<DerivationSuccess>,
    generated_goals: Vec<GoalGenerated>,
    rule: String,
    phase: String,
}

#[derive(Debug, Clone)]
enum Head {
    Check { term: Exp, ty: Exp },
    Infer { term: Exp },
    Prop,
}

impl Builder {
    pub fn new_check(ctx: Context, term: Exp, ty: Exp) -> Self {
        Builder {
            ctx,
            head: Head::Check {
                term: term.clone(),
                ty: ty.clone(),
            },
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "check".to_string(),
        }
    }
    pub fn new_infer(ctx: Context, term: Exp) -> Self {
        Builder {
            ctx,
            head: Head::Infer { term: term.clone() },
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "infer".to_string(),
        }
    }
    pub fn new_infersort(ctx: Context, ty: Exp) -> Self {
        Builder {
            ctx,
            head: Head::Infer { term: ty.clone() },
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "infer_sort".to_string(),
        }
    }
    pub fn new_prop(ctx: Context) -> Self {
        Builder {
            ctx,
            head: Head::Prop,
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "prop".to_string(),
        }
    }
    pub fn rule(&mut self, rule: &str) {
        self.rule = rule.to_string();
    }

    pub fn add_check(
        &mut self,
        ctx: &Context,
        term: &Exp,
        ty: &Exp,
        expect: &str, // message of "what we need"
    ) -> Result<(), DerivationFail> {
        let derivation = check(ctx, term, ty);
        match derivation {
            Ok(ok) => {
                self.premises.push(ok);
                Ok(())
            }
            Err(err) => {
                assert!(self.generated_goals.is_empty());
                let Builder {
                    ctx,
                    head,
                    premises,
                    generated_goals: _,
                    rule,
                    phase,
                } = self.clone();
                Err(match head {
                    Head::Check { term, ty } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: Some(ty),
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Infer { term } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Prop => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::ProofJudgement {
                            ctx,
                            prop: Some(ty.clone()),
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                })
            }
        }
    }
    pub fn add_infer(
        &mut self,
        ctx: &Context,
        term: &Exp,
        expect: &str,
    ) -> Result<Exp, DerivationFail> {
        let derivation = infer(ctx, term);
        match derivation {
            Ok(ok) => {
                let ty = ok.type_of().unwrap().clone();
                self.premises.push(ok);
                Ok(ty)
            }
            Err(err) => {
                assert!(self.generated_goals.is_empty());
                let Builder {
                    ctx,
                    head,
                    premises,
                    generated_goals: _,
                    rule,
                    phase,
                } = self.clone();
                Err(match head {
                    Head::Check { term, ty } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: Some(ty.clone()),
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Infer { term } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Prop => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::ProofJudgement {
                            ctx,
                            prop: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                })
            }
        }
    }
    pub fn add_sort(
        &mut self,
        ctx: &Context,
        ty: &Exp,
        expect: &str,
    ) -> Result<Sort, DerivationFail> {
        let derivation = infer_sort(ctx, ty);
        match derivation {
            Ok(ok) => {
                let Exp::Sort(s) = ok.type_of().unwrap().clone() else {
                    unreachable!("infer_sort must return a sort type if success");
                };
                self.premises.push(ok);
                Ok(s)
            }
            Err(err) => {
                assert!(self.generated_goals.is_empty());
                let Builder {
                    ctx,
                    head,
                    premises,
                    generated_goals: _,
                    rule,
                    phase,
                } = self.clone();
                Err(match head {
                    Head::Check { term, ty } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: Some(ty.clone()),
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Infer { term } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                    Head::Prop => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::ProofJudgement {
                            ctx,
                            prop: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: expect.to_string(),
                        },
                    )),
                })
            }
        }
    }

    pub fn add_proof(
        &mut self,
        ctx: &Context,
        command: ProveCommandBy,
    ) -> Result<Exp, DerivationFail> {
        let derivation = prove_command(ctx, &command);
        match derivation {
            Ok(ok) => {
                let prop = ok.prop_of().unwrap().clone();
                self.premises.push(ok);
                Ok(prop)
            }
            Err(err) => {
                assert!(self.generated_goals.is_empty());
                let Builder {
                    ctx,
                    head,
                    premises,
                    generated_goals: _,
                    rule,
                    phase,
                } = self.clone();
                Err(match head {
                    Head::Check { term, ty } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: Some(ty.clone()),
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: "a proof".to_string(),
                        },
                    )),
                    Head::Infer { term } => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::TypeJudgement {
                            ctx,
                            term,
                            ty: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: "a proof".to_string(),
                        },
                    )),
                    Head::Prop => DerivationFail::Propagate(Box::new(
                        DerivationFailPropagate::ProofJudgement {
                            ctx,
                            prop: None,
                            premises: premises.clone(),
                            fail: err,
                            rule,
                            phase,
                            expect: "a proof".to_string(),
                        },
                    )),
                })
            }
        }
    }

    pub fn add_unproved_goal(&mut self, ctx: Context, proposition: Exp) {
        self.generated_goals.push(GoalGenerated {
            ctx,
            proposition,
            solvetree: None,
        });
    }

    pub fn resolve_goal(&mut self) -> Result<(), DerivationFail> {
        let mut rcs = vec![];
        let mut premises = vec![];
        let mut rc_premised = vec![];

        for premise in self.premises.drain(..) {
            if let DerivationSuccess::ProofJudgement { ctx, prop, .. } = &premise {
                let (ctx, prop) = (ctx.clone(), prop.clone());
                let rc = rc::Rc::new(premise);
                rcs.push((rc.clone(), ctx, prop));
                rc_premised.push(DerivationSuccess::Solve(rc));
            } else {
                premises.push(premise);
            }
        }

        self.premises = premises;

        for (rc, ctx, prop) in rcs {
            let first_goal = self
                .premises
                .iter_mut()
                .find_map(|der| der.first_unproved_mut());
            match first_goal {
                Some(goal) => {
                    if exp_is_alpha_eq_under_ctx(&goal.ctx, &goal.proposition, &ctx, &prop) {
                        goal.solvetree = Some(rc);
                    } else {
                        return Err(self
                            .clone()
                            .cause("unproved goal found, but proposition mismatch"));
                    }
                }
                None => {
                    // error, no unproved goal found => DerivationFail::Caused
                    let Builder {
                        ctx,
                        head,
                        premises,
                        generated_goals: _,
                        rule,
                        phase,
                    } = self.clone();
                    return Err(DerivationFail::Caused(Box::new(match head {
                        Head::Check { term, ty } => DerivationFailCaused::TypeJudgement {
                            ctx,
                            term,
                            ty: Some(ty),
                            premises,
                            cause: "no unproved goal found when solving".to_string(),
                            rule,
                            phase,
                        },
                        Head::Infer { term } => DerivationFailCaused::TypeJudgement {
                            ctx,
                            term,
                            ty: None,
                            premises,
                            cause: "no unproved goal found when solving".to_string(),
                            rule,
                            phase,
                        },
                        Head::Prop => DerivationFailCaused::ProofJudgement {
                            ctx,
                            prop: None,
                            premises,
                            cause: "no unproved goal found when solving".to_string(),
                            rule,
                            phase,
                        },
                    })));
                }
            }
        }
        todo!()
    }

    pub fn build_check(self, through: bool) -> DerivationSuccess {
        let Builder {
            ctx,
            head,
            premises,
            generated_goals,
            rule,
            phase,
        } = self;
        let Head::Check { term, ty } = head else {
            unreachable!("head must be Check in build_check")
        };
        DerivationSuccess::TypeJudgement {
            ctx,
            term,
            ty,
            premises,
            generated_goals,
            rule,
            phase,
            through,
        }
    }
    pub fn build_infer(self, ty: Exp) -> DerivationSuccess {
        let Builder {
            ctx,
            head,
            premises,
            generated_goals,
            rule,
            phase,
        } = self;
        let Head::Infer { term } = head else {
            unreachable!("head must be Infer in build_infer")
        };
        DerivationSuccess::TypeJudgement {
            ctx,
            term,
            ty,
            premises,
            generated_goals,
            rule,
            phase,
            through: false,
        }
    }
    pub fn build_sort(self, sort: Sort, through: bool) -> DerivationSuccess {
        let Builder {
            ctx,
            head,
            premises,
            generated_goals,
            rule,
            phase,
        } = self;
        let Head::Infer { term } = head else {
            unreachable!("head must be Infer in build_sort")
        };
        DerivationSuccess::TypeJudgement {
            ctx,
            term,
            ty: Exp::Sort(sort),
            premises,
            generated_goals,
            rule,
            phase,
            through,
        }
    }
    pub fn build_prop(self, prop: Exp) -> DerivationSuccess {
        let Builder {
            ctx,
            head,
            premises,
            generated_goals,
            rule,
            phase,
        } = self;
        let Head::Prop = head else {
            unreachable!("head must be Prop in build_prop")
        };
        DerivationSuccess::ProofJudgement {
            ctx,
            prop,
            premises,
            generated_goals,
            rule,
            phase,
        }
    }
    pub fn cause(self, cause: &str) -> DerivationFail {
        let Builder {
            ctx,
            head,
            premises,
            generated_goals,
            rule,
            phase,
        } = self;
        assert!(generated_goals.is_empty());
        DerivationFail::Caused(Box::new(match head {
            Head::Check { term, ty } => DerivationFailCaused::TypeJudgement {
                ctx,
                term,
                ty: Some(ty),
                premises,
                cause: cause.to_string(),
                rule,
                phase,
            },
            Head::Infer { term } => DerivationFailCaused::TypeJudgement {
                ctx,
                term,
                ty: None,
                premises,
                cause: cause.to_string(),
                rule,
                phase,
            },
            Head::Prop => DerivationFailCaused::ProofJudgement {
                ctx,
                prop: None,
                premises,
                cause: cause.to_string(),
                rule,
                phase,
            },
        }))
    }
}
