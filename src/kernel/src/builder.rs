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
    pub fn new_command(ctx: Context) -> Self {
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
                let head: FailHead = match &head {
                    Head::Check { term, ty } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: Some(ty.clone()),
                    },
                    Head::Infer { term } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: None,
                    },
                    Head::Prop => FailHead::ProofJudgement {
                        ctx: ctx.clone(),
                        prop: None,
                    },
                };
                Err(DerivationFail::Propagate(Box::new(
                    DerivationFailPropagate {
                        head,
                        premises: premises.clone(),
                        fail: err,
                        rule,
                        phase,
                        expect: expect.to_string(),
                    },
                )))
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
                let head = match &head {
                    Head::Check { term, ty } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: Some(ty.clone()),
                    },
                    Head::Infer { term } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: None,
                    },
                    Head::Prop => FailHead::ProofJudgement {
                        ctx: ctx.clone(),
                        prop: None,
                    },
                };
                Err(DerivationFail::Propagate(Box::new(
                    DerivationFailPropagate {
                        head,
                        premises: premises.clone(),
                        fail: err,
                        rule,
                        phase,
                        expect: expect.to_string(),
                    },
                )))
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
                let head = match &head {
                    Head::Check { term, ty } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: Some(ty.clone()),
                    },
                    Head::Infer { term } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: None,
                    },
                    Head::Prop => FailHead::ProofJudgement {
                        ctx: ctx.clone(),
                        prop: None,
                    },
                };
                Err(DerivationFail::Propagate(Box::new(
                    DerivationFailPropagate {
                        head,
                        premises: premises.clone(),
                        fail: err,
                        rule,
                        phase,
                        expect: expect.to_string(),
                    },
                )))
            }
        }
    }

    pub fn add_proof(
        &mut self,
        ctx: &Context,
        command: ProveCommandBy,
        as_solve: bool,
    ) -> Result<Exp, DerivationFail> {
        let derivation = prove_command(ctx, &command);
        match derivation {
            Ok(mut ok) => {
                let prop = ok.prop_of().unwrap().clone();
                if as_solve {
                    let ok_head = SuccessHead::Solve(rc::Rc::new(ok));
                    ok = DerivationSuccess {
                        head: ok_head,
                        premises: vec![],
                        generated_goals: vec![],
                        rule: "as solve".to_string(),
                        phase: "as solve".to_string(),
                        through: false,
                    };
                }
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
                let head = match &head {
                    Head::Check { term, ty } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: Some(ty.clone()),
                    },
                    Head::Infer { term } => FailHead::TypeJudgement {
                        ctx: ctx.clone(),
                        term: term.clone(),
                        ty: None,
                    },
                    Head::Prop => FailHead::ProofJudgement {
                        ctx: ctx.clone(),
                        prop: None,
                    },
                };
                Err(DerivationFail::Propagate(Box::new(
                    DerivationFailPropagate {
                        head,
                        premises: premises.clone(),
                        fail: err,
                        rule,
                        phase,
                        expect: "proof".to_string(),
                    },
                )))
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

        for premise in &self.premises {
            if let DerivationSuccess {
                head: SuccessHead::Solve(rc),
                ..
            } = premise
            {
                let goal_ctx = rc.ctx_of().unwrap().clone();
                let goal_prop = rc.prop_of().unwrap().clone();
                rcs.push((rc.clone(), goal_ctx, goal_prop));
            }
        }

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
                    let head = match &head {
                        Head::Check { term, ty } => FailHead::TypeJudgement {
                            ctx: ctx.clone(),
                            term: term.clone(),
                            ty: Some(ty.clone()),
                        },
                        Head::Infer { term } => FailHead::TypeJudgement {
                            ctx: ctx.clone(),
                            term: term.clone(),
                            ty: None,
                        },
                        Head::Prop => FailHead::ProofJudgement {
                            ctx: ctx.clone(),
                            prop: None,
                        },
                    };
                    return Err(DerivationFail::Caused(Box::new(DerivationFailCaused {
                        head,
                        premises,
                        rule,
                        phase,
                        cause: "no unproved goal found when solving".to_string(),
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
        let head = SuccessHead::TypeJudgement { ctx, term, ty };
        DerivationSuccess {
            head,
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
        let head = SuccessHead::TypeJudgement { ctx, term, ty };
        DerivationSuccess {
            head,
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
        let head = SuccessHead::TypeJudgement {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: Exp::Sort(sort),
        };
        DerivationSuccess {
            head,
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
        let head = SuccessHead::ProofJudgement {
            ctx: ctx.clone(),
            prop: prop.clone(),
        };
        DerivationSuccess {
            head,
            premises,
            generated_goals,
            rule,
            phase,
            through: false,
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
        let head = match &head {
            Head::Check { term, ty } => FailHead::TypeJudgement {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: Some(ty.clone()),
            },
            Head::Infer { term } => FailHead::TypeJudgement {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: None,
            },
            Head::Prop => FailHead::ProofJudgement {
                ctx: ctx.clone(),
                prop: None,
            },
        };
        DerivationFail::Caused(Box::new(DerivationFailCaused {
            head,
            premises,
            rule,
            phase,
            cause: cause.to_string(),
        }))
    }
}
