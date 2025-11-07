// All judgement functions return a Derivation (the trace) plus a payload indicating success/value.
// ? for output value

use std::rc::Rc;

use crate::inductive::eliminator_type;
use crate::utils;

use crate::calculus::*;
use crate::exp::*;

// 許して
#[derive(Debug, Clone)]
struct Builder {
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
    fn new_check(ctx: Context, term: Exp, ty: Exp) -> Self {
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
    fn new_infer(ctx: Context, term: Exp) -> Self {
        Builder {
            ctx,
            head: Head::Infer { term: term.clone() },
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "infer".to_string(),
        }
    }
    fn new_prop(ctx: Context) -> Self {
        Builder {
            ctx,
            head: Head::Prop,
            premises: vec![],
            generated_goals: vec![],
            rule: "".to_string(),
            phase: "prop".to_string(),
        }
    }
    fn rule(&mut self, rule: &str) {
        self.rule = rule.to_string();
    }

    fn add_check(
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
    fn add_infer(
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
    fn add_sort(&mut self, ctx: &Context, ty: &Exp, expect: &str) -> Result<Sort, DerivationFail> {
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

    fn add_unproved_goal(&mut self, ctx: Context, proposition: Exp) {
        self.generated_goals.push(GoalGenerated {
            ctx,
            proposition,
            solvetree: None,
        });
    }

    fn solve(mut self, solve_goal: DerivationSuccess) -> Result<Self, DerivationFail> {
        assert!(matches!(
            solve_goal,
            DerivationSuccess::ProofJudgement { .. }
        ));
        let rc = Rc::new(solve_goal);
        self.premises.push(DerivationSuccess::Solve(rc.clone()));
        let first_goal = self
            .premises
            .iter_mut()
            .find_map(|der| der.first_unproved_mut());
        match first_goal {
            Some(goal) => {
                goal.solvetree = Some(rc);
                Ok(self)
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
                } = self;
                Err(DerivationFail::Caused(Box::new(match head {
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
                })))
            }
        }
    }

    fn build_check(self, through: bool) -> DerivationSuccess {
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
    fn build_infer(self, ty: Exp) -> DerivationSuccess {
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
    fn build_sort(self, sort: Sort) -> DerivationSuccess {
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
            through: false,
        }
    }
    fn build_prop(self, prop: Exp) -> DerivationSuccess {
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
    fn cause(self, cause: &str) -> DerivationFail {
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

// return (ctx |- term: ty), result is in derivation.node.res
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new_check(ctx.clone(), term.clone(), ty.clone());

    // 1. infer (ctx |- term : ?inferred_ty)
    let inferred_ty = builder.add_infer(ctx, term, "infer given term")?;

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if exp_strict_equivalence(ty, &inferred_ty) {
        return Ok(builder.build_check(true));
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let _sort = builder.add_sort(ctx, ty, "infer given")?;

    // 3 get normal(inferred_ty) & normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        return Ok(builder.build_check(false));
    }

    // 3-B-if inferred_ty == s1, ty == s2 ... lift universe rule
    if let (Exp::Sort(s1), Exp::Sort(s2)) = (&inferred_ty_result, &ty) {
        builder.rule("UniverseLift");
        if s1.can_lift_to(*s2) {
            return Ok(builder.build_check(false));
        } else {
            // if inferred_ty == s1, ty == s2 with s1 not liftable to s2 ... fails
            return Err(builder.cause("fail universe lift"));
        }
    }

    // 3-C-if check inferred_ty =(alpha)= TypeLift(ty, some) ... inferred_ty < ty
    // conclude (ctx |- term : ty) by subset weak rule
    if let Exp::TypeLift {
        superset,
        subset: _,
    } = &inferred_ty_result
    {
        builder.rule("SubsetWeak");
        if exp_is_alpha_eq(superset.as_ref(), &ty) {
            return Ok(builder.build_check(false));
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return Err(builder.cause("fail subset weak"));
        }
    }

    // 3-D-if ty =(alpha)= TypeLift(inferred_ty, subset) ... ty < inferred_ty
    // conclude (ctx |- term : ty) by subset strong rule if one can prove (ctx |= Pred(inferred_ty, subset, term))
    if let Exp::TypeLift { superset, subset } = &ty {
        builder.rule("SubsetStrong");
        if exp_is_alpha_eq(superset.as_ref(), &inferred_ty_result) {
            // add goal (ctx |= Pred(inferred_ty, subset, term))
            builder.add_unproved_goal(
                ctx.clone(),
                Exp::Pred {
                    superset: Box::new(inferred_ty_result),
                    subset: subset.clone(),
                    element: Box::new(term.clone()),
                },
            );
            return Ok(builder.build_check(false));
        } else {
            // if ty =(alpha)= TypeLift(ty1, some) with ty1 != inferred_ty ... fails
            return Err(builder.cause("fail subset strong"));
        }
    }

    // 4. fails
    Err(builder.cause("ty, inferred_ty not convertible"))
}

// infer: (Derivation, Option<Exp>) where Option<Exp> = Some(ty) on success
pub fn infer(ctx: &Context, term: &Exp) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new_infer(ctx.clone(), term.clone());

    match term {
        Exp::Sort(sort) => {
            builder.rule("Sort");

            // 1. conclude (ctx |- s : ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    Ok(builder.build_infer(ty))
                }
                None => Err(builder.cause("no sort of sort found")),
            }
        }
        Exp::Var(index) => {
            builder.rule("Var");

            // 1. conclude (ctx |- var : ?ty) where (var: ty) in ctx
            match ctx_get(ctx, index) {
                Some(ty) => Ok(builder.build_infer(ty.clone())),
                None => Err(builder.cause("var not found")),
            }
        }
        Exp::Prod { var, ty, body } => {
            builder.rule("Prod");

            // 1) infer (ctx |- ty : ?s1)
            let s1 = builder.add_sort(ctx, ty, "infer domain sort for product")?;

            // 2) infer (ctx, (var, ty) |- body : ?s2)
            let extend = ctx_extend(ctx, (var.clone(), *(*ty).clone()));
            let s2 = builder.add_sort(&extend, body, "infer codomain sort for product")?;

            // 3) (s1, s2) から product sort s3 を得る
            match s1.relation_of_sort(s2) {
                Some(s3) => Ok(builder.build_infer(Exp::Sort(s3))),
                None => Err(builder.cause("no (s1, s2, s3) relation for product")),
            }
        }
        Exp::Lam { var, ty, body } => {
            builder.rule("Lam");

            // 1. infer (ctx |- ty : ?s) for some sort s
            let _sort = builder.add_sort(ctx, ty, "infer domain sort for lambda")?;

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let body_ty = builder.add_infer(&extend, body, "infer body type for lambda")?;

            // 3. conclude (ctx |- Lam(var, ty, body) : lam_ty)
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            Ok(builder.build_infer(lam_ty))
        }
        Exp::App { func, arg } => {
            builder.rule("App");

            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let func_ty = builder.add_infer(ctx, func, "infer function type for application")?;
            let Exp::Prod {
                var,
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return Err(builder.cause("type is not a product"));
            };

            // 2. check (ctx |- arg : arg_ty)
            builder.add_check(ctx, arg, &arg_ty, "check argument type for application")?;

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            let ret_ty_substituted = exp_subst(&ret_ty, &var, arg);
            Ok(builder.build_infer(ret_ty_substituted))
        }
        Exp::IndType {
            indspec,
            parameters,
        } => {
            builder.rule("IndType");

            let parameter_indty_defined = indspec.parameters.clone();

            // 1. check parameters length
            if parameters.len() != parameter_indty_defined.len() {
                return Err(builder.cause("Mismatch in parameter length"));
            }

            // 2. check (ctx |- parameters[i] : substituted) for each i
            //   where substituted = (parameter_indty_defined[i])[var_j := parameters[j]] for j < i

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameters.iter().zip(parameter_indty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = exp_subst(&substituted, v, e);
                    }
                    substituted
                };
                // check (ctx |- param : substituted_param_ty)
                builder.add_check(
                    ctx,
                    param,
                    &substituted_param_ty,
                    "given parameter should welltyped",
                )?;
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
            }

            // 3. conclude (ctx |- IndType(ty, parameters) : arity_substituted)
            //  where arity_substituted = (ty.indices[] -> ty.sort)[var_j := parameters[j]] for j in indices
            let arity_substituted = {
                let mut substituted =
                    utils::assoc_prod(indspec.indices.clone(), Exp::Sort(indspec.sort));
                for (v, e) in &subst_varexp {
                    substituted = exp_subst(&substituted, v, e);
                }
                substituted
            };
            Ok(builder.build_infer(arity_substituted))
        }
        Exp::IndCtor {
            indspec,
            idx,
            parameters,
        } => {
            builder.rule("IndCtor");

            let parameter_indty_defined = indspec.parameters.clone();

            // 1. check parameter length
            if parameters.len() != parameter_indty_defined.len() {
                return Err(builder.cause("mismatch length"));
            }

            // 2. check (ctx |- parameter[i] : parameter_ty_defined[i]) for each i
            //   (we need to substitute previous parameters into later parameter types)

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameters.iter().zip(parameter_indty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = exp_subst(&substituted, v, e);
                    }
                    substituted
                };
                // check (ctx |- param : substituted_param_ty)
                builder.add_check(ctx, param, &substituted_param_ty, "parameter type mismatch")?;
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
            }

            // 3. conclude (ctx |- IndTypeCst(ty, idx, parameter) : ty.Constructors[idx] where THIS = ty)
            let constructor_type = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                indspec,
                *idx,
                parameters.clone(),
            );
            Ok(builder.build_infer(constructor_type))
        }
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            builder.rule("IndTypeElim");

            // 1. infer (ctx |- elim : IndType(ty, parameters) a[])
            let inferred_indty = builder.add_infer(ctx, elim, "infer eliminator type")?;
            let (inferred_indty_base, a) = utils::decompose_app(inferred_indty);
            let Exp::IndType {
                indspec: inferred_indty,
                parameters,
            } = inferred_indty_base
            else {
                return Err(builder.cause("type of elim is not inductive"));
            };

            // 2. check indty is the same as inferred_indty
            if !Rc::ptr_eq(indspec, &inferred_indty) {
                return Err(builder.cause("inductive type mismatch"));
            }

            // 3. infer kind of return_type
            let return_type_kind = builder.add_infer(ctx, return_type, "infer return type kind")?;
            let (telescope, sort) = utils::decompose_prod(normalize(&return_type_kind));
            let Exp::Sort(sort) = sort else {
                return Err(builder.cause("return type kind not ending with a sort"));
            };

            // 4. check (ty.sort, sort) can form an elimination
            if indspec.sort.relation_of_sort_indelim(sort).is_none() {
                return Err(builder.cause("cannot form eliminator"));
            }

            // 5. check convertibility of kind of return_type
            let expected_return_type_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
                indspec,
                parameters.clone(),
                sort,
            );
            let current_return_type_kind = utils::assoc_prod(telescope, Exp::Sort(sort));
            if !convertible(&current_return_type_kind, &expected_return_type_kind) {
                return Err(builder.cause("return type kind is not convertible to expected"));
            }

            // 6. check each case has type eliminator_type of constructor
            if cases.len() != indspec.constructors.len() {
                return Err(builder.cause("constructor length mismatch"));
            }

            for (idx, case) in cases.iter().enumerate() {
                let ctor = Exp::IndCtor {
                    indspec: indspec.clone(),
                    parameters: parameters.clone(),
                    idx,
                };
                let eliminator_ty = eliminator_type(
                    &indspec.constructors[idx],
                    return_type,
                    &ctor,
                    &Exp::IndType {
                        indspec: indspec.clone(),
                        parameters: parameters.clone(),
                    },
                );
                builder.add_check(ctx, case, &eliminator_ty, "check case type")?;
            }

            // 7. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };
            Ok(builder.build_infer(ty))
        }
        // type check (ctx |- exp: to)
        Exp::Cast { exp, to } => {
            builder.rule("Cast");

            // 1. check (ctx |- exp : to)
            if !builder.add_check(ctx, exp, to) {
                return builder.build_fail(
                    "Failed to check casted expression against type",
                    make_jd(None),
                );
            };

            // 2. conclude (ctx |- Cast(exp, to) : to)
            builder.build_typejudgement(make_jd(Some(to.as_ref().clone())))
        }
        Exp::ProveLater { prop } => {
            builder.rule("ProveLater");

            // 1. check (ctx |- exp : \Prop)
            if !builder.add_check(ctx, prop, &Exp::Sort(Sort::Prop)) {
                return builder.build_fail(
                    "Failed to check proposition against type Prop in context",
                    make_jd(None),
                );
            };

            // 2. add goal (ctx |= exp)
            builder.add_unproved_goal(PropositionJudgement {
                ctx: ctx.clone(),
                prop: Some(prop.as_ref().clone()),
            });

            // 3. conclude (ctx |- ProveLater(prop) : prop)
            builder.build_typejudgement(make_jd(Some(prop.as_ref().clone())))
        }
        Exp::ProveHere { exp, goals } => {
            builder.rule("ProveHere");

            // 1. infer (ctx |- exp : ?ty)
            let Some(inferred_ty) = builder.add_infer(ctx, exp) else {
                return builder.build_fail(
                    "Failed to infer type of proof term expression",
                    make_jd(None),
                );
            };

            // 2. get proof_tree is success
            //   if fail, early return
            let mut prove_ders: Vec<ProofTree> = vec![];

            for ProveGoal {
                extended_ctx,
                goal_prop,
                command,
            } in goals.iter()
            {
                let extended_ctx = ctx_extend_ctx(ctx, extended_ctx);

                // add (ctx::extended_ctx |- proof_term: goal_prop)
                match prove_command(&extended_ctx, command) {
                    Ok(der) => {
                        let as_proposition = PropositionJudgement {
                            ctx: extended_ctx.clone(),
                            prop: Some(goal_prop.clone()),
                        };

                        if !proposition_is_alpha_eq(&der.conclusion, &as_proposition) {
                            return builder.build_fail(
                                "Proved goal proposition does not match expected proposition",
                                make_jd(None),
                            );
                        }

                        prove_ders.push(der);
                    }
                    Err(derivation) => {
                        builder.premises.push(derivation);
                        return builder.build_fail("Goal failed to prove", make_jd(None));
                    }
                }
            }

            // 3. all goals are proved, now solve them
            if let Err(err) = builder.solve(prove_ders) {
                return builder.build_fail(err, make_jd(None));
            }

            // // 4. conclude (ctx |- ProveHere(exp, goals) : inferred_ty) where inferred_ty is infered at 1.
            builder.build_typejudgement(make_jd(Some(inferred_ty)))
        }
        // (ctx |- ProofTermRaw(command) : prop) if (ctx |= prop) by command
        Exp::ProofTermRaw { command } => {
            builder.rule("ProofTermRaw");

            // 1. get (ctx |= prop) by command
            let goal = prove_command(ctx, command);

            match goal {
                Ok(proof_tree) => {
                    let as_type_judgement = TypeJudgement {
                        ctx: proof_tree.conclusion.ctx.clone(),
                        term: term.clone(),
                        ty: proof_tree.conclusion.prop.clone(),
                    };
                    let der = Derivation::SolveSuccess(Rc::new(proof_tree));
                    builder.premises.push(der);
                    builder.build_typejudgement(as_type_judgement)
                }
                Err(derivation_solvefail) => {
                    let Derivation::SolveFail { conclusion, .. } = &derivation_solvefail else {
                        unreachable!("expected SolveFail derivation");
                    };
                    let as_type_judgement = TypeJudgement {
                        ctx: conclusion.ctx.clone(),
                        term: term.clone(),
                        ty: conclusion.prop.clone(),
                    };
                    builder.premises.push(derivation_solvefail);
                    builder.build_fail("Failed to prove proposition", as_type_judgement)
                }
            }
        }
        Exp::PowerSet { set } => {
            builder.rule("PowerSet");

            // 1. check (ctx |- exp : Set(i))
            let Some(i) = builder.add_sortset(ctx, set) else {
                return builder.build_fail("Failed to infer sort of type", make_jd(None));
            };

            // 2. conclude (ctx |- PowerSet(exp) : Set(i))
            let ty = Exp::Sort(Sort::Set(i));
            builder.build_typejudgement(make_jd(Some(ty)))
        }
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            builder.rule("SubSet");

            // 1. check (ctx |- set : Set(i))
            let Some(_i) = builder.add_sortset(ctx, set) else {
                return builder.build_fail("Failed to infer sort of type", make_jd(None));
            };

            // 2. check (ctx::(var, set) |- predicate : \Prop)
            let extend = ctx_extend(ctx, (var.clone(), *set.clone()));
            if !builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) {
                return builder.build_fail(
                    "Failed to check predicate against type Prop in extended context",
                    make_jd(None),
                );
            };

            // 3. conclude (ctx |- SubSet(var, set, predicate) : Power(set))
            builder.build_typejudgement(make_jd(Some(Exp::PowerSet { set: set.clone() })))
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            builder.rule("Pred");

            // 1. check (ctx |- superset : Set(i))
            let Some(_i) = builder.add_sortset(ctx, superset) else {
                return builder.build_fail("Failed to infer sort of type", make_jd(None));
            };

            // 2. check (ctx |- subset : Power(superset))
            if !builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            ) {
                return builder.build_fail(
                    "Failed to check subset against type Power(superset) in context",
                    make_jd(None),
                );
            };

            // 3. check (ctx |- element : superset)
            if !builder.add_check(ctx, element, superset) {
                return builder.build_fail(
                    "Failed to check element against type superset in context",
                    make_jd(None),
                );
            };
            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::TypeLift { superset, subset } => {
            builder.rule("TypeLift");
            // 1. check (ctx |- superset : Set(i))
            let Some(i) = builder.add_sortset(ctx, superset) else {
                return builder.build_fail("Failed to infer sort of type", make_jd(None));
            };

            // 2. check (ctx |- subset : Power(superset))
            if !builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            ) {
                return builder.build_fail(
                    "Failed to check subset against type Power(superset) in context",
                    make_jd(None),
                );
            };

            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Set(i)))))
        }
        Exp::Equal { left, right } => {
            builder.rule("Equal");
            // 1. infer left type
            let Some(left_ty) = builder.add_infer(ctx, left) else {
                return builder
                    .build_fail("Failed to infer type of left expression", make_jd(None));
            };

            // 2. infer right type
            let Some(right_ty) = builder.add_infer(ctx, right) else {
                return builder
                    .build_fail("Failed to infer type of right expression", make_jd(None));
            };

            // 3. check convertibility
            if !convertible(&left_ty, &right_ty) {
                return builder.build_fail(
                    "Type mismatch: left type is not convertible to right type",
                    make_jd(None),
                );
            }
            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::Exists { set } => {
            builder.rule("Exists");
            // 1. check (ctx |- ty : Set(i))
            let Some(_i) = builder.add_sortset(ctx, set) else {
                return builder.build_fail("Failed to infer sort of type", make_jd(None));
            };
            // 2. conclude (ctx |- Exists(ty) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::Take { map } => {
            builder.rule("Take");
            // 1. infer (ctx |- map: ?map_ty)
            let Some(map_ty) = builder.add_infer(ctx, map) else {
                return builder.build_fail("Failed to infer type of map expression", make_jd(None));
            };

            // 2. decompose map_ty into domain -> codomain
            let Exp::Prod {
                var,
                ty: _domain,
                body: codomain,
            } = normalize(&map_ty)
            else {
                return builder
                    .build_fail("Inferred type of map is not a function type", make_jd(None));
            };

            // 3. check codomain is independent of var
            if exp_contains_as_freevar(&codomain, &var) {
                return builder.build_fail(
                    "Codomain depends on variable, not allowed in Take",
                    make_jd(None),
                );
            }

            // 4. check (ctx |- map_ty : Set(i)) for some i
            let Some(_i) = builder.add_sortset(ctx, &map_ty) else {
                return builder.build_fail("Failed to infer sort of map type", make_jd(None));
            };

            // 5. conclude (ctx |- Take(map, domain, codomain) : codomain)
            builder.build_typejudgement(make_jd(Some(codomain.as_ref().clone())))
        }
    }
}

// infer_sort: (Derivation, Option<Sort>)
pub fn infer_sort(ctx: &Context, term: &Exp) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new("InferSort".to_string(), "sort");

    let make_jd = |s: Option<Sort>| -> TypeJudgement {
        TypeJudgement {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: s.map(Exp::Sort),
        }
    };

    // 1. infer type of term
    let Some(inferred_ty) = builder.add_infer(ctx, term) else {
        return builder.build_fail("Failed to infer type of term", make_jd(None));
    };

    // 2-A. if inferred_ty is already a sort, through
    if let Exp::Sort(s) = inferred_ty {
        builder.meta_through("infer_sort");
        return builder.build_typejudgement(make_jd(Some(s)));
    }

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return builder.build_fail("Type is not convertible to a sort", make_jd(None));
    };

    builder.build_typejudgement(make_jd(Some(s)))
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
// if err, it will return Derivation::SolveFail
pub fn prove_command(
    ctx: &Context,
    command: &ProveCommandBy,
) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new(
        "Subst Here (prove)".to_string(), // we will change rule name later
        "prove_command",
    );

    let make_pp = |prop: Option<Exp>| -> PropositionJudgement {
        PropositionJudgement {
            ctx: ctx.clone(),
            prop,
        }
    };

    match command {
        ProveCommandBy::Construct(proof_term) => {
            builder.rule("Construct");

            // 1. infer (ctx |- proof_term : prop)
            let Some(prop) = builder.add_infer(ctx, proof_term) else {
                return Err(
                    builder.build_fail_prop("Failed to infer type of proof term", make_pp(None))
                );
            };

            // 2. check prop: \Prop
            if !builder.add_check(ctx, &prop, &Exp::Sort(Sort::Prop)) {
                return Err(
                    builder.build_fail_prop("Inferred type is not of type Prop", make_pp(None))
                );
            };

            // 3. conclude (ctx |= prop)
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            builder.rule("ExactElem");

            // 1. check (ctx |- elem : ty)
            if !builder.add_check(ctx, elem, ty) {
                return Err(
                    builder.build_fail_prop("Failed to check element against type", make_pp(None))
                );
            };

            // 2. check (ctx |- ty : Set(i)) for some i
            let Some(_i) = builder.add_sortset(ctx, ty) else {
                return Err(builder.build_fail_prop("Failed to infer sort of type", make_pp(None)));
            };

            // 3. conclude (ctx |= Exists(ty))
            let prop = Exp::Exists {
                set: Box::new(ty.clone()),
            };
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => {
            builder.rule("SubsetElim");

            // 1. check (ctx |- elem : Typelift(superset, subset))
            let typelift = Exp::TypeLift {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
            };
            if !builder.add_check(ctx, elem, &typelift) {
                return Err(
                    builder.build_fail_prop("Failed to check subset elimination", make_pp(None))
                );
            };

            // 2. check (ctx |- Typelift(superset, subset) : Set(i)) for some i
            let Some(_i) = builder.add_sortset(ctx, &typelift) else {
                return Err(builder.build_fail_prop("Failed to infer sort of type", make_pp(None)));
            };

            // 3. conclude (ctx |= Pred(superset, subset, elem))
            let prop = Exp::Pred {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
                element: Box::new(elem.clone()),
            };
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::IdRefl { elem } => {
            builder.rule("IdRefl");

            // 1. infer (ctx |- elem : ?ty)
            let Some(ty) = builder.add_infer(ctx, elem) else {
                return Err(
                    builder.build_fail_prop("Failed to infer type of element", make_pp(None))
                );
            };

            // 2. check (ctx |- ty : Set(i)) for some i
            let Some(_i) = builder.add_sortset(ctx, &ty) else {
                return Err(builder.build_fail_prop("Failed to infer sort of type", make_pp(None)));
            };

            // 3. conclude (ctx |= elem = elem)
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(elem.clone()),
            };
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
        } => {
            builder.rule("IdElim");

            // 1. check (ctx |- ty : Set(i)) for some i
            let Some(_i) = builder.add_sortset(ctx, ty) else {
                return Err(builder.build_fail_prop("Failed to infer sort of type", make_pp(None)));
            };

            // 2. check (ctx |- left : ty)
            if builder.add_check(ctx, left, ty) {
                return Err(
                    builder.build_fail_prop("Failed to infer type of left element", make_pp(None))
                );
            };

            // 3. check (ctx |- right : ty)
            if builder.add_check(ctx, right, ty) {
                return Err(
                    builder.build_fail_prop("Failed to infer type of right element", make_pp(None))
                );
            };

            // 4. check (ctx::(var, ty) |- predicate : Prop)
            let extend = ctx_extend(ctx, (var.clone(), ty.clone()));
            if builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) {
                return Err(builder.build_fail_prop(
                    "Failed to check predicate in extended context",
                    make_pp(None),
                ));
            };

            // apply = (var: ty) => predicate
            let apply = Exp::Lam {
                var: var.clone(),
                ty: Box::new(ty.clone()),
                body: Box::new(predicate.clone()),
            };

            // 5. add (ctx |= ((var: ty) => predicate) (left)) as unproved goal
            let prop1 = Exp::App {
                func: Box::new(apply.clone()),
                arg: Box::new(left.clone()),
            };
            builder.add_unproved_goal(PropositionJudgement {
                ctx: ctx.clone(),
                prop: Some(prop1.clone()),
            });

            // 6. add (ctx |= elem1 = elem2) as unproved goal
            let prop2 = Exp::Equal {
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            builder.add_unproved_goal(PropositionJudgement {
                ctx: ctx.clone(),
                prop: Some(prop2.clone()),
            });

            // 7. conclude (ctx |= predicate(right))
            let prop = Exp::App {
                func: Box::new(apply.clone()),
                arg: Box::new(right.clone()),
            };
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => {
            builder.rule("TakeEq");

            // 1. check (ctx |- Take(func) : codomain)
            let take_ty = Exp::Take {
                map: Box::new(func.clone()),
            };
            if !builder.add_check(ctx, &take_ty, codomain) {
                return Err(
                    builder.build_fail_prop("Failed to check Take against type", make_pp(None))
                );
            };

            // 2. check (ctx |- elem : domain)
            if !builder.add_check(ctx, elem, domain) {
                return Err(builder
                    .build_fail_prop("Failed to check element against domain", make_pp(None)));
            };

            // 3. conclude (ctx |= Take(func, domain, codomain) = func(elem))
            let prop = Exp::Equal {
                left: Box::new(take_ty),
                right: Box::new(Exp::App {
                    func: Box::new(func.clone()),
                    arg: Box::new(elem.clone()),
                }),
            };

            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::Axiom(_axiom) => todo!("axiom implement later"),
    }
}

pub fn check_wellformed_ctx(ctx: &Context) -> (Vec<Derivation>, Option<Derivation>) {
    let mut ders = vec![];
    let mut cur_ctx = vec![];
    for (v, ty) in ctx {
        let der = infer_sort(ctx, ty);
        if matches!(der, Derivation::DerivationSuccess { .. }) {
            ders.push(der);
            cur_ctx.push((v.clone(), ty.clone()));
        } else {
            return (ders, Some(der));
        }
    }
    (ders, None)
}
