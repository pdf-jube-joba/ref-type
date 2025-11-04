// All judgement functions return a Derivation (the trace) plus a payload indicating success/value.
// ? for output value

use std::rc::Rc;

use crate::inductive::eliminator_type;
use crate::utils;

use crate::calculus::*;
use crate::exp::*;

// 許して
struct Builder {
    premises: Vec<Derivation>,
    rule: String,
    meta: Meta,
}

impl Builder {
    fn new(rule: String, meta: &str) -> Self {
        Self {
            premises: vec![],
            meta: Meta::Usual(meta.to_string()),
            rule,
        }
    }
    fn rule(&mut self, rule: &str) {
        self.rule = rule.to_string();
    }
    fn meta_through(&mut self, meta: &str) {
        self.meta = Meta::Through(meta.to_string());
    }

    fn add_check(&mut self, ctx: &Context, term: &Exp, ty: &Exp) -> bool {
        let derivation = check(ctx, term, ty);
        if let Derivation::DerivationSuccess { .. } = &derivation {
            self.premises.push(derivation);
            return true;
        }
        if let Derivation::DerivationFail { .. } = &derivation {
            self.premises.push(derivation);
            return false;
        }
        unreachable!("check result should be DerivationSuccess | DerivationFail");
    }
    fn add_infer(&mut self, ctx: &Context, term: &Exp) -> Option<Exp> {
        let derivation = infer(ctx, term);
        if let Derivation::DerivationSuccess { conclusion, .. } = &derivation {
            let ty = conclusion.ty.as_ref().unwrap().clone();
            self.premises.push(derivation);
            return Some(ty);
        }
        if let Derivation::DerivationFail { .. } = &derivation {
            self.premises.push(derivation);
            return None;
        }
        unreachable!("infer result should be DerivationSuccess | DerivationFail");
    }
    fn add_sort(&mut self, ctx: &Context, ty: &Exp) -> Option<Sort> {
        let derivation = infer_sort(ctx, ty);
        if let Derivation::DerivationSuccess { conclusion, .. } = &derivation {
            let Exp::Sort(sort) = conclusion.ty.as_ref().unwrap() else {
                unreachable!("sort inference must return a sort type")
            };
            let sort = *sort;
            self.premises.push(derivation);
            return Some(sort);
        }
        if let Derivation::DerivationFail { .. } = &derivation {
            self.premises.push(derivation);
            return None;
        }
        unreachable!("infer_sort result should be DerivationSuccess | DerivationFail");
    }
    fn add_unproved_goal(&mut self, unproved: PropositionJudgement) {
        self.premises.push(Derivation::GoalGenerated {
            proposition: unproved,
            solvetree: None,
        });
    }

    fn solve(&mut self, solve_goals: Vec<ProofTree>) -> Result<(), String> {
        assert!(solve_goals.iter().all(|g| matches!(g, ProofTree { .. })));
        for goal in solve_goals {
            let proved_goal = goal.conclusion.clone();
            let rc_goal = Rc::new(goal);

            self.premises
                .push(Derivation::SolveSuccess(rc_goal.clone()));

            let Some(first_goal) = self
                .premises
                .iter_mut()
                .find_map(|der| der.get_first_unproved_mut())
            else {
                return Err("No unproved goal found when solving".to_string());
            };

            let Derivation::GoalGenerated {
                proposition,
                solvetree,
            } = first_goal
            else {
                unreachable!("Expected GoalGenerated derivation");
            };

            if !proposition_is_alpha_eq(proposition, &proved_goal) {
                return Err(format!(
                    "Solved goal proposition {:?} does not match expected proposition {:?}",
                    proved_goal, proposition.prop
                ));
            }

            solvetree.replace(rc_goal.clone());
        }
        Ok(())
    }

    fn build_typejudgement(self, judgement: TypeJudgement) -> Derivation {
        Derivation::DerivationSuccess {
            conclusion: judgement,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_prop(self, proposition: PropositionJudgement) -> ProofTree {
        ProofTree {
            conclusion: proposition,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_fail<I>(self, fail_reason: I, judgement: TypeJudgement) -> Derivation
    where
        I: Into<String>,
    {
        let Meta::Usual(inner) = &self.meta else {
            unreachable!("meta must be Usual in build_fail")
        };
        let meta = format!("{}; {}", inner, fail_reason.into());

        Derivation::DerivationFail {
            conclusion: judgement,
            premises: self.premises,
            rule: self.rule,
            meta: Meta::Usual(meta),
        }
    }
    fn build_fail_prop(self, fail_reason: String, proposition: PropositionJudgement) -> Derivation {
        let Meta::Usual(inner) = &self.meta else {
            unreachable!("meta must be Usual in build_fail_prop")
        };
        let meta = format!("{}; {}", inner, fail_reason);

        Derivation::SolveFail {
            conclusion: proposition,
            premises: self.premises,
            rule: self.rule,
            meta: Meta::Usual(meta),
        }
    }
}

// return (ctx |- term: ty), result is in derivation.node.res
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> Derivation {
    let mut builder = Builder::new("Conversion".to_string(), "check");

    // expected judgement
    let judgement = TypeJudgement {
        ctx: ctx.clone(),
        term: term.clone(),
        ty: Some(ty.clone()),
    };

    // 1. infer (ctx |- term : ?inferred_ty)
    let Some(inferred_ty) = builder.add_infer(ctx, term) else {
        return builder.build_fail("no inferred type", judgement);
    };

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if exp_strict_equivalence(ty, &inferred_ty) {
        builder.meta_through("check");
        return builder.build_typejudgement(judgement);
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let Some(_sort) = builder.add_sort(ctx, ty) else {
        return builder.build_fail("ty is not well-sorted", judgement);
    };

    // 3 get normal(inferred_ty) & normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        return builder.build_typejudgement(judgement);
    }

    // 3-B-if inferred_ty == s1, ty == s2 ... lift universe rule
    if let (Exp::Sort(s1), Exp::Sort(s2)) = (&inferred_ty_result, &ty) {
        builder.rule("UniverseLift");
        if s1.can_lift_to(*s2) {
            return builder.build_typejudgement(judgement);
        } else {
            // if inferred_ty == s1, ty == s2 with s1 not liftable to s2 ... fails
            return builder.build_fail("fail universe lift", judgement);
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
            return builder.build_typejudgement(judgement);
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return builder.build_fail("fail subset weak", judgement);
        }
    }

    // 3-D-if ty =(alpha)= TypeLift(inferred_ty, subset) ... ty < inferred_ty
    // conclude (ctx |- term : ty) by subset strong rule if one can prove (ctx |= Pred(inferred_ty, subset, term))
    if let Exp::TypeLift { superset, subset } = &ty {
        builder.rule("SubsetStrong");
        if exp_is_alpha_eq(superset.as_ref(), &inferred_ty_result) {
            // add goal (ctx |= Pred(inferred_ty, subset, term))
            builder.add_unproved_goal(PropositionJudgement {
                ctx: ctx.clone(),
                prop: Some(Exp::Pred {
                    superset: Box::new(inferred_ty_result),
                    subset: subset.clone(),
                    element: Box::new(term.clone()),
                }),
            });
            return builder.build_typejudgement(judgement);
        } else {
            // if ty =(alpha)= TypeLift(ty1, some) with ty1 != inferred_ty ... fails
            return builder.build_fail("fail subset strong", judgement);
        }
    }

    // 4. fails
    builder.build_fail("ty, inferred_ty not convertible", judgement)
}

// infer: (Derivation, Option<Exp>) where Option<Exp> = Some(ty) on success
pub fn infer(ctx: &Context, term: &Exp) -> Derivation {
    let mut builder = Builder::new(
        "Subst Here (Infer)".to_string(), // we will change rule name later
        "infer",
    );

    let make_jd = |ty: Option<Exp>| -> TypeJudgement {
        TypeJudgement {
            ctx: ctx.clone(),
            term: term.clone(),
            ty,
        }
    };

    match term {
        Exp::Sort(sort) => {
            builder.rule("Sort");

            // 1. conclude (ctx |- s : ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    builder.build_typejudgement(make_jd(Some(ty)))
                }
                None => builder.build_fail("no sort of sort found", make_jd(None)),
            }
        }
        Exp::Var(index) => {
            builder.rule("Var");

            // 1. conclude (ctx |- var : ?ty) where (var: ty) in ctx
            match ctx_get(ctx, index) {
                Some(ty) => builder.build_typejudgement(make_jd(Some(ty.clone()))),
                None => builder.build_fail("not found", make_jd(None)),
            }
        }
        Exp::Prod { var, ty, body } => {
            builder.rule("Prod");

            // 1. infer (ctx |- ty : ?s1)
            let Some(s1) = builder.add_sort(ctx, ty) else {
                return builder.build_fail("fail s1", make_jd(None));
            };

            // 2. infer (ctx:: (var, ty) |= body : ?s2)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let Some(s2) = builder.add_sort(&extend, body) else {
                return builder.build_fail("fail s2", make_jd(None));
            };

            // 3. check (s1, s2) can form a product sort s3
            let s3 = match s1.relation_of_sort(s2) {
                Some(s3) => s3,
                None => {
                    return builder.build_fail("no (s1, s2, s3)", make_jd(None));
                }
            };

            // 4. conclude (ctx |- Prod(var, ty, body) : s3)
            let ty = Exp::Sort(s3);
            builder.build_typejudgement(make_jd(Some(ty)))
        }
        Exp::Lam { var, ty, body } => {
            builder.rule("Lam");

            // 1. infer (ctx |- ty : ?s) for some sort s
            let Some(_sort) = builder.add_sort(ctx, ty) else {
                return builder.build_fail("fail sort", make_jd(None));
            };

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let Some(body_ty) = builder.add_infer(&extend, body) else {
                return builder.build_fail("no type of body", make_jd(None));
            };

            // 3. conclude (ctx |- Lam(var, ty, body) : lam_ty)
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            builder.build_typejudgement(make_jd(Some(lam_ty)))
        }
        Exp::App { func, arg } => {
            builder.rule("App");

            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let Some(func_ty) = builder.add_infer(ctx, func) else {
                return builder.build_fail("no type of func", make_jd(None));
            };
            let Exp::Prod {
                var,
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return builder.build_fail("type is not a product", make_jd(None));
            };

            // 2. check (ctx |- arg : arg_ty)
            if !builder.add_check(ctx, arg, &arg_ty) {
                return builder.build_fail("arg type mismatch", make_jd(None));
            };

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            let ret_ty_substituted = exp_subst(&ret_ty, &var, arg);
            builder.build_typejudgement(make_jd(Some(ret_ty_substituted)))
        }
        Exp::IndType {
            indspec: indty,
            parameters,
        } => {
            builder.rule("IndType");

            let parameter_indty_defined = indty.parameters.clone();

            // 1. check parameters length
            if parameters.len() != parameter_indty_defined.len() {
                return builder.build_fail("mismatch length", make_jd(None));
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
                if !builder.add_check(ctx, param, &substituted_param_ty) {
                    return builder.build_fail("parameter type mismatch", make_jd(None));
                };
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
            }

            // 3. conclude (ctx |- IndType(ty, parameters) : arity_substituted)
            //  where arity_substituted = (ty.indices[] -> ty.sort)[var_j := parameters[j]] for j in indices
            let arity_substituted = {
                let mut substituted =
                    utils::assoc_prod(indty.indices.clone(), Exp::Sort(indty.sort));
                for (v, e) in &subst_varexp {
                    substituted = exp_subst(&substituted, v, e);
                }
                substituted
            };
            builder.build_typejudgement(make_jd(Some(arity_substituted)))
        }
        Exp::IndCtor {
            indspec: indty,
            idx,
            parameters,
        } => {
            builder.rule("IndTypeCst");

            let parameter_indty_defined = indty.parameters.clone();

            // 1. check parameter length
            if parameters.len() != parameter_indty_defined.len() {
                return builder.build_fail("mismatch length", make_jd(None));
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
                if !builder.add_check(ctx, param, &substituted_param_ty) {
                    return builder.build_fail("parameter type mismatch", make_jd(None));
                };
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
            }

            // 3. conclude (ctx |- IndTypeCst(ty, idx, parameter) : ty.Constructors[idx] where THIS = ty)
            let constructor_type = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                indty,
                *idx,
                parameters.clone(),
            );

            builder.build_typejudgement(make_jd(Some(constructor_type)))
        }
        Exp::IndElim {
            indspec: indty,
            elim,
            return_type,
            cases,
        } => {
            builder.rule("IndTypeElim");

            // 1. infer (ctx |- elim : IndType(ty, parameters) a[])
            let Some(inferred_indty) = builder.add_infer(ctx, elim) else {
                return builder.build_fail(
                    format!("Failed to infer type of eliminator expression {:?}", elim),
                    make_jd(None),
                );
            };
            // a[] are well-typed
            // i.e. a[]: t[] where (x[]: t[]) are in indty.indices

            let (inferred_indty_base, a) = utils::decompose_app(inferred_indty);
            let Exp::IndType {
                indspec: inferred_indty,
                parameters, // => well-typed
            } = inferred_indty_base
            else {
                return builder.build_fail(
                    format!(
                        "Eliminator type {:?} is not an inductive type",
                        inferred_indty_base
                    ),
                    make_jd(None),
                );
            };

            // 2. check indty is the same as inferred_indty
            if !std::rc::Rc::ptr_eq(indty, &inferred_indty) {
                return builder.build_fail(
                    format!(
                        "Inductive type mismatch: expected {:?}, found {:?}",
                        indty, inferred_indty
                    ),
                    make_jd(None),
                );
            }

            // 3. infer kind of return_type
            let Some(return_type_kind) = builder.add_infer(ctx, return_type) else {
                return builder.build_fail(
                    format!(
                        "Failed to infer sort of return type expression {:?}",
                        return_type
                    ),
                    make_jd(None),
                );
            };
            let (telescope, sort) = utils::decompose_prod(normalize(&return_type_kind));
            let Exp::Sort(sort) = sort else {
                return builder.build_fail(
                    format!(
                        "Return type kind {:?} is not ending with a sort",
                        return_type_kind
                    ),
                    make_jd(None),
                );
            };

            // 4. check (ty.sort, sort) can form a elimination
            if indty.sort.relation_of_sort_indelim(sort).is_none() {
                return builder.build_fail(format!(
                    "Cannot form eliminator with inductive type sort {:?} and return type sort {:?}",
                    indty.sort, sort
                ), make_jd(None));
            }

            // 5. check convertibility of kind of return_type
            let expected_return_type_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
                indty,
                parameters.clone(),
                sort,
            );
            let current_return_type_kind = utils::assoc_prod(telescope, Exp::Sort(sort));
            if !convertible(&return_type_kind, &current_return_type_kind) {
                return builder.build_fail(
                    format!(
                        "Return type kind {:?} is not convertible to expected kind {:?}",
                        return_type_kind, expected_return_type_kind
                    ),
                    make_jd(None),
                );
            }

            // 6. check each case has type eliminator_type of constructor
            // check length of cases and constructors
            if cases.len() != indty.constructors.len() {
                return builder.build_fail(
                    format!(
                        "Constructor length mismatch: expected {}, found {}",
                        indty.constructors.len(),
                        cases.len()
                    ),
                    make_jd(None),
                );
            }

            // check (ctx |- cases[i] : eliminator_type[i])
            for (case, constructor) in cases.iter().zip(indty.constructors.iter()) {
                let eliminator_ty = eliminator_type(
                    constructor,
                    return_type,
                    elim,
                    &Exp::IndType {
                        indspec: indty.clone(),
                        parameters: parameters.clone(),
                    },
                );
                if !builder.add_check(ctx, case, &eliminator_ty) {
                    return builder.build_fail(
                        format!(
                            "Failed to check case {:?} against eliminator type {:?}",
                            case, eliminator_ty
                        ),
                        make_jd(None),
                    );
                };
            }

            // 8. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };

            builder.build_typejudgement(make_jd(Some(ty)))
        }
        // type check (ctx |- exp: to)
        Exp::Cast { exp, to } => {
            builder.rule("Cast");

            // 1. check (ctx |- exp : to)
            if !builder.add_check(ctx, exp, to) {
                return builder.build_fail(
                    format!(
                        "Failed to check casted expression {:?} against type {:?}",
                        exp, to
                    ),
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
                    format!(
                        "Failed to check proposition {:?} against type Prop in context",
                        prop
                    ),
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

            for (
                i,
                ProveGoal {
                    extended_ctx,
                    goal_prop,
                    command,
                },
            ) in goals.iter().enumerate()
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
                                format!(
                                    "Proved goal {} proposition {:?} does not match expected proposition {:?}",
                                    i + 1,
                                    der.conclusion.prop,
                                    goal_prop
                                ),
                                make_jd(None),
                            );
                        }

                        prove_ders.push(der);
                    }
                    Err(derivation) => {
                        builder.premises.push(derivation);
                        return builder
                            .build_fail(format!("Goal {} failed to prove", i + 1), make_jd(None));
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
                    builder.build_fail(
                        format!("Failed to prove proposition {:?}", as_type_judgement.ty),
                        as_type_judgement,
                    )
                }
            }
        }
        Exp::PowerSet { set: exp } => {
            builder.rule("PowerSet");

            // 1. check (ctx |- exp : Set(i))
            let Some(sort) = builder.add_sort(ctx, exp) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", exp),
                    make_jd(None),
                );
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", exp),
                    make_jd(None),
                );
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
            let Some(sort) = builder.add_sort(ctx, set) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", set),
                    make_jd(None),
                );
            };
            let Sort::Set(_i) = sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", set),
                    make_jd(None),
                );
            };

            // 2. check (ctx::(var, set) |- predicate : \Prop)
            let extend = ctx_extend(ctx, (var.clone(), *set.clone()));
            if !builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) {
                return builder.build_fail(
                    format!(
                        "Failed to check predicate {:?} against type Prop in extended context",
                        predicate
                    ),
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
            let Some(sort) = builder.add_sort(ctx, superset) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", superset),
                    make_jd(None),
                );
            };
            let Sort::Set(_i) = sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", superset),
                    make_jd(None),
                );
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
                    format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    ),
                    make_jd(None),
                );
            };

            // 3. check (ctx |- element : superset)
            if !builder.add_check(ctx, element, superset) {
                return builder.build_fail(
                    format!(
                        "Failed to check element {:?} against type superset in context",
                        element,
                    ),
                    make_jd(None),
                );
            };
            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::TypeLift { superset, subset } => {
            builder.rule("TypeLift");
            // 1. check (ctx |- superset : Set(i))
            let Some(sort) = builder.add_sort(ctx, superset) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", superset),
                    make_jd(None),
                );
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", superset),
                    make_jd(None),
                );
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
                    format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    ),
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
                return builder.build_fail(
                    format!("Failed to infer type of left expression {:?}", left),
                    make_jd(None),
                );
            };

            // 2. infer right type
            let Some(right_ty) = builder.add_infer(ctx, right) else {
                return builder.build_fail(
                    format!("Failed to infer type of right expression {:?}", right),
                    make_jd(None),
                );
            };

            // 3. check convertibility
            if !convertible(&left_ty, &right_ty) {
                return builder.build_fail(
                    format!(
                        "Type mismatch: left type {:?} is not convertible to right type {:?}",
                        left_ty, right_ty
                    ),
                    make_jd(None),
                );
            }
            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::Exists { set: ty } => {
            builder.rule("Exists");
            // 1. check (ctx |- ty : Set(i))
            let Some(_sort) = builder.add_sort(ctx, ty) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", ty),
                    make_jd(None),
                );
            };
            let Sort::Set(_) = _sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", ty),
                    make_jd(None),
                );
            };
            // 2. conclude (ctx |- Exists(ty) : \Prop)
            builder.build_typejudgement(make_jd(Some(Exp::Sort(Sort::Prop))))
        }
        Exp::Take { map } => {
            builder.rule("Take");
            // 1. infer (ctx |- map: ?map_ty)
            let Some(map_ty) = builder.add_infer(ctx, map) else {
                return builder.build_fail(
                    format!("Failed to infer type of map expression {:?}", map),
                    make_jd(None),
                );
            };

            // 2. decompose map_ty into domain -> codomain
            let Exp::Prod {
                var,
                ty: _domain,
                body: codomain,
            } = normalize(&map_ty)
            else {
                return builder.build_fail(
                    format!(
                        "Inferred type {:?} of map expression {:?} is not a function type",
                        map_ty, map
                    ),
                    make_jd(None),
                );
            };

            // 3. check codomain is independent of var
            if exp_contains_as_freevar(&codomain, &var) {
                return builder.build_fail(
                    format!(
                        "Codomain {:?} depends on variable {:?}, which is not allowed in Take",
                        codomain, var
                    ),
                    make_jd(None),
                );
            }

            // 4. check (ctx |- map_ty : Set(i)) for some i
            let Some(sort) = builder.add_sort(ctx, &map_ty) else {
                return builder.build_fail(
                    format!("Failed to infer sort of type {:?}", map_ty),
                    make_jd(None),
                );
            };
            let Sort::Set(_) = sort else {
                return builder.build_fail(
                    format!("Type {:?} is not of form Set(i)", map_ty),
                    make_jd(None),
                );
            };

            // 5. conclude (ctx |- Take(map, domain, codomain) : codomain)
            builder.build_typejudgement(make_jd(Some(codomain.as_ref().clone())))
        }
    }
}

// infer_sort: (Derivation, Option<Sort>)
pub fn infer_sort(ctx: &Context, term: &Exp) -> Derivation {
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
        return builder.build_fail(
            format!("Failed to infer type of term {:?}", term),
            make_jd(None),
        );
    };

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return builder.build_fail(
            format!("Type {:?} is not convertible to a sort", inferred_ty),
            make_jd(None),
        );
    };

    builder.build_typejudgement(make_jd(Some(s)))
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
// if err, it will return Derivation::SolveFail
pub fn prove_command(ctx: &Context, command: &ProveCommandBy) -> Result<ProofTree, Derivation> {
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
                return Err(builder.build_fail_prop(
                    format!("Failed to infer type of proof term {:?}", proof_term),
                    make_pp(None),
                ));
            };

            // 2. check prop: \Prop
            if !builder.add_check(ctx, &prop, &Exp::Sort(Sort::Prop)) {
                return Err(builder.build_fail_prop(
                    format!(
                        "Inferred type {:?} of proof term {:?} is not of type Prop",
                        prop, proof_term
                    ),
                    make_pp(None),
                ));
            };

            // 3. conclude (ctx |= prop)
            Ok(builder.build_prop(make_pp(Some(prop))))
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            builder.rule("ExactElem");

            // 1. check (ctx |- elem : ty)
            if !builder.add_check(ctx, elem, ty) {
                return Err(builder.build_fail_prop(
                    format!("Failed to check element {:?} against type {:?}", elem, ty),
                    make_pp(None),
                ));
            };

            // 2. (check ctx |- ty : Set(i)) for some i
            let Some(sort) = builder.add_sort(ctx, ty) else {
                return Err(builder.build_fail_prop(
                    format!("Failed to infer sort of type {:?}", ty),
                    make_pp(None),
                ));
            };
            let Sort::Set(_) = sort else {
                return Err(builder.build_fail_prop(
                    format!("Type {:?} is not of form Set(i)", ty),
                    make_pp(None),
                ));
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
                return Err(builder.build_fail_prop(
                    format!(
                        "Failed to check element {:?} against type Typelift({:?}, {:?})",
                        elem, superset, subset
                    ),
                    make_pp(None),
                ));
            };

            // 2. check (ctx |- Typelift(superset, subset) : Set(i)) for some i
            let Some(_sort) = builder.add_sort(ctx, &typelift) else {
                return Err(builder.build_fail_prop(
                    format!(
                        "Failed to infer sort of type Typelift({:?}, {:?})",
                        superset, subset
                    ),
                    make_pp(None),
                ));
            };
            let Sort::Set(_) = _sort else {
                return Err(builder.build_fail_prop(
                    format!(
                        "Type Typelift({:?}, {:?}) is not of form Set(i)",
                        superset, subset
                    ),
                    make_pp(None),
                ));
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
                return Err(builder.build_fail_prop(
                    format!("Failed to infer type of element {:?}", elem),
                    make_pp(None),
                ));
            };

            // 2. check (ctx |- ty : Set(i)) for some i
            let Some(sort) = builder.add_sort(ctx, &ty) else {
                return Err(builder.build_fail_prop(
                    format!("Failed to infer sort of type {:?}", ty),
                    make_pp(None),
                ));
            };
            let Sort::Set(_) = sort else {
                return Err(builder.build_fail_prop(
                    format!("Type {:?} is not of form Set(i)", ty),
                    make_pp(None),
                ));
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
            let Some(sort) = builder.add_sort(ctx, ty) else {
                return Err(builder.build_fail_prop(
                    format!("Failed to infer sort of type {:?}", ty),
                    make_pp(None),
                ));
            };
            let Sort::Set(_) = sort else {
                return Err(builder.build_fail_prop(
                    format!("Type {:?} is not of form Set(i)", ty),
                    make_pp(None),
                ));
            };

            // 2. check (ctx |- left : ty)
            if builder.add_check(ctx, left, ty) {
                return Err(builder.build_fail_prop(
                    format!("Failed to check element {:?} against type {:?}", left, ty),
                    make_pp(None),
                ));
            };

            // 3. check (ctx |- right : ty)
            if builder.add_check(ctx, right, ty) {
                return Err(builder.build_fail_prop(
                    format!("Failed to check element {:?} against type {:?}", right, ty),
                    make_pp(None),
                ));
            };

            // 4. check (ctx::(var, ty) |- predicate : Prop)
            let extend = ctx_extend(ctx, (var.clone(), ty.clone()));
            if builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) {
                return Err(builder.build_fail_prop(
                    format!(
                        "Failed to check predicate {:?} against type Prop in extended context",
                        predicate
                    ),
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
                return Err(builder.build_fail_prop(
                    format!(
                        "Failed to check Take({:?}, {:?}, {:?}) against type {:?} in context",
                        func, domain, codomain, codomain
                    ),
                    make_pp(None),
                ));
            };

            // 2. check (ctx |- elem : domain)
            if !builder.add_check(ctx, elem, domain) {
                return Err(builder.build_fail_prop(
                    format!(
                        "Failed to check element {:?} against type {:?}",
                        elem, domain
                    ),
                    make_pp(None),
                ));
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
