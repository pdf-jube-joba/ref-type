// All judgement functions return a Derivation (the trace) plus a payload indicating success/value.
// ? for output value

use std::rc::Rc;

use crate::inductive::eliminator_type;
use crate::utils;

use crate::calculus::*;
use crate::exp::*;

// 許して
struct Builder {
    node: Node,
    premises: Vec<Derivation>,
    rule: String,
    meta: Meta,
}

impl Builder {
    fn new(rule: String, meta: &str, candidate: Node) -> Self {
        Self {
            premises: vec![],
            meta: Meta::Usual(meta.to_string()),
            rule,
            node: candidate,
        }
    }
    fn rule(&mut self, rule: &str) {
        self.rule = rule.to_string();
    }
    fn meta_through(&mut self, meta: &str) {
        self.meta = Meta::Through(meta.to_string());
    }

    fn add_check(&mut self, ctx: &Context, term: &Exp, ty: &Exp) -> Option<()> {
        let premise = check(ctx, term, ty);
        assert!(matches!(premise.node(), Some(Node::TypeCheck(_))));
        let TypeCheck { res, .. } = premise.node().unwrap().as_type_check().unwrap();
        if !*res {
            self.premises.push(premise);
            None
        } else {
            self.premises.push(premise);
            Some(())
        }
    }
    fn add_infer(&mut self, ctx: &Context, term: &Exp) -> Option<Exp> {
        let premise = infer(ctx, term);
        assert!(matches!(premise.node(), Some(Node::TypeInfer(_))));
        let TypeInfer { ty, .. } = premise.node().unwrap().as_type_infer().unwrap();
        if let Some(ty) = ty {
            let ty = ty.clone();
            self.premises.push(premise);
            Some(ty)
        } else {
            self.premises.push(premise);
            None
        }
    }
    fn add_sort(&mut self, ctx: &Context, ty: &Exp) -> Option<Sort> {
        let premise = infer_sort(ctx, ty);
        assert!(matches!(premise.node(), Some(Node::SortInfer(_))));
        let SortInfer { sort, .. } = premise.node().unwrap().as_sort_infer().unwrap();
        if let Some(sort) = sort {
            let sort = *sort;
            self.premises.push(premise);
            Some(sort)
        } else {
            self.premises.push(premise);
            None
        }
    }
    fn add_prove(&mut self, premise: Derivation) -> Option<Exp> {
        assert!(matches!(premise.node(), Some(Node::Prove(_))));
        let Prove { prop, .. } = premise.node().unwrap().as_prove().unwrap();
        if prop.is_none() {
            self.premises.push(premise);
            None
        } else {
            let prop = prop.clone();
            self.premises.push(premise);
            prop
        }
    }
    fn add_unproved_goal(&mut self, unproved: Prove) {
        self.premises.push(Derivation::UnSolved(unproved));
    }
    fn add(&mut self, der: Derivation) {
        self.premises.push(der);
    }
    fn solve(&mut self, ders: Vec<Derivation>) -> Result<(), String> {
        assert!(
            ders.iter()
                .all(|der| matches!(der, Derivation::Prove { .. }))
        );
        // we solve all goals in first element of premises
        assert!(!self.premises.is_empty());

        for der in ders {
            self.premises.push(der);
        }

        // head ... check to unproved goals, tails ... goal solvers
        let ([head, ..], tails) = self.premises.split_at_mut(1) else {
            unreachable!("premises must have at least one element")
        };

        for tail in tails {
            let Derivation::Prove { proved, num: n, .. } = tail else {
                unreachable!("Only Prove derivations are allowed here")
            };

            let unproved = get_first_goal(head);
            let Some(unproved) = unproved else {
                return Err("not found unproved goal".into());
            };

            let Derivation::UnSolved(unproved_goal) = unproved else {
                unreachable!("Only UnProved derivations are allowed here")
            };
            if is_alpha_eq_prove(unproved_goal, proved) {
                // solved, remove from premises
                *unproved = Derivation::Solved {
                    target: unproved_goal.clone(),
                    num: n.clone(),
                };
            } else {
                *unproved = Derivation::SolveFailed {
                    target: unproved_goal.clone(),
                    num: n.clone(),
                };
                return Err("failed to solve goal".into());
            }
        }

        // if some goal is remained, return error
        if get_first_goal(head).is_some() {
            return Err("some goals are remained unsolved".into());
        }

        Ok(())
    }

    fn build_typecheck(mut self) -> Derivation {
        let TypeCheck { res, .. } = self.node.as_type_check_mut().unwrap();
        *res = true;
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_typeinfer(mut self, ty_res: Exp) -> Derivation {
        assert!(matches!(self.node, Node::TypeInfer(_)));
        let TypeInfer { ty, .. } = &mut self.node.as_type_infer_mut().unwrap();
        *ty = Some(ty_res);
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_sortinfer(mut self, sort_res: Sort) -> Derivation {
        assert!(matches!(self.node, Node::SortInfer(_)));
        let SortInfer { sort, .. } = &mut self.node.as_sort_infer_mut().unwrap();
        *sort = Some(sort_res);
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_prop(mut self, prop_res: Exp) -> Derivation {
        assert!(matches!(self.node, Node::Prove(_)));
        let Prove { prop, .. } = &mut self.node.as_prove_mut().unwrap();
        *prop = Some(prop_res);
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_fail<I>(self, fail_reason: I) -> Derivation
    where
        I: Into<String>,
    {
        assert!(matches!(self.meta, Meta::Usual(_)));
        let Meta::Usual(meta) = self.meta else {
            unreachable!("Only Usual meta can build fail")
        };
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: Meta::Fail(format!("{}: {}", meta, fail_reason.into())),
        }
    }
}

// return (ctx |- term: ty), result is in derivation.node.res
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> Derivation {
    let mut builder = Builder::new(
        "Conversion".to_string(),
        "check",
        Node::TypeCheck(TypeCheck {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: ty.clone(),
            res: false,
        }),
    );

    // 1. infer (ctx |- term : ?inferred_ty)
    let Some(inferred_ty) = builder.add_infer(ctx, term) else {
        return builder.build_fail("no inferred type");
    };

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if strict_equivalence(ty, &inferred_ty) {
        builder.meta_through("check");
        return builder.build_typecheck();
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let Some(_sort) = builder.add_sort(ctx, ty) else {
        return builder.build_fail("ty is not well-sorted");
    };

    // 3 get normal(inferred_ty) & normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        return builder.build_typecheck();
    }

    // 3-B-if inferred_ty == s1, ty == s2 ... lift universe rule
    if let (Exp::Sort(s1), Exp::Sort(s2)) = (&inferred_ty_result, &ty) {
        builder.rule("UniverseLift");
        if s1.can_lift_to(*s2) {
            return builder.build_typecheck();
        } else {
            // if inferred_ty == s1, ty == s2 with s1 not liftable to s2 ... fails
            return builder.build_fail("fail universe lift");
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
        if is_alpha_eq(superset.as_ref(), &ty) {
            return builder.build_typecheck();
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return builder.build_fail("fail subset weak");
        }
    }

    // 3-D-if ty =(alpha)= TypeLift(inferred_ty, subset) ... ty < inferred_ty
    // conclude (ctx |- term : ty) by subset strong rule if one can prove (ctx |= Pred(inferred_ty, subset, term))
    if let Exp::TypeLift { superset, subset } = &ty {
        builder.rule("SubsetStrong");
        if is_alpha_eq(superset.as_ref(), &inferred_ty_result) {
            // add goal (ctx |= Pred(inferred_ty, subset, term))
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: Some(Exp::Pred {
                    superset: Box::new(inferred_ty_result),
                    subset: subset.clone(),
                    element: Box::new(term.clone()),
                }),
            });
            return builder.build_typecheck();
        } else {
            // if ty =(alpha)= TypeLift(ty1, some) with ty1 != inferred_ty ... fails
            return builder.build_fail("fail subset strong");
        }
    }

    // 4. fails
    builder.build_fail("ty, inferred_ty not convertible")
}

// infer: (Derivation, Option<Exp>) where Option<Exp> = Some(ty) on success
pub fn infer(ctx: &Context, term: &Exp) -> Derivation {
    let mut builder = Builder::new(
        "Subst Here (Infer)".to_string(), // we will change rule name later
        "infer",
        Node::TypeInfer(TypeInfer {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: None,
        }),
    );
    match term {
        Exp::Sort(sort) => {
            builder.rule("Sort");

            // 1. conclude (ctx |- s : ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    builder.build_typeinfer(ty)
                }
                None => builder.build_fail("no sort of sort found"),
            }
        }
        Exp::Var(index) => {
            builder.rule("Var");

            // 1. conclude (ctx |- var : ?ty) where (var: ty) in ctx
            match ctx_get(ctx, index) {
                Some(ty) => builder.build_typeinfer(ty.clone()),
                None => builder.build_fail("not found"),
            }
        }
        Exp::Prod { var, ty, body } => {
            builder.rule("Prod");

            // 1. infer (ctx |- ty : ?s1)
            let Some(s1) = builder.add_sort(ctx, ty) else {
                return builder.build_fail("fail s1");
            };

            // 2. infer (ctx:: (var, ty) |= body : ?s2)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let Some(s2) = builder.add_sort(&extend, body) else {
                return builder.build_fail("fail s2");
            };

            // 3. check (s1, s2) can form a product sort s3
            let s3 = match s1.relation_of_sort(s2) {
                Some(s3) => s3,
                None => {
                    return builder.build_fail("no (s1, s2, s3)");
                }
            };

            // 4. conclude (ctx |- Prod(var, ty, body) : s3)
            let ty = Exp::Sort(s3);
            builder.build_typeinfer(ty)
        }
        Exp::Lam { var, ty, body } => {
            builder.rule("Lam");

            // 1. infer (ctx |- ty : ?s) for some sort s
            let Some(_sort) = builder.add_sort(ctx, ty) else {
                return builder.build_fail("fail sort");
            };

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let Some(body_ty) = builder.add_infer(&extend, body) else {
                return builder.build_fail("no type of body");
            };

            // 3. conclude (ctx |- Lam(var, ty, body) : lam_ty)
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            builder.build_typeinfer(lam_ty)
        }
        Exp::App { func, arg } => {
            builder.rule("App");

            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let Some(func_ty) = builder.add_infer(ctx, func) else {
                return builder.build_fail("no type of func");
            };
            let Exp::Prod {
                var,
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return builder.build_fail("type is not a product");
            };

            // 2. check (ctx |- arg : arg_ty)
            let Some(()) = builder.add_check(ctx, arg, &arg_ty) else {
                return builder.build_fail("arg type mismatch");
            };

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            let ret_ty_substituted = subst(&ret_ty, &var, arg);
            builder.build_typeinfer(ret_ty_substituted)
        }
        Exp::IndType { indty, parameters } => {
            builder.rule("IndType");

            let parameter_indty_defined = indty.parameters.clone();

            // 1. check parameters length
            if parameters.len() != parameter_indty_defined.len() {
                return builder.build_fail("mismatch length");
            }

            // 2. check (ctx |- parameters[i] : substituted) for each i
            //   where substituted = (parameter_indty_defined[i])[var_j := parameters[j]] for j < i

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameters.iter().zip(parameter_indty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = subst(&substituted, v, e);
                    }
                    substituted
                };
                // check (ctx |- param : substituted_param_ty)
                let Some(()) = builder.add_check(ctx, param, &substituted_param_ty) else {
                    return builder.build_fail("parameter type mismatch");
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
                    substituted = subst(&substituted, v, e);
                }
                substituted
            };
            builder.build_typeinfer(arity_substituted)
        }
        Exp::IndCtor {
            indty,
            idx,
            parameters,
        } => {
            builder.rule("IndTypeCst");

            let parameter_indty_defined = indty.parameters.clone();

            // 1. check parameter length
            if parameters.len() != parameter_indty_defined.len() {
                return builder.build_fail("mismatch length");
            }

            // 2. check (ctx |- parameter[i] : parameter_ty_defined[i]) for each i
            //   (we need to substitute previous parameters into later parameter types)

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameters.iter().zip(parameter_indty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = subst(&substituted, v, e);
                    }
                    substituted
                };
                // check (ctx |- param : substituted_param_ty)
                let Some(()) = builder.add_check(ctx, param, &substituted_param_ty) else {
                    return builder.build_fail("parameter type mismatch");
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

            builder.build_typeinfer(constructor_type)
        }
        Exp::IndElim {
            indty,
            elim,
            return_type,
            sort,
            cases,
        } => {
            builder.rule("IndTypeElim");

            // 1. check (ty.sort, sort) can form a elimination
            if indty.sort.relation_of_sort_indelim(*sort).is_none() {
                return builder.build_fail(format!(
                    "Cannot form eliminator with inductive type sort {:?} and return type sort {:?}",
                    indty.sort, sort
                ));
            }

            // 2. infer (ctx |- elim : IndType(ty, parameters) a[])
            let Some(inferred_indty) = builder.add_infer(ctx, elim) else {
                return builder.build_fail(format!(
                    "Failed to infer type of eliminator expression {:?}",
                    elim
                ));
            };

            let (inferred_indty_base, a) = utils::decompose_app(inferred_indty);
            let Exp::IndType {
                indty: inferred_indty,
                parameters,
            } = inferred_indty_base
            else {
                return builder.build_fail(format!(
                    "Eliminator type {:?} is not an inductive type",
                    inferred_indty_base
                ));
            };

            // 3. check indty is the same as inferred_indty
            if !std::rc::Rc::ptr_eq(indty, &inferred_indty) {
                return builder.build_fail(format!(
                    "Inductive type mismatch: expected {:?}, found {:?}",
                    indty, inferred_indty
                ));
            }

            let xt: Vec<(Var, Exp)> = indty.indices.to_vec();

            // 4. check types of a[]: t[] where (x[]: t[]) are in indty.indices
            if xt.len() != a.len() {
                return builder.build_fail("mismatch arity length");
            }

            for ((_, t), a) in xt.iter().zip(a.iter()) {
                let Some(()) = builder.add_check(ctx, a, t) else {
                    return builder.build_fail(format!("Failed to check arity ... {a}: {t}",));
                };
            }

            // 5. check (ctx |- return_type: (x[]: t[]) -> THIS x[] -> s)
            let kind_of_return_type = crate::inductive::InductiveTypeSpecs::return_type_kind(
                indty,
                parameters.clone(),
                *sort,
            );
            let Some(()) = builder.add_check(ctx, return_type, &kind_of_return_type) else {
                return builder.build_fail(format!(
                    "Failed to check return type ... {return_type}: {kind_of_return_type}",
                ));
            };

            // 6. check each case has type eliminator_type of constructor
            // check length of cases and constructors
            if cases.len() != indty.constructors.len() {
                return builder.build_fail(format!(
                    "Constructor length mismatch: expected {}, found {}",
                    indty.constructors.len(),
                    cases.len()
                ));
            }

            // check (ctx |- cases[i] : eliminator_type[i])
            for (case, constructor) in cases.iter().zip(indty.constructors.iter()) {
                let eliminator_ty = eliminator_type(
                    constructor,
                    return_type,
                    elim,
                    &Exp::IndType {
                        indty: indty.clone(),
                        parameters: parameters.clone(),
                    },
                );
                let Some(()) = builder.add_check(ctx, case, &eliminator_ty) else {
                    return builder.build_fail(format!(
                        "Failed to check case {:?} against eliminator type {:?}",
                        case, eliminator_ty
                    ));
                };
            }

            // 8. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };

            builder.build_typeinfer(ty)
        }
        // type check (ctx |- exp: to)
        Exp::Cast { exp, to } => {
            builder.rule("Cast");

            // 1. check (ctx |- exp : to)
            let Some(()) = builder.add_check(ctx, exp, to) else {
                return builder.build_fail(format!(
                    "Failed to check casted expression {:?} against type {:?}",
                    exp, to
                ));
            };

            // 2. conclude (ctx |- Cast(exp, to) : to)
            builder.build_typeinfer(to.as_ref().clone())
        }
        Exp::ProveLater { prop } => {
            builder.rule("ProveLater");

            // 1. check (ctx |- exp : \Prop)
            let Some(()) = builder.add_check(ctx, prop, &Exp::Sort(Sort::Prop)) else {
                return builder.build_fail(format!(
                    "Failed to check proposition {:?} against type Prop in context",
                    prop
                ));
            };

            // 2. add goal (ctx |= exp)
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: Some(prop.as_ref().clone()),
            });

            // 3. conclude (ctx |- ProveLater(prop) : prop)
            builder.build_typeinfer(prop.as_ref().clone())
        }
        Exp::ProveHere { exp, goals } => {
            builder.rule("ProveHere");

            // 1. infer (ctx |- exp : ?ty)
            let Some(inferred_ty) = builder.add_infer(ctx, exp) else {
                return builder.build_fail("Failed to infer type of proof term expression");
            };

            // 2. we get all prove derivations (fail or success is cared later)
            let mut prove_ders: Vec<Derivation> = vec![];
            let mut fail: Option<usize> = None;

            for (
                i,
                ProveGoal {
                    extended_ctx,
                    goal_prop,
                    proof_term,
                },
            ) in goals.iter().enumerate()
            {
                let extended_ctx = ctx_extend_ctx(ctx, extended_ctx);

                let proved_goal = Prove {
                    ctx: extended_ctx.clone(),
                    prop: Some(goal_prop.clone()),
                };

                let prove_number = Rc::new(());

                // add (ctx::extended_ctx |- proof_term: goal_prop)
                let der = check(&extended_ctx, proof_term, goal_prop);
                if !der.node().unwrap().is_success() {
                    fail = Some(i);
                }

                let der = Derivation::Prove {
                    tree: Box::new(der),
                    proved: proved_goal.clone(),
                    num: prove_number.clone(),
                };

                prove_ders.push(der);
            }
            // if some goals failed, return fail derivation
            if let Some(i) = fail {
                for der in prove_ders {
                    builder.add(der);
                }
                return builder.build_fail(format!("Goal {} failed to prove", i + 1));
            }

            // 3. all goals are proved, now solve them
            if let Err(err) = builder.solve(prove_ders) {
                return builder.build_fail(err);
            }

            // 4. conclude (ctx |- ProveHere(exp, goals) : inferred_ty) where inferred_ty is infered at 1.
            builder.build_typeinfer(inferred_ty)
        }
        // (ctx |- ProofTermRaw(command) : prop) if (ctx |= prop) by command
        Exp::ProofTermRaw { command } => {
            builder.rule("ProofTermRaw");

            // 1. get (ctx |= prop) by command
            let Some(proved_goal) = builder.add_prove(prove_command(ctx, command.as_ref())) else {
                return builder
                    .build_fail(format!("Failed to prove proof term command {:?}", command));
            };

            // conclude (ctx |- ProofTermRaw(command) : prop)
            builder.build_typeinfer(proved_goal)
        }
        Exp::PowerSet { set: exp } => {
            builder.rule("PowerSet");

            // 1. check (ctx |- exp : Set(i))
            let Some(sort) = builder.add_sort(ctx, exp) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", exp));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", exp));
            };

            // 2. conclude (ctx |- PowerSet(exp) : Set(i))
            let ty = Exp::Sort(Sort::Set(i));
            builder.build_typeinfer(ty)
        }
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            builder.rule("SubSet");

            // 1. check (ctx |- set : Set(i))
            let Some(sort) = builder.add_sort(ctx, set) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", set));
            };
            let Sort::Set(_i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", set));
            };

            // 2. check (ctx::(var, set) |- predicate : \Prop)
            let extend = ctx_extend(ctx, (var.clone(), *set.clone()));
            let Some(()) = builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) else {
                return builder.build_fail(format!(
                    "Failed to check predicate {:?} against type Prop in extended context",
                    predicate
                ));
            };

            // 3. conclude (ctx |- SubSet(var, set, predicate) : Power(set))
            builder.build_typeinfer(Exp::PowerSet { set: set.clone() })
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            builder.rule("Pred");

            // 1. check (ctx |- superset : Set(i))
            let Some(sort) = builder.add_sort(ctx, superset) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", superset));
            };
            let Sort::Set(_i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", superset));
            };

            // 2. check (ctx |- subset : Power(superset))
            let Some(()) = builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            ) else {
                return builder.build_fail(format!(
                    "Failed to check subset {:?} against type Power(superset) in context",
                    subset
                ));
            };

            // 3. check (ctx |- element : superset)
            let Some(()) = builder.add_check(ctx, element, superset) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type superset in context",
                    element
                ));
            };
            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            builder.build_typeinfer(Exp::Sort(Sort::Prop))
        }
        Exp::TypeLift { superset, subset } => {
            builder.rule("TypeLift");
            // 1. check (ctx |- superset : Set(i))
            let Some(sort) = builder.add_sort(ctx, superset) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", superset));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", superset));
            };

            // 2. check (ctx |- subset : Power(superset))
            let Some(()) = builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            ) else {
                return builder.build_fail(format!(
                    "Failed to check subset {:?} against type Power(superset) in context",
                    subset
                ));
            };

            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            builder.build_typeinfer(Exp::Sort(Sort::Set(i)))
        }
        Exp::Equal { left, right } => {
            builder.rule("Equal");
            // 1. infer left type
            let Some(left_ty) = builder.add_infer(ctx, left) else {
                return builder.build_fail(format!(
                    "Failed to infer type of left expression {:?}",
                    left
                ));
            };

            // 2. infer right type
            let Some(right_ty) = builder.add_infer(ctx, right) else {
                return builder.build_fail(format!(
                    "Failed to infer type of right expression {:?}",
                    right
                ));
            };

            // 3. check convertibility
            if !convertible(&left_ty, &right_ty) {
                return builder.build_fail(format!(
                    "Type mismatch: left type {:?} is not convertible to right type {:?}",
                    left_ty, right_ty
                ));
            }
            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            builder.build_typeinfer(Exp::Sort(Sort::Prop))
        }
        Exp::Exists { set: ty } => {
            builder.rule("Exists");
            // 1. check (ctx |- ty : Set(i))
            let Some(_sort) = builder.add_sort(ctx, ty) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", ty));
            };
            let Sort::Set(_) = _sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", ty));
            };
            // 2. conclude (ctx |- Exists(ty) : \Prop)
            builder.build_typeinfer(Exp::Sort(Sort::Prop))
        }
        Exp::Take {
            map,
            domain,
            codomain,
        } => {
            builder.rule("Take");
            // 1. check (ctx |- domain : Set(i))
            let Some(sort) = builder.add_sort(ctx, domain) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", domain));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", domain));
            };

            // 2. check (ctx |- codomain : Set(j))
            let Some(sort) = builder.add_sort(ctx, codomain) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", codomain));
            };
            let Sort::Set(j) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(j)", codomain));
            };

            // 3. check i == j
            if i != j {
                return builder.build_fail(format!(
                    "Type mismatch: domain sort Set({}) is not equal to codomain sort Set({})",
                    i, j
                ));
            }

            // 4. check (ctx |- map : domain -> codomain)
            let func_type = Exp::Prod {
                var: Var::new("_"),
                ty: domain.clone(),
                body: codomain.clone(),
            };
            let Some(()) = builder.add_check(ctx, map, &func_type) else {
                return builder.build_fail(format!(
                    "Failed to check map {:?} against type domain -> codomain in context",
                    map
                ));
            };

            // 5. conclude (ctx |- Take(map, domain, codomain) : codomain)
            builder.build_typeinfer(codomain.as_ref().clone())
        }
    }
}

// infer_sort: (Derivation, Option<Sort>)
pub fn infer_sort(ctx: &Context, term: &Exp) -> Derivation {
    let mut builder = Builder::new(
        "InferSort".to_string(),
        "sort",
        Node::SortInfer(SortInfer {
            ctx: ctx.clone(),
            ty: term.clone(),
            sort: None,
        }),
    );

    // 1. infer type of term
    let Some(inferred_ty) = builder.add_infer(ctx, term) else {
        return builder.build_fail(format!("Failed to infer type of term {:?}", term));
    };

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return builder.build_fail(format!(
            "Type {:?} is not convertible to a sort",
            inferred_ty
        ));
    };

    builder.build_sortinfer(s)
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
pub fn prove_command(ctx: &Context, command: &ProveCommandBy) -> Derivation {
    let mut builder = Builder::new(
        "Subst Here (prove)".to_string(), // we will change rule name later
        "prove_command",
        Node::Prove(Prove {
            ctx: ctx.clone(),
            prop: None,
        }),
    );

    match command {
        ProveCommandBy::Construct { proof_term } => {
            builder.rule("Construct");

            // 1. infer (ctx |- proof_term : prop)
            let Some(prop) = builder.add_infer(ctx, proof_term) else {
                return builder.build_fail(format!(
                    "Failed to infer type of proof term {:?}",
                    proof_term
                ));
            };

            // 2. check prop: \Prop
            let Some(()) = builder.add_check(ctx, &prop, &Exp::Sort(Sort::Prop)) else {
                return builder.build_fail(format!(
                    "Inferred type {:?} of proof term {:?} is not of type Prop",
                    prop, proof_term
                ));
            };

            // 3. conclude (ctx |= prop)
            builder.build_prop(prop)
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            builder.rule("ExactElem");

            // 1. check (ctx |- elem : ty)
            let Some(()) = builder.add_check(ctx, elem, ty) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type {:?}",
                    elem, ty
                ));
            };

            // 2. (check ctx |- ty : Set(i)) for some i
            let Some(sort) = builder.add_sort(ctx, ty) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", ty));
            };
            let Sort::Set(_) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", ty));
            };

            // 3. conclude (ctx |= Exists(ty))
            let prop = Exp::Exists {
                set: Box::new(ty.clone()),
            };
            builder.build_prop(prop)
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
            let Some(()) = builder.add_check(ctx, elem, &typelift) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type Typelift({:?}, {:?})",
                    elem, superset, subset
                ));
            };

            // 2. check (ctx |- Typelift(superset, subset) : Set(i)) for some i
            let Some(_sort) = builder.add_sort(ctx, &typelift) else {
                return builder.build_fail(format!(
                    "Failed to infer sort of type Typelift({:?}, {:?})",
                    superset, subset
                ));
            };
            let Sort::Set(_) = _sort else {
                return builder.build_fail(format!(
                    "Type Typelift({:?}, {:?}) is not of form Set(i)",
                    superset, subset
                ));
            };

            // 3. conclude (ctx |= Pred(superset, subset, elem))
            let prop = Exp::Pred {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
                element: Box::new(elem.clone()),
            };
            builder.build_prop(prop)
        }
        ProveCommandBy::IdRefl { elem } => {
            builder.rule("IdRefl");

            // 1. infer (ctx |- elem : ?ty)
            // after
            let Some(ty) = builder.add_infer(ctx, elem) else {
                return builder.build_fail(format!("Failed to infer type of element {:?}", elem));
            };

            // 2. check (ctx |- ty : Set(i)) for some i
            let Some(sort) = builder.add_sort(ctx, &ty) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", ty));
            };
            let Sort::Set(_) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", ty));
            };

            // 3. conclude (ctx |= elem = elem)
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(elem.clone()),
            };
            builder.build_prop(prop)
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
                return builder.build_fail(format!("Failed to infer sort of type {:?}", ty));
            };
            let Sort::Set(_) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", ty));
            };

            // 2. check (ctx |- left : ty)
            let Some(()) = builder.add_check(ctx, left, ty) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type {:?}",
                    left, ty
                ));
            };

            // 3. check (ctx |- right : ty)
            let Some(()) = builder.add_check(ctx, right, ty) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type {:?}",
                    right, ty
                ));
            };

            // 4. check (ctx::(var, ty) |- predicate : Prop)
            let extend = ctx_extend(ctx, (var.clone(), ty.clone()));
            let Some(()) = builder.add_check(&extend, predicate, &Exp::Sort(Sort::Prop)) else {
                return builder.build_fail(format!(
                    "Failed to check predicate {:?} against type Prop in extended context",
                    predicate
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
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: Some(prop1.clone()),
            });

            // 6. add (ctx |= elem1 = elem2) as unproved goal
            let prop2 = Exp::Equal {
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: Some(prop2.clone()),
            });

            // 7. conclude (ctx |= predicate(right))
            let prop = Exp::App {
                func: Box::new(apply.clone()),
                arg: Box::new(right.clone()),
            };
            builder.build_prop(prop)
        }
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => {
            builder.rule("TakeEq");

            // 1. check (ctx |- Take(func, domain, codomain) : codomain)
            let take_ty = Exp::Take {
                map: Box::new(func.clone()),
                domain: Box::new(domain.clone()),
                codomain: Box::new(codomain.clone()),
            };
            let Some(()) = builder.add_check(ctx, &take_ty, codomain) else {
                return builder.build_fail(format!(
                    "Failed to check Take({:?}, {:?}, {:?}) against type {:?} in context",
                    func, domain, codomain, codomain
                ));
            };

            // 2. check (ctx |- elem : domain)
            let Some(()) = builder.add_check(ctx, elem, domain) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type {:?}",
                    elem, domain
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
            builder.build_prop(prop)
        }
        ProveCommandBy::Axiom(_axiom) => todo!("axiom implement later"),
    }
}

// return derivation of unproved Prove if exists
pub fn get_first_goal(der: &mut Derivation) -> Option<&mut Derivation> {
    match der {
        Derivation::Derivation {
            conclusion: _,
            premises,
            rule: _,
            meta: _,
        } => {
            for premise in premises {
                if let Some(goal) = get_first_goal(premise) {
                    return Some(goal);
                }
            }
            None
        }
        Derivation::UnSolved(_) => Some(der),
        Derivation::Prove {
            tree: _,
            proved: _,
            num: _,
        }
        | Derivation::Solved { target: _, num: _ }
        | Derivation::SolveFailed { target: _, num: _ } => None,
    }
}

pub fn check_wellformed_ctx(ctx: &Context) -> (Vec<Derivation>, Option<Derivation>) {
    let mut ders = vec![];
    let mut cur_ctx = vec![];
    for (v, ty) in ctx {
        let der = infer_sort(ctx, ty);
        if der.node().unwrap().is_success() {
            ders.push(der);
            cur_ctx.push((v.clone(), ty.clone()));
        } else {
            return (ders, Some(der));
        }
    }
    (ders, None)
}
