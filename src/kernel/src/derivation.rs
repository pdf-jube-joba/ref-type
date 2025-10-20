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
    fn meta(&mut self, meta: &str) {
        self.meta = Meta::Usual(meta.to_string());
    }
    fn meta_through(&mut self, meta: &str) {
        self.meta = Meta::Through(meta.to_string());
    }

    fn add_check(&mut self, premise: Derivation) -> Option<()> {
        assert!(matches!(premise.node(), Some(Node::TypeCheck(_))));
        let TypeCheck { res, .. } = premise.node().unwrap().typecheck().unwrap();
        if !*res {
            self.premises.push(premise);
            None
        } else {
            self.premises.push(premise);
            Some(())
        }
    }
    fn add_infer(&mut self, premise: Derivation) -> Option<Exp> {
        assert!(matches!(premise.node(), Some(Node::TypeInfer(_))));
        let TypeInfer { ty, .. } = premise.node().unwrap().typeinfer().unwrap();
        if let Some(ty) = ty {
            let ty = ty.clone();
            self.premises.push(premise);
            Some(ty)
        } else {
            self.premises.push(premise);
            None
        }
    }
    fn add_sort(&mut self, premise: Derivation) -> Option<Sort> {
        assert!(matches!(premise.node(), Some(Node::TypeInfer(_))));
        let SortInfer { sort, .. } = premise.node().unwrap().sortinfer().unwrap();
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
        let Prove { res, prop, .. } = premise.node().unwrap().prove().unwrap();
        if !*res {
            self.premises.push(premise);
            None
        } else {
            let prop = prop.clone();
            self.premises.push(premise);
            Some(prop)
        }
    }
    fn add_unproved_goal(&mut self, unproved: Prove) {
        self.premises.push(Derivation::UnProved(unproved));
    }
    fn add(&mut self, der: Derivation) {
        self.premises.push(der);
    }
    fn build_typecheck(mut self) -> Derivation {
        let TypeCheck { res, .. } = self.node.typecheck_mut().unwrap();
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
        let TypeInfer { ty, .. } = &mut self.node.typeinfer_mut().unwrap();
        *ty = Some(ty_res);
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
    fn build_sortinfer(mut self, sort_res: Sort) -> Derivation {
        assert!(matches!(self.node, Node::TypeInfer(_)));
        let SortInfer { sort, .. } = &mut self.node.sortinfer_mut().unwrap();
        *sort = Some(sort_res);
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
        Derivation::Derivation {
            conclusion: self.node,
            premises: self.premises,
            rule: self.rule,
            meta: Meta::Fail(fail_reason.into()),
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
    let Some(inferred_ty) = builder.add_infer(infer(ctx, term)) else {
        return builder.build_fail("(ctx |- term: ?ty)(check");
    };

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if strict_equivalence(ty, &inferred_ty) {
        builder.meta_through("check");
        return builder.build_typecheck();
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let Some(_sort) = builder.add_sort(infer_sort(ctx, ty)) else {
        return builder.build_fail("(ctx |- ty: ?s)(check");
    };

    // 3 get normal(inferred_ty) and normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        return builder.build_typecheck();
    }

    // 3-B-if check inferred_ty =(alpha)= TypeLift(ty, some) ... inferred_ty < ty
    // conclude (ctx |- term : ty) by subset weak rule
    if let Exp::TypeLift {
        superset,
        subset: _,
    } = &inferred_ty_result
    {
        builder.meta("SubsetWeak");
        if is_alpha_eq(superset.as_ref(), &ty) {
            return builder.build_typecheck();
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return builder.build_fail("fail subset weak");
        }
    }

    // 3-C-if ty =(alpha)= TypeLift(inferred_ty, subset) ... ty < inferred_ty
    // conclude (ctx |- term : ty) by subset strong rule
    // add goal (ctx |= Pred(inferred_ty, subset, term))
    if let Exp::TypeLift { superset, subset } = &ty {
        builder.meta("SubsetStrong");
        if is_alpha_eq(superset.as_ref(), &inferred_ty_result) {
            // add goal (ctx |= Pred(inferred_ty, subset, term))
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: Exp::Pred {
                    superset: Box::new(inferred_ty_result),
                    subset: subset.clone(),
                    element: Box::new(term.clone()),
                },
                res: false,
            });
            return builder.build_typecheck();
        } else {
            // if ty =(alpha)= TypeLift(ty1, some) with ty1 != inferred_ty ... fails
            return builder.build_fail("fail subset strong");
        }
    }

    // 4. fails
    return builder.build_fail("ty, inferred_ty not convertible");
}

// infer: (Derivation, Option<Exp>) where Option<Exp> = Some(ty) on success
pub fn infer(ctx: &Context, term: &Exp) -> Derivation {
    let mut builder = Builder::new(
        "Subst Here (Infer)".to_string(),
        "infer",
        Node::TypeInfer(TypeInfer {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: None,
        }),
    );
    match term {
        Exp::Sort(sort) => {
            builder.meta("Sort");

            // 1. conclude (ctx |- s: ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    builder.build_typeinfer(ty)
                }
                None => builder.build_fail("no sort of sort found"),
            }
        }
        Exp::Var(index) => {
            builder.meta("Var");

            // 1. (ctx |- var: ?ty) where (var: ty) in ctx
            match ctx.get(index) {
                Some(ty) => builder.build_typeinfer(ty.clone()),
                None => builder.build_fail("not found"),
            }
        }
        Exp::Prod { var, ty, body } => {
            builder.meta("Prod");

            // 1. infer (ctx |- ty : ?s1)
            let Some(s1) = builder.add_sort(infer_sort(ctx, ty)) else {
                return builder.build_fail("fail s1");
            };

            // 2. infer (ctx:: (var, ty) |= body : ?s2)
            let extend = ctx.extend((var.clone(), *ty.clone()));
            let Some(s2) = builder.add_sort(infer_sort(&extend, body)) else {
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
            builder.meta("Lam");

            // 1. infer (ctx |- ty : ?s) for some sort s
            let Some(_sort) = builder.add_sort(infer_sort(ctx, ty)) else {
                return builder.build_fail("fail sort");
            };

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let extend = ctx.extend((var.clone(), *ty.clone()));
            let Some(body_ty) = builder.add_infer(infer(&extend, body)) else {
                return builder.build_fail("no type of body");
            };
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };

            // 3. conclude (ctx |- Lam(var, ty, body) : lam_ty)
            builder.build_typeinfer(lam_ty)
        }
        Exp::App { func, arg } => {
            builder.meta("App");

            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let Some(func_ty) = builder.add_infer(infer(ctx, func)) else {
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
            let Some(()) = builder.add_check(check(ctx, arg, &arg_ty)) else {
                return builder.build_fail("arg type mismatch");
            };

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            let ret_ty_substituted = subst(&ret_ty, &var, arg);
            builder.build_typeinfer(ret_ty_substituted)
        }
        Exp::IndType {
            indty: ty,
            parameters,
        } => {
            builder.meta("IndType");
            let parameter_ty_defined = ty.parameters.clone();
            // 1. check parameters length
            if parameters.len() != parameter_ty_defined.len() {
                return builder.build_fail("mismatch length");
            }
            // 2. check (ctx |- parameters[i] : parameter_ty_defined[i]) for each i
            //   (we need to substitute previous parameters into later parameter types)

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameters.iter().zip(parameter_ty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = subst(&substituted, v, e);
                    }
                    substituted
                };
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
                // check (ctx |- param : substituted_param_ty)
                let Some(()) = builder.add_check(check(ctx, param, &substituted_param_ty)) else {
                    return builder.build_fail("parameter type mismatch");
                };
            }
            // 3. conclude (ctx |- IndType(ty, parameters) : arity_ty[] -> ty.sort)
            let arity_ty = ty.indices.clone();
            let arity = utils::assoc_prod(arity_ty, Exp::Sort(ty.sort));
            builder.build_typeinfer(arity)
        }
        Exp::IndCtor {
            indty: ty,
            idx,
            parameters: parameter,
        } => {
            builder.meta("IndTypeCst");
            let parameter_ty_defined = ty.parameters.clone();
            // 1. check parameter length
            if parameter.len() != parameter_ty_defined.len() {
                return builder.build_fail("mismatch length");
            }

            // 2. check (ctx |- parameter[i] : parameter_ty_defined[i]) for each i
            //   (we need to substitute previous parameters into later parameter types)

            let mut subst_varexp: Vec<(Var, Exp)> = vec![];

            for (param, (var, param_ty)) in parameter.iter().zip(parameter_ty_defined.iter()) {
                // substitute previous parameters into param_ty
                let substituted_param_ty = {
                    let mut substituted = param_ty.clone();
                    for (v, e) in &subst_varexp {
                        substituted = subst(&substituted, v, e);
                    }
                    substituted
                };
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
                // check (ctx |- param : substituted_param_ty)
                let Some(()) = builder.add_check(check(ctx, param, &substituted_param_ty)) else {
                    return builder.build_fail("parameter type mismatch");
                };
            }
            // 3. conclude (ctx |- IndTypeCst(ty, idx, parameter) : ty.Constructors[idx] where THIS = ty)
            let constructor_type = ty.constructors[*idx].as_exp_with_type(&Exp::IndType {
                indty: ty.clone(),
                parameters: parameter.clone(),
            });
            builder.build_typeinfer(constructor_type)
        }
        Exp::IndElim {
            indty,
            elim,
            return_type,
            sort,
            cases,
        } => {
            builder.meta("IndTypeElim");
            // 1. check (ty.sort, sort) can form a elimination
            if indty.sort.relation_of_sort_indelim(*sort).is_none() {
                return builder.build_fail(format!(
                    "Cannot form eliminator with inductive type sort {:?} and return type sort {:?}",
                    indty.sort, sort
                ));
            }
            // 2. infer (ctx |- elim : IndType(ty, parameters) a[])
            let Some(inferred_indty) = builder.add_infer(infer(ctx, elim)) else {
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

            // 4. check types of a[]: t[] in ty.arity_arg
            if indty.indices.len() != a.len() {
                return builder.build_fail("mismatch arity length");
            }

            for ((_, arg_ty), arg) in indty.indices.iter().zip(a.iter()) {
                let Some(()) = builder.add_check(check(ctx, arg, arg_ty)) else {
                    return builder.build_fail(format!(
                        "Failed to check arity argument {:?} against type {:?}",
                        arg, arg_ty
                    ));
                };
            }

            // 5. check (ctx |- return_type: (x[]: t[]) -> THIS x[] -> s)
            // where (x[]: t[]) are in ty.arity_arg
            let expected_type_of_return_type = {
                // THIS x[] where x[] is ty.arity_arg's variables
                let e = utils::assoc_apply(
                    Exp::IndType {
                        indty: indty.clone(),
                        parameters: parameters.clone(),
                    },
                    indty
                        .indices
                        .iter()
                        .map(|(x, _)| Exp::Var(x.clone()))
                        .collect(),
                );
                utils::assoc_prod(
                    indty.indices.clone(),
                    Exp::Prod {
                        var: Var::new("THIS"),
                        ty: Box::new(e),
                        body: Box::new(Exp::Sort(indty.sort)),
                    },
                )
            };
            let Some(()) =
                builder.add_check(check(ctx, return_type, &expected_type_of_return_type))
            else {
                return builder.build_fail(format!(
                    "Failed to check return type {:?} against expected type {:?}",
                    return_type, expected_type_of_return_type
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

            // check (ctx |- cases[i] : eliminator_type)
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
                let Some(()) = builder.add_check(check(ctx, case, &eliminator_ty)) else {
                    return builder.build_fail(format!(
                        "Failed to check case {:?} against eliminator type {:?}",
                        case, eliminator_ty
                    ));
                };
            }

            // 7. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };

            builder.build_typeinfer(ty)
        }
        // type check (ctx |- exp: to) and solve all goal generated in derivation with `withgoals`
        Exp::Cast { exp, to, withgoals } => {
            builder.meta("Cast");

            // 1. simply, check (ctx |- exp : to)
            // we use check_derivation later, so we do not add it yet
            let mut check_derivation = check(ctx, exp, to);
            if !check_derivation.node().unwrap().is_success() {
                builder.add(check_derivation);
                return builder.build_fail(format!(
                    "Failed to check casted expression {:?} against type {:?}",
                    exp, to
                ));
            }

            // 2. we add all prove goals to derivation
            let mut goal_and_number: Vec<(Prove, Rc<()>)> = vec![];
            for ProveGoal {
                extended_ctx,
                goal_prop,
                proof_term,
            } in withgoals
            {
                let extended_ctx = ctx.extend_ctx(extended_ctx);

                let proved_goal = Prove {
                    ctx: extended_ctx.clone(),
                    prop: goal_prop.clone(),
                    res: false,
                };

                let prove_number = Rc::new(());

                // add (ctx::extended_ctx |- proof_term: goal_prop)
                let der = check(&extended_ctx, proof_term, goal_prop);
                if !der.node().unwrap().is_success() {
                    builder.add(der);
                    builder.add(check_derivation);
                    return builder
                        .build_fail(format!("Failed to prove cast goal {:?}", goal_prop));
                }

                let der = Derivation::Prove {
                    tree: Box::new(der),
                    proved: proved_goal.clone(),
                    num: prove_number.clone(),
                };

                builder.add(der);

                goal_and_number.push((proved_goal, prove_number));
            }

            // 3. solve each unproved goal in check_derivation with goal_and_number
            for (proved, prove_number) in goal_and_number {
                // get first unproved goal
                let Some(unproved_tree) = get_first_goal(&mut check_derivation) else {
                    builder.add(check_derivation);
                    return builder
                        .build_fail("No more goals to prove in cast derivation".to_string());
                };
                let Derivation::UnProved(unproved_goal) = &unproved_tree else {
                    unreachable!("get_first_goal should return UnProved");
                };

                // check unproved_goal and proved_goal are equivalent
                let b = crate::calculus::is_alpha_eq_prove(unproved_goal, &proved);
                if b {
                    *unproved_tree = Derivation::Proved {
                        target: unproved_goal.clone(),
                        num: prove_number,
                    };
                } else {
                    *unproved_tree = Derivation::ProveFailed {
                        target: unproved_goal.clone(),
                        num: prove_number,
                    };
                    builder.add(check_derivation);
                    return builder
                        .build_fail("Proved goal does not match unproved goal".to_string());
                }
            }

            // 4. check no more unproved goals remain
            if let Some(_) = get_first_goal(&mut check_derivation.clone()) {
                builder.add(check_derivation);
                return builder.build_fail("Some goals remain unproved in cast derivation");
            }

            // 5. conclude (ctx |- Cast(exp, to, withgoals) : to)
            builder.add(check_derivation);
            builder.build_typeinfer(to.as_ref().clone())
        }
        Exp::ProveLater { prop } => {
            // (ctx |- Proof(exp): exp) if (ctx |- exp : \Prop) and (ctx |= exp)
            builder.meta("ProveLater");
            // 1. check (ctx |- exp : \Prop)
            let mut builder = Builder::new(
                "ProveLater".to_string(),
                "infer",
                Node::TypeInfer(TypeInfer {
                    ctx: ctx.clone(),
                    term: term.clone(),
                    ty: None,
                }),
            );
            // 2. add goal (ctx |= exp)
            builder.add_unproved_goal(Prove {
                ctx: ctx.clone(),
                prop: prop.as_ref().clone(),
                res: false,
            });
            builder.build_typeinfer(prop.as_ref().clone())
        }
        // (ctx |- ProofTermRaw(command) : prop) if (ctx |= prop) by command
        Exp::ProofTermRaw { command } => {
            builder.meta("ProofTermRaw");

            // 1. get (ctx |= prop) by command
            let Some(proved_goal) = builder.add_prove(prove_command(ctx, command.as_ref())) else {
                return builder
                    .build_fail(format!("Failed to prove proof term command {:?}", command));
            };

            // conclude (ctx |- ProofTermRaw(command) : prop)
            builder.build_typeinfer(proved_goal)
        }
        Exp::PowerSet { set: exp } => {
            builder.meta("PowerSet");

            // 1. check (ctx |- exp : Set(i))
            let Some(sort) = builder.add_sort(infer_sort(ctx, exp)) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", exp));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", exp));
            };
            let ty = Exp::Sort(Sort::Set(i));
            // 2. conclude (ctx |- PowerSet(exp) : Set(i))
            builder.build_typeinfer(ty)
        }
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            builder.meta("SubSet");

            // 1. check (ctx |- exp : Set(i))
            let Some(sort) = builder.add_sort(infer_sort(ctx, set)) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", set));
            };
            let Sort::Set(_i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", set));
            };

            // 2. check (ctx::(var, exp) |- predicate : \Prop)
            let extend = ctx.extend((var.clone(), *set.clone()));
            let Some(()) = builder.add_check(check(&extend, predicate, &Exp::Sort(Sort::Prop)))
            else {
                return builder.build_fail(format!(
                    "Failed to check predicate {:?} against type Prop in extended context",
                    predicate
                ));
            };

            // 3. conclude (ctx |- SubSet(var, exp, predicate) : Power(exp))
            builder.build_typeinfer(Exp::PowerSet { set: set.clone() })
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            builder.meta("Pred");

            // 1. check (ctx |- superset : Set(i))
            let Some(_sort) = builder.add_sort(infer_sort(ctx, superset)) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", superset));
            };
            let Sort::Set(_) = _sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", superset));
            };

            // 2. check (ctx |- subset : Power(superset))
            let Some(()) = builder.add_check(check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            )) else {
                return builder.build_fail(format!(
                    "Failed to check subset {:?} against type Power(superset) in context",
                    subset
                ));
            };

            // 3. check (ctx |- element : superset)
            let Some(()) = builder.add_check(check(ctx, element, superset)) else {
                return builder.build_fail(format!(
                    "Failed to check element {:?} against type superset in context",
                    element
                ));
            };
            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            builder.build_typeinfer(Exp::Sort(Sort::Prop))
        }
        Exp::TypeLift { superset, subset } => {
            builder.meta("TypeLift");
            // 1. check (ctx |- superset : Set(i))
            let Some(sort) = builder.add_sort(infer_sort(ctx, superset)) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", superset));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", superset));
            };

            // 2. check (ctx |- subset : Power(superset))
            let Some(()) = builder.add_check(check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            )) else {
                return builder.build_fail(format!(
                    "Failed to check subset {:?} against type Power(superset) in context",
                    subset
                ));
            };

            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            builder.build_typeinfer(Exp::Sort(Sort::Set(i)))
        }
        Exp::Equal { left, right } => {
            builder.meta("Equal");
            // 1. infer left type
            let Some(left_ty) = builder.add_infer(infer(ctx, left)) else {
                return builder.build_fail(format!(
                    "Failed to infer type of left expression {:?}",
                    left
                ));
            };

            // 2. infer right type
            let Some(right_ty) = builder.add_infer(infer(ctx, right)) else {
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
            builder.meta("Exists");
            // 1. check (ctx |- ty : Set(i))
            let Some(_sort) = builder.add_sort(infer_sort(ctx, ty)) else {
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
            builder.meta("Take");
            // 1. check (ctx |- domain : Set(i))
            let Some(sort) = builder.add_sort(infer_sort(ctx, domain)) else {
                return builder.build_fail(format!("Failed to infer sort of type {:?}", domain));
            };
            let Sort::Set(i) = sort else {
                return builder.build_fail(format!("Type {:?} is not of form Set(i)", domain));
            };

            // 2. check (ctx |- codomain : Set(j))
            let Some(sort) = builder.add_sort(infer_sort(ctx, codomain)) else {
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
            let Some(()) = builder.add_check(check(ctx, map, &func_type)) else {
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
    let Some(ty_opt) = builder.add_infer(infer(ctx, term)) else {
        return builder.build_fail(format!("Failed to infer type of term {:?}", term));
    };

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return (
            builder.build_fail(FailJudge(format!(
                "Type {:?} is not convertible to a sort",
                inferred_ty
            ))),
            None,
        );
    };

    builder.build_sortinfer(s)
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
pub fn prove_command(ctx: &Context, command: &ProveCommandBy) -> Derivation {
    let goal = |prop: Exp| Provable {
        ctx: ctx.clone(),
        prop,
    };

    match command {
        ProveCommandBy::Construct { proof_term } => {
            let mut builder = Builder::new("Construct".to_string(), "prove_command");

            // 1. infer (ctx |- proof_term : prop)
            let (derivation, prop_opt) = infer(ctx, proof_term);
            builder.add(derivation);
            let prop = match prop_opt {
                Some(p) => p,
                None => {
                    return (
                        builder.build_fail(FailJudge(format!(
                            "Failed to infer type of proof term {:?}",
                            proof_term
                        ))),
                        false,
                    );
                }
            };

            // 2. check prop: \Prop
            let (derivation, ok) = check(ctx, &prop, &Exp::Sort(Sort::Prop));
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Inferred type {:?} of proof term {:?} is not of type Prop",
                        prop, proof_term
                    ))),
                    false,
                );
            }

            // 3. conclude (ctx |= prop)
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            let mut builder = Builder::new("ExactElem".to_string(), "prove_command");
            let (derivation, ok) = check(ctx, elem, ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem, ty
                    ))),
                    false,
                );
            }
            let (derivation, sort_opt) = infer_sort(ctx, ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder
                            .build_fail(FailJudge(format!("Type {:?} is not of form Set(i)", ty))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build_fail(FailJudge(format!("Failed to infer sort of type {:?}", ty))),
                    false,
                );
            }
            let prop = Exp::Exists {
                set: Box::new(ty.clone()),
            };
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => {
            let mut builder = Builder::new("SubsetElim".to_string(), "prove_command");
            let typelift = Exp::TypeLift {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
            };
            let (derivation, ok) = check(ctx, elem, &typelift);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check element {:?} against type Typelift({:?}, {:?})",
                        elem, superset, subset
                    ))),
                    false,
                );
            }
            let (derivation, sort_opt) = infer_sort(ctx, &typelift);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder.build_fail(FailJudge(format!(
                            "Type Typelift({:?}, {:?}) is not of form Set(i)",
                            superset, subset
                        ))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to infer sort of type Typelift({:?}, {:?})",
                        superset, subset
                    ))),
                    false,
                );
            }
            let prop = Exp::Pred {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
                element: Box::new(elem.clone()),
            };
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::IdRefl { elem } => {
            let mut builder = Builder::new("IdRefl".to_string(), "prove_command");
            let (derivation, ty_opt) = infer(ctx, elem);
            builder.add(derivation);
            let ty = match ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build_fail(FailJudge(format!(
                            "Failed to infer type of element {:?}",
                            elem
                        ))),
                        false,
                    );
                }
            };
            let (derivation, sort_opt) = infer_sort(ctx, &ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder
                            .build_fail(FailJudge(format!("Type {:?} is not of form Set(i)", ty))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build_fail(FailJudge(format!("Failed to infer sort of type {:?}", ty))),
                    false,
                );
            }
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(elem.clone()),
            };
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::IdElim {
            elem1,
            elem2,
            ty,
            var,
            predicate,
        } => {
            let mut builder = Builder::new("IdElim".to_string(), "prove_command");
            let (derivation, sort_opt) = infer_sort(ctx, ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder
                            .build_fail(FailJudge(format!("Type {:?} is not of form Set(i)", ty))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build_fail(FailJudge(format!("Failed to infer sort of type {:?}", ty))),
                    false,
                );
            }
            let (derivation, ok) = check(ctx, elem1, ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem1, ty
                    ))),
                    false,
                );
            }
            let (derivation, ok) = check(ctx, elem2, ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem2, ty
                    ))),
                    false,
                );
            }
            let (derivation, ok) = check(
                ctx,
                predicate,
                &Exp::Prod {
                    var: var.clone(),
                    ty: Box::new(*ty.clone()),
                    body: Box::new(Exp::Sort(Sort::Prop)),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check predicate {:?} against type {:?} -> Prop",
                        predicate, ty
                    ))),
                    false,
                );
            }
            let prop1 = Exp::App {
                func: Box::new(*predicate.clone()),
                arg: Box::new(elem1.clone()),
            };
            builder.add(Derivation::unproved(ctx.clone(), prop1));
            let prop2 = Exp::Equal {
                left: Box::new(elem1.clone()),
                right: Box::new(elem2.clone()),
            };
            builder.add(Derivation::unproved(ctx.clone(), prop2));
            let prop = Exp::App {
                func: Box::new(*predicate.clone()),
                arg: Box::new(elem2.clone()),
            };
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => {
            let mut builder = Builder::new("TakeEq".to_string(), "prove_command");
            let (derivation, ok) = check(
                ctx,
                func,
                &Exp::Prod {
                    var: Var::new("_"),
                    ty: Box::new(*domain.clone()),
                    body: Box::new(*codomain.clone()),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check function {:?} against type (_: {:?}) -> {:?}",
                        func, domain, codomain
                    ))),
                    false,
                );
            }
            let (derivation, ok) = check(ctx, elem, domain);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem, domain
                    ))),
                    false,
                );
            }
            let take_ty = Exp::Take {
                map: Box::new(*func.clone()),
                domain: Box::new(*domain.clone()),
                codomain: Box::new(*codomain.clone()),
            };
            let (derivation, ty_opt) = infer(ctx, &take_ty);
            builder.add(derivation);
            if let Some(ty) = ty_opt {
                if !convertible(&ty, codomain) {
                    return (
                        builder.build_fail(FailJudge(format!(
                            "Type mismatch: expected {:?}, found {:?}",
                            codomain, ty
                        ))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build_fail(FailJudge(format!(
                        "Failed to infer type of Take function {:?}",
                        take_ty
                    ))),
                    false,
                );
            }
            let prop = Exp::Equal {
                left: Box::new(take_ty),
                right: Box::new(Exp::App {
                    func: func.clone(),
                    arg: elem.clone(),
                }),
            };
            (builder.build_prop(goal(prop)), true)
        }
        ProveCommandBy::Axiom(_axiom) => todo!("axiom implement later"),
    }
}

// return derivation of provable judgement if exists
pub fn get_first_goal(der: &mut Derivation) -> Option<&mut Derivation> {
    match der {
        Derivation::TypeDerive {
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
        Derivation::PropDerive {
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
        Derivation::FailDerive {
            conclusion: _,
            premises: _,
            rule: _,
            meta: _,
        } => None,
        Derivation::UnProved(_) => Some(der),
        Derivation::Proved { target: _, num: _ }
        | Derivation::ProveFailed { target: _, num: _ } => None,
        Derivation::Prove {
            der: tree,
            num: _,
            prop: _,
        } => get_first_goal(tree),
    }
}
