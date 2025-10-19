// All judgement functions return a Derivation (the trace) plus a payload indicating success/value.
// ? for output value

use std::rc::Rc;

use crate::inductive::eliminator_type;
use crate::utils;

use crate::calculus::*;
use crate::exp::*;

struct Builder {
    rule: String,
    meta: Meta,
    premises: Vec<Derivation>,
}

impl Builder {
    fn new(rule: String, meta: &str) -> Self {
        Self {
            rule,
            meta: Meta::Usual(meta.to_string()),
            premises: vec![],
        }
    }
    fn meta(&mut self, meta: &str) {
        self.meta = Meta::Usual(meta.to_string());
    }
    fn meta_through(&mut self, meta: &str) {
        self.meta = Meta::Through(meta.to_string());
    }
    fn add(&mut self, premise: Derivation) -> &mut Self {
        self.premises.push(premise);
        self
    }
    fn build(self, judgement: Judgement) -> Derivation {
        Derivation::Tree {
            conclusion: judgement,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
}

// check: (Derivation, bool) where bool = true on success
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> (Derivation, bool) {
    let mut builder = Builder::new("Conversion".to_string(), "check");

    // 1. infer (ctx |- term : ?inferred_ty)
    let (infer_derivation, infer_ty_opt) = infer(ctx, term);
    builder.add(infer_derivation);
    let inferred_ty = match infer_ty_opt {
        Some(t) => t,
        None => {
            return (
                builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Failed to infer type of term {:?}",
                    term
                )))),
                false,
            );
        }
    };

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if strict_equivalence(ty, &inferred_ty) {
        builder.meta_through("check");
        return (
            builder.build(Judgement::Type(TypeJudge {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: ty.clone(),
            })),
            true,
        );
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let (ty_sort_derivation, ty_sort_opt) = infer_sort(ctx, ty);
    builder.add(ty_sort_derivation);
    if ty_sort_opt.is_none() {
        return (
            builder.build(Judgement::FailJudge(FailJudge(format!(
                "Expected type {:?} is not well-sorted",
                ty
            )))),
            false,
        );
    }

    // 3 get normal(inferred_ty) and normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        builder.meta_through("check");
        return (
            builder.build(Judgement::Type(TypeJudge {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: ty.clone(),
            })),
            true,
        );
    }

    // 3-B-if check inferred_ty =(alpha)= TypeLift(ty, some) ... inferred_ty < ty
    // conclude (ctx |- term : ty) by subset weak rule
    if let Exp::TypeLift {
        superset,
        subset: _,
    } = &inferred_ty_result
    {
        if is_alpha_eq(superset.as_ref(), &ty) {
            builder.meta("SubsetWeak");
            return (
                builder.build(Judgement::Type(TypeJudge {
                    ctx: ctx.clone(),
                    term: term.clone(),
                    ty: ty.clone(),
                })),
                true,
            );
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return (
                builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type mismatch: inferred type {:?} is a TypeLift over {:?}, which is not equal to expected type {:?}",
                    inferred_ty_result, superset, ty
                )))),
                false,
            );
        }
    }

    // 3-C-if ty =(alpha)= TypeLift(inferred_ty, subset) ... ty < inferred_ty
    // conclude (ctx |- term : ty) by subset strong rule
    // add goal (ctx |= Pred(inferred_ty, subset, term))
    if let Exp::TypeLift { superset, subset } = &ty {
        if is_alpha_eq(superset.as_ref(), &inferred_ty_result) {
            builder.meta("SubsetStrong");
            // add goal (ctx |= Pred(inferred_ty, subset, term))
            builder.add(Derivation::stop(
                ctx.clone(),
                Exp::Pred {
                    superset: Box::new(inferred_ty_result),
                    subset: subset.clone(),
                    element: Box::new(term.clone()),
                },
            ));
            return (
                builder.build(Judgement::Type(TypeJudge {
                    ctx: ctx.clone(),
                    term: term.clone(),
                    ty: ty.clone(),
                })),
                true,
            );
        }
    }

    // 4. fails
    (
        builder.build(Judgement::FailJudge(FailJudge(format!(
            "Type mismatch: inferred type {:?} is not convertible to expected type {:?}",
            inferred_ty_result, ty
        )))),
        false,
    )
}

// infer: (Derivation, Option<Exp>) where Option<Exp> = Some(ty) on success
pub fn infer(ctx: &Context, term: &Exp) -> (Derivation, Option<Exp>) {
    let judgement_from_ty = |ty: &Exp| {
        Judgement::Type(TypeJudge {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: ty.clone(),
        })
    };

    match term {
        Exp::Sort(sort) => {
            let builder = Builder::new("Sort".to_string(), "infer");

            // 1. conclude (ctx: s: ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    (builder.build(judgement_from_ty(&ty)), Some(ty))
                }
                None => (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "No higher sort for sort {:?}",
                        sort
                    )))),
                    None,
                ),
            }
        }
        Exp::Var(index) => {
            let builder = Builder::new("Var".to_string(), "infer");

            // 1. (ctx |- var: ?ty) where (var: ty) in ctx
            match ctx.get(index) {
                Some(ty) => (builder.build(judgement_from_ty(ty)), Some(ty.clone())),
                None => (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Variable at index {} not found in context",
                        index
                    )))),
                    None,
                ),
            }
        }
        Exp::Prod { var, ty, body } => {
            let mut builder = Builder::new("Prod".to_string(), "infer");
            // 1. infer (ctx |- ty : ?s1)
            let (ty_sort_derivation, s1_opt) = infer_sort(ctx, ty);
            builder.add(ty_sort_derivation);
            let s1 = match s1_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            ty
                        )))),
                        None,
                    );
                }
            };
            let extend = ctx.extend((var.clone(), *ty.clone()));
            // 2. infer (ctx, ty |= body : ?s2)
            let (body_sort_derivation, s2_opt) = infer_sort(&extend, body);
            builder.add(body_sort_derivation);
            let s2 = match s2_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of body {:?}",
                            body
                        )))),
                        None,
                    );
                }
            };
            // 3. check (s1, s2) can form a product sort s3
            let s3 = match s1.relation_of_sort(s2) {
                Some(s3) => s3,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Cannot form product: {s1} {s2}",
                        )))),
                        None,
                    );
                }
            };

            // 4. conclude (ctx |- Prod(var, ty, body) : s3)
            let ty = Exp::Sort(s3);
            (builder.build(judgement_from_ty(&ty)), Some(ty))
        }
        Exp::Lam { var, ty, body } => {
            let mut builder = Builder::new("Lam".to_string(), "infer");

            // 1. infer (ctx |- ty : ?s) for some sort s
            let (ty_sort_derivation, ty_sort_opt) = infer_sort(ctx, ty);
            builder.add(ty_sort_derivation);
            if ty_sort_opt.is_none() {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))),
                    None,
                );
            }
            let extend = ctx.extend((var.clone(), *ty.clone()));

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let (body_derivation, body_ty_opt) = infer(&extend, body);
            builder.add(body_derivation);
            let body_ty = match body_ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of body {:?}",
                            body
                        )))),
                        None,
                    );
                }
            };
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            (builder.build(judgement_from_ty(&lam_ty)), Some(lam_ty))
        }
        Exp::App { func, arg } => {
            let mut builder = Builder::new("App".to_string(), "infer");
            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let (func_derivation, func_ty_opt) = infer(ctx, func);
            builder.add(func_derivation);
            let func_ty = match func_ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of function {:?}",
                            func
                        )))),
                        None,
                    );
                }
            };
            let Exp::Prod {
                var,
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Function type {:?} is not a product type",
                        func_ty
                    )))),
                    None,
                );
            };

            // 2. check (ctx |- arg : arg_ty)
            let (arg_check_derivation, arg_ok) = check(ctx, arg, &arg_ty);
            builder.add(arg_check_derivation);
            if !arg_ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check argument {:?} against type {:?}",
                        arg, arg_ty
                    )))),
                    None,
                );
            }
            let ret_ty_substituted = subst(&ret_ty, &var, arg);

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            (
                builder.build(judgement_from_ty(&ret_ty_substituted)),
                Some(ret_ty_substituted),
            )
        }
        Exp::IndType { ty, parameters } => {
            let mut builder = Builder::new("IndType".to_string(), "infer");
            let parameter_ty_defined = ty.parameters.clone();
            // 1. check parameters length
            if parameters.len() != parameter_ty_defined.len() {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Parameter length mismatch: expected {}, found {}",
                        parameter_ty_defined.len(),
                        parameters.len()
                    )))),
                    None,
                );
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
                let (derivation, ok) = check(ctx, param, &substituted_param_ty);
                builder.add(derivation);
                if !ok {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to check parameter {:?} against type {:?}",
                            param, substituted_param_ty
                        )))),
                        None,
                    );
                }
            }
            // 3. conclude (ctx |- IndType(ty, parameters) : arity_ty[] -> ty.sort)
            let arity_ty = ty.indices.clone();
            let arity = utils::assoc_prod(arity_ty, Exp::Sort(ty.sort));
            (builder.build(judgement_from_ty(&arity)), Some(arity))
        }
        Exp::IndCtor {
            ty,
            idx,
            parameters: parameter,
        } => {
            let mut builder = Builder::new("IndTypeCst".to_string(), "infer");
            let parameter_ty_defined = ty.parameters.clone();
            // 1. check parameter length
            if parameter.len() != parameter_ty_defined.len() {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Parameter length mismatch: expected {}, found {}",
                        parameter_ty_defined.len(),
                        parameter.len()
                    )))),
                    None,
                );
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
                let (derivation, ok) = check(ctx, param, &substituted_param_ty);
                builder.add(derivation);
                if !ok {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to check parameter {:?} against type {:?}",
                            param, substituted_param_ty
                        )))),
                        None,
                    );
                }
            }
            // 3. conclude (ctx |- IndTypeCst(ty, idx, parameter) : ty.Constructors[idx] where THIS = ty)
            let constructor_type = ty.constructors[*idx].as_exp_with_type(&Exp::IndType {
                ty: ty.clone(),
                parameters: parameter.clone(),
            });
            (
                builder.build(judgement_from_ty(&constructor_type)),
                Some(constructor_type),
            )
        }
        Exp::IndElim {
            ty,
            elim,
            return_type,
            sort,
            cases,
        } => {
            let mut builder = Builder::new("IndTypeElim".to_string(), "infer");
            // 1. check (ty.sort, sort) can form a elimination
            if ty.sort.relation_of_sort_indelim(*sort).is_none() {
                return (builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Cannot form eliminator with inductive type sort {:?} and return type sort {:?}",
                    ty.sort, sort
                )))), None);
            }
            // 2. infer (ctx |- elim : IndType(ty, parameters) a[])
            let (inferred_derivation, inferred_indty_opt) = infer(ctx, elim);
            builder.add(inferred_derivation);
            let inferred_indty = match inferred_indty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of eliminator expression {:?}",
                            elim
                        )))),
                        None,
                    );
                }
            };

            let (inferred_indty_base, a) = utils::decompose_app(inferred_indty);
            let Exp::IndType {
                ty: inferred_indty,
                parameters,
            } = inferred_indty_base
            else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Eliminator type {:?} is not an inductive type",
                        inferred_indty_base
                    )))),
                    None,
                );
            };

            // 3. check ty is the same as inferred ty
            if std::rc::Rc::ptr_eq(ty, &inferred_indty) {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Inductive type mismatch: expected {:?}, found {:?}",
                        ty, ty
                    )))),
                    None,
                );
            }

            // 4. check types of a[]: t[] in ty.arity_arg
            if ty.indices.len() != a.len() {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Arity length mismatch: expected {}, found {}",
                        ty.indices.len(),
                        a.len()
                    )))),
                    None,
                );
            }

            for ((_, arg_ty), arg) in ty.indices.iter().zip(a.iter()) {
                let (derivation, ok) = check(ctx, arg, arg_ty);
                builder.add(derivation);
                if !ok {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to check arity argument {:?} against type {:?}",
                            arg, arg_ty
                        )))),
                        None,
                    );
                }
            }

            // 5. check (ctx |- return_type: (x[]: t[]) -> THIS x[] -> s)
            // where (x[]: t[]) are in ty.arity_arg
            let expected_type_of_return_type = {
                // THIS x[] where x[] is ty.arity_arg's variables
                let e = utils::assoc_apply(
                    Exp::IndType {
                        ty: ty.clone(),
                        parameters: parameters.clone(),
                    },
                    ty.indices
                        .iter()
                        .map(|(x, _)| Exp::Var(x.clone()))
                        .collect(),
                );
                utils::assoc_prod(
                    ty.indices.clone(),
                    Exp::Prod {
                        var: Var::new("THIS"),
                        ty: Box::new(e),
                        body: Box::new(Exp::Sort(ty.sort)),
                    },
                )
            };
            let (ret_derivation, ret_ok) = check(ctx, return_type, &expected_type_of_return_type);
            builder.add(ret_derivation);
            if !ret_ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check return type {:?} against expected type {:?}",
                        return_type, expected_type_of_return_type
                    )))),
                    None,
                );
            }

            // 6. check each case has type eliminator_type of constructor
            // check length of cases and constructors
            if cases.len() != ty.constructors.len() {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Constructor length mismatch: expected {}, found {}",
                        ty.constructors.len(),
                        cases.len()
                    )))),
                    None,
                );
            }
            // check (ctx |- cases[i] : eliminator_type)
            for (case, constructor) in cases.iter().zip(ty.constructors.iter()) {
                let eliminator_ty = eliminator_type(
                    constructor,
                    return_type,
                    elim,
                    &Exp::IndType {
                        ty: ty.clone(),
                        parameters: parameters.clone(),
                    },
                );
                let (derivation, ok) = check(ctx, case, &eliminator_ty);
                builder.add(derivation);
                if !ok {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to check case {:?} against eliminator type {:?}",
                            case, eliminator_ty
                        )))),
                        None,
                    );
                }
            }

            // 7. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };

            (builder.build(judgement_from_ty(&ty)), Some(ty))
        }
        Exp::Cast { exp, to, withgoals } => {
            let mut builder = Builder::new("Cast".to_string(), "infer");
            // 1. simply, check (ctx |- exp : to)
            let (check_derivation, ok) = check(ctx, exp, to);
            builder.add(check_derivation);

            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check casted expression {:?} against type {:?}",
                        exp, to
                    )))),
                    None,
                );
            }

            // 2. we solve generated goals in derivation
            todo!();

            (builder.build(judgement_from_ty(to)), Some(*to.clone()))
        }
        Exp::ProveLater { prop: exp } => {
            // (ctx |- Proof(exp): exp) if (ctx |- exp : \PROP) and (ctx |= exp)
            let mut builder = Builder::new("Proof".to_string(), "infer");
            // 1. check (ctx |- exp : \PROP)
            let (derivation, ok) = check(ctx, exp, &Exp::Sort(Sort::Prop));
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check proof expression {:?} against type Prop",
                        exp
                    )))),
                    None,
                );
            }
            // 2. add goal (ctx |= exp)
            builder.add(Derivation::stop(ctx.clone(), *exp.clone()));
            // 3. conclude (ctx |- Proof(exp) : exp)
            (builder.build(judgement_from_ty(exp)), Some(*exp.clone()))
        }
        Exp::ProofTermRaw { command: command } => {
            // (ctx |- ProofTermRaw(command) : prop) if (ctx |= prop) by command

            let mut builder = Builder::new("ProofTermRaw".to_string(), "infer");

            // 1. get (ctx |= prop) by command
            let (der, ok) = prove_command(ctx, command.as_ref());
            if !ok {
                builder.add(der);
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to prove proof term command {:?}",
                        command
                    )))),
                    None,
                );
            }
            // unpack der to get prop
            let prop: Exp = {
                let Derivation::Tree {
                    conclusion,
                    premises: _,
                    rule: _,
                    meta: _,
                } = &der
                else {
                    unreachable!();
                };
                let Judgement::Provable(provable) = conclusion else {
                    unreachable!();
                };
                let Provable { ctx: _, prop } = provable.as_ref();
                prop.clone()
            };

            builder.add(der);

            // 2. conclude (ctx |- ProofTermRaw(command) : prop)
            (builder.build(judgement_from_ty(&prop)), Some(prop))
        }
        Exp::PowerSet { set: exp } => {
            let mut builder = Builder::new("PowerSet".to_string(), "infer");
            // 1. check (ctx |- exp : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, exp);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            exp
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(i) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        exp
                    )))),
                    None,
                );
            };
            let ty = Exp::Sort(Sort::Set(i));
            (builder.build(judgement_from_ty(&ty)), Some(ty))
        }
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            let mut builder = Builder::new("SubSet".to_string(), "infer");
            // 1. check (ctx |- exp : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, exp);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            exp
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(_) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        exp
                    )))),
                    None,
                );
            };
            let extend = ctx.extend((var.clone(), *exp.clone()));
            // 2. check (ctx, exp |- predicate : \PROP)
            let (derivation, ok) = check(&extend, predicate, &Exp::Sort(Sort::Prop));
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check predicate {:?} against type Prop in extended context",
                        predicate
                    )))),
                    None,
                );
            }
            // 3. conclude (ctx |- SubSet(var, exp, predicate) : Power(exp))
            (
                builder.build(judgement_from_ty(&Exp::PowerSet { set: exp.clone() })),
                Some(Exp::PowerSet { set: exp.clone() }),
            )
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            let mut builder = Builder::new("Pred".to_string(), "infer");
            // 1. check (ctx |- superset : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, superset);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            superset
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(_) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        superset
                    )))),
                    None,
                );
            };
            // 2. check (ctx |- subset : Power(superset))
            let (derivation, ok) = check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    )))),
                    None,
                );
            }
            // 3. check (ctx |- element : superset)
            let (derivation, ok) = check(ctx, element, superset);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type superset in context",
                        element
                    )))),
                    None,
                );
            }
            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            (
                builder.build(judgement_from_ty(&Exp::Sort(Sort::Prop))),
                Some(Exp::Sort(Sort::Prop)),
            )
        }
        Exp::TypeLift { superset, subset } => {
            let mut builder = Builder::new("TypeLift".to_string(), "infer");
            // 1. check (ctx |- superset : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, superset);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            superset
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(i) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        superset
                    )))),
                    None,
                );
            };
            // 2. check (ctx |- subset : Power(superset))
            let (derivation, ok) = check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    )))),
                    None,
                );
            }
            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            (
                builder.build(judgement_from_ty(&Exp::Sort(Sort::Set(i)))),
                Some(Exp::Sort(Sort::Set(i))),
            )
        }
        Exp::Equal { left, right } => {
            let mut builder = Builder::new("Equal".to_string(), "infer");
            // 1. infer left type
            let (derivation, left_ty_opt) = infer(ctx, left);
            builder.add(derivation);
            let left_ty = match left_ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of left expression {:?}",
                            left
                        )))),
                        None,
                    );
                }
            };
            // 2. infer right type
            let (derivation, right_ty_opt) = infer(ctx, right);
            builder.add(derivation);
            let right_ty = match right_ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of right expression {:?}",
                            right
                        )))),
                        None,
                    );
                }
            };
            // 3. check convertibility
            if !convertible(&left_ty, &right_ty) {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type mismatch: left type {:?} is not convertible to right type {:?}",
                        left_ty, right_ty
                    )))),
                    None,
                );
            }
            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            (
                builder.build(judgement_from_ty(&Exp::Sort(Sort::Prop))),
                Some(Exp::Sort(Sort::Prop)),
            )
        }
        Exp::Exists { set: ty } => {
            let mut builder = Builder::new("Exists".to_string(), "infer");
            // 1. check (ctx |- ty : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, ty);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            ty
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(_i) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        ty
                    )))),
                    None,
                );
            };
            // 2. conclude (ctx |- Exists(ty) : \Prop)
            (
                builder.build(judgement_from_ty(&Exp::Sort(Sort::Prop))),
                Some(Exp::Sort(Sort::Prop)),
            )
        }
        Exp::Take {
            map,
            domain,
            codomain,
        } => {
            let mut builder = Builder::new("Take".to_string(), "infer");
            // 1. check (ctx |- domain : Set(i))
            let (derivation, sort_opt) = infer_sort(ctx, domain);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            domain
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(i) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        domain
                    )))),
                    None,
                );
            };
            // 2. check (ctx |- codomain : Set(j))
            let (derivation, sort_opt) = infer_sort(ctx, codomain);
            builder.add(derivation);
            let sort = match sort_opt {
                Some(s) => s,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer sort of type {:?}",
                            codomain
                        )))),
                        None,
                    );
                }
            };
            let Sort::Set(j) = sort else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type {:?} is not of form Set(i)",
                        codomain
                    )))),
                    None,
                );
            };
            // 3. check i == j
            if i != j {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Type mismatch: domain sort Set({}) is not equal to codomain sort Set({})",
                        i, j
                    )))),
                    None,
                );
            }
            // 4. check (ctx |- map : domain -> codomain)
            let (derivation, ok) = check(
                ctx,
                map,
                &Exp::Prod {
                    var: Var::new("_"),
                    ty: domain.clone(),
                    body: codomain.clone(),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check map {:?} against type domain -> codomain in context",
                        map
                    )))),
                    None,
                );
            }
            // 5. conclude (ctx |- Take(map, domain, codomain) : codomain)
            let ty = codomain.as_ref().clone();
            (builder.build(judgement_from_ty(&ty)), Some(ty))
        }
    }
}

// infer_sort: (Derivation, Option<Sort>)
pub fn infer_sort(ctx: &Context, term: &Exp) -> (Derivation, Option<Sort>) {
    let mut builder = Builder::new("InferSort".to_string(), "sort");

    // 1. infer type of term
    let (der, sort_opt) = infer(ctx, term);
    builder.add(der);
    let Some(inferred_ty) = sort_opt else {
        return (
            builder.build(Judgement::FailJudge(FailJudge(format!(
                "Failed to infer type of term {:?}",
                term
            )))),
            None,
        );
    };

    // if inferred_ty is already sort, done
    if let Exp::Sort(s) = &inferred_ty {
        builder.meta_through("sort");
        return (
            builder.build(Judgement::Type(TypeJudge {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: Exp::Sort(*s),
            })),
            Some(*s),
        );
    }

    // converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return (
            builder.build(Judgement::FailJudge(FailJudge(format!(
                "Type {:?} is not convertible to a sort",
                inferred_ty
            )))),
            None,
        );
    };

    (
        builder.build(Judgement::Type(TypeJudge {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: Exp::Sort(s),
        })),
        Some(s),
    )
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
pub fn prove_command(ctx: &Context, command: &ProveCommandBy) -> (Derivation, bool) {
    let goal = |prop: Exp| {
        Judgement::Provable(Rc::new(Provable {
            ctx: ctx.clone(),
            prop,
        }))
    };

    match command {
        ProveCommandBy::Construct { proof_term } => {
            let mut builder = Builder::new("Construct".to_string(), "prove_command");

            // 1. infer (ctx |- proof_term : prop)
            let (derivation, prop_opt) = infer(ctx, &proof_term);
            builder.add(derivation);
            let prop = match prop_opt {
                Some(p) => p,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of proof term {:?}",
                            proof_term
                        )))),
                        false,
                    );
                }
            };

            // 2. check prop: \Prop
            let (derivation, ok) = check(ctx, &prop, &Exp::Sort(Sort::Prop));
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Inferred type {:?} of proof term {:?} is not of type Prop",
                        prop, proof_term
                    )))),
                    false,
                );
            }

            // 3. conclude (ctx |= prop)
            (builder.build(goal(prop)), true)
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            let mut builder = Builder::new("ExactElem".to_string(), "prove_command");
            let (derivation, ok) = check(ctx, &elem, &ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem, ty
                    )))),
                    false,
                );
            }
            let (derivation, sort_opt) = infer_sort(ctx, &ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Type {:?} is not of form Set(i)",
                            ty
                        )))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))),
                    false,
                );
            }
            let prop = Exp::Exists {
                set: Box::new(ty.clone()),
            };
            (builder.build(goal(prop)), true)
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
            let (derivation, ok) = check(ctx, &elem, &typelift);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type Typelift({:?}, {:?})",
                        elem, superset, subset
                    )))),
                    false,
                );
            }
            let (derivation, sort_opt) = infer_sort(ctx, &typelift);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Type Typelift({:?}, {:?}) is not of form Set(i)",
                            superset, subset
                        )))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type Typelift({:?}, {:?})",
                        superset, subset
                    )))),
                    false,
                );
            }
            let prop = Exp::Pred {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
                element: Box::new(elem.clone()),
            };
            (builder.build(goal(prop)), true)
        }
        ProveCommandBy::IdRefl { ctx, elem } => {
            let mut builder = Builder::new("IdRefl".to_string(), "prove_command");
            let (derivation, ty_opt) = infer(&ctx, &elem);
            builder.add(derivation);
            let ty = match ty_opt {
                Some(t) => t,
                None => {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Failed to infer type of element {:?}",
                            elem
                        )))),
                        false,
                    );
                }
            };
            let (derivation, sort_opt) = infer_sort(&ctx, &ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Type {:?} is not of form Set(i)",
                            ty
                        )))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))),
                    false,
                );
            }
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(elem.clone()),
            };
            (builder.build(goal(prop)), true)
        }
        ProveCommandBy::IdElim {
            ctx,
            elem1,
            elem2,
            ty,
            predicate,
        } => {
            let mut builder = Builder::new("IdElim".to_string(), "prove_command");
            let (derivation, ok) = check(&ctx, &elem1, &ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem1, ty
                    )))),
                    false,
                );
            }
            let (derivation, ok) = check(&ctx, &elem2, &ty);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem2, ty
                    )))),
                    false,
                );
            }
            let (derivation, sort_opt) = infer_sort(&ctx, &ty);
            builder.add(derivation);
            if let Some(sort) = sort_opt {
                if !matches!(sort, Sort::Set(_)) {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Type {:?} is not of form Set(i)",
                            ty
                        )))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))),
                    false,
                );
            }
            let (derivation, ok) = check(
                &ctx,
                &predicate,
                &Exp::Prod {
                    var: Var::new("_"),
                    ty: Box::new(*ty.clone()),
                    body: Box::new(Exp::Sort(Sort::Prop)),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check predicate {:?} against type {:?} -> Prop",
                        predicate, ty
                    )))),
                    false,
                );
            }
            let prop1 = Exp::App {
                func: Box::new(*predicate.clone()),
                arg: Box::new(elem1.clone()),
            };
            builder.add(Derivation::stop(ctx.clone(), prop1));
            let prop2 = Exp::Equal {
                left: Box::new(elem1.clone()),
                right: Box::new(elem2.clone()),
            };
            builder.add(Derivation::stop(ctx.clone(), prop2));
            let prop = Exp::App {
                func: Box::new(*predicate.clone()),
                arg: Box::new(elem2.clone()),
            };
            (builder.build(goal(prop)), true)
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
                &func,
                &Exp::Prod {
                    var: Var::new("_"),
                    ty: Box::new(*domain.clone()),
                    body: Box::new(*codomain.clone()),
                },
            );
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check function {:?} against type (_: {:?}) -> {:?}",
                        func, domain, codomain
                    )))),
                    false,
                );
            }
            let (derivation, ok) = check(ctx, &elem, &domain);
            builder.add(derivation);
            if !ok {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type {:?}",
                        elem, domain
                    )))),
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
                if !convertible(&ty, &codomain) {
                    return (
                        builder.build(Judgement::FailJudge(FailJudge(format!(
                            "Type mismatch: expected {:?}, found {:?}",
                            codomain, ty
                        )))),
                        false,
                    );
                }
            } else {
                return (
                    builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer type of Take function {:?}",
                        take_ty
                    )))),
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
            (builder.build(goal(prop)), true)
        }
        ProveCommandBy::Axiom(_axiom) => todo!(),
    }
}

// return derivation of provable judgement if exists
pub fn get_first_goal(der: &mut Derivation) -> Option<&mut Derivation> {
    match der {
        Derivation::Tree {
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
        Derivation::Stop(_) => Some(der),
    }
}
