use crate::builder::Builder;
use crate::calculus::*;
use crate::exp::*;
use crate::inductive::eliminator_type;
use crate::utils;
use std::rc::Rc;

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
        Exp::DefinedConstant(rc) => {
            // we assume rc: DefinedConstant is well-typed
            builder.rule("DefinedConstant");

            let DefinedConstant { ty, body: _ } = rc.as_ref();
            // conclude (ctx |- DefinedConstant(name, ty, inner) : ty)
            Ok(builder.build_infer(ty.clone()))
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
            builder.add_check(ctx, exp, to, "check casted expression")?;

            // 2. conclude (ctx |- Cast(exp, to) : to)
            Ok(builder.build_infer(to.as_ref().clone()))
        }
        Exp::ProveLater { prop } => {
            builder.rule("ProveLater");

            // 1. check (ctx |- prop : \Prop)
            builder.add_check(ctx, prop, &Exp::Sort(Sort::Prop), "check proposition type")?;

            // 2. add goal (ctx |= prop)
            builder.add_unproved_goal(ctx.clone(), prop.as_ref().clone());

            // 3. conclude (ctx |- ProveLater(prop) : prop)
            Ok(builder.build_infer(prop.as_ref().clone()))
        }
        Exp::ProveHere { exp, goals } => {
            builder.rule("ProveHere");

            // 1. infer (ctx |- exp : ?ty)
            let inferred_ty = builder.add_infer(ctx, exp, "infer proof term type")?;

            // 2. for each goal in goals, prove (ctx_extended |= goal_prop) by command
            for ProveGoal {
                extended_ctx,
                goal_prop,
                command,
            } in goals.iter()
            {
                let extended_ctx = ctx_extend_ctx(ctx, extended_ctx);
                let prop = builder.add_proof(&extended_ctx, command.clone(), true)?;
                if !convertible(&prop, goal_prop) {
                    return Err(builder.cause("goal proposition mismatch"));
                }
            }
            // 3. check corresponding goals and proved goals match
            builder.resolve_goal()?;

            // 4. conclude (ctx |- ProveHere(exp, goals) : inferred_ty)
            Ok(builder.build_infer(inferred_ty))
        }
        // (ctx |- ProofTermRaw(command) : prop) if (ctx |= prop) by command
        Exp::ProofTermRaw { command } => {
            builder.rule("ProofTermRaw");
            // 1. prove (ctx |= prop) by command
            let prop = builder.add_proof(ctx, command.as_ref().clone(), false)?;
            Ok(builder.build_prop(prop))
        }
        Exp::PowerSet { set } => {
            builder.rule("PowerSet");

            // 1. check (ctx |- set : Set(?i))
            let sort = builder.add_sort(ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("set is not of Set(i)"));
            }

            // 2. conclude (ctx |- PowerSet(set) : Set(i))
            Ok(builder.build_infer(Exp::Sort(Sort::Set(0)))) // Replace `0` with the correct sort level if needed
        }
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            builder.rule("SubSet");

            // 1. check (ctx |- set : Set(?i))
            let sort = builder.add_sort(ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("set is not of Set(i)"));
            }

            // 2. check (ctx, (var, set) |- predicate : \Prop)
            let extended_ctx = ctx_extend(ctx, (var.clone(), *set.clone()));
            builder.add_check(
                &extended_ctx,
                predicate,
                &Exp::Sort(Sort::Prop),
                "check predicate",
            )?;

            // 3. conclude (ctx |- SubSet(var, set, predicate) : PowerSet(set))
            Ok(builder.build_infer(Exp::PowerSet { set: set.clone() }))
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            builder.rule("Pred");

            // builder.add_sortset(ctx, superset, "check superset sort")?;
            let sort = builder.add_sort(ctx, superset, "check superset sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("superset is not of Set(i)"));
            }

            // 2. check (ctx |- subset : PowerSet(superset))
            builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
                "check subset type",
            )?;

            // 3. check (ctx |- element : superset)
            builder.add_check(ctx, element, superset, "check element type")?;

            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            Ok(builder.build_infer(Exp::Sort(Sort::Prop)))
        }
        Exp::TypeLift { superset, subset } => {
            builder.rule("TypeLift");

            // 1. check (ctx |- superset : Set(i))
            let sort = builder.add_sort(ctx, superset, "check superset sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("superset is not of Set(i)"));
            }

            // 2. check (ctx |- subset : PowerSet(superset))
            builder.add_check(
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
                "check subset type",
            )?;

            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            Ok(builder.build_infer(Exp::Sort(Sort::Set(0)))) // Replace `0` with the correct sort level if needed
        }
        Exp::Equal { left, right } => {
            builder.rule("Equal");

            // 1. infer (ctx |- left : ?ty)
            let left_ty = builder.add_infer(ctx, left, "infer left type")?;

            // 2. infer (ctx |- right : ?ty)
            let right_ty = builder.add_infer(ctx, right, "infer right type")?;

            // 3. check convertibility of left_ty and right_ty
            if !convertible(&left_ty, &right_ty) {
                return Err(builder.cause("type mismatch between left and right"));
            }

            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            Ok(builder.build_infer(Exp::Sort(Sort::Prop)))
        }
        Exp::Exists { set } => {
            builder.rule("Exists");

            // 1. check (ctx |- set : Set(i))
            let sort = builder.add_sort(ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("set is not of Set(i)"));
            }

            // 2. conclude (ctx |- Exists(set) : \Prop)
            Ok(builder.build_infer(Exp::Sort(Sort::Prop)))
        }
        Exp::Take { map } => {
            builder.rule("Take");

            // 1. infer (ctx |- map : ?map_ty)
            let map_ty = builder.add_infer(ctx, map, "infer map type")?;

            // 2. decompose map_ty into (domain -> codomain)
            let Exp::Prod {
                var,
                ty: _domain,
                body: codomain,
            } = normalize(&map_ty)
            else {
                return Err(builder.cause("map type is not a function type"));
            };

            // 3. check codomain is independent of var
            if exp_contains_as_freevar(&codomain, &var) {
                return Err(builder.cause("codomain depends on variable"));
            }

            // 4. check (ctx |- map_ty : Set(i))
            let sort = builder.add_sort(ctx, &map_ty, "check map type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("map type is not of Set(i)"));
            }

            // 5. conclude (ctx |- Take(map) : codomain)
            Ok(builder.build_infer(*codomain))
        }
    }
}

// infer sort of term
pub fn infer_sort(ctx: &Context, term: &Exp) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new_infersort(ctx.clone(), term.clone());
    builder.rule("Conv");

    // 1. infer type of term
    let inferred_ty = builder.add_infer(ctx, term, "infer type of term")?;

    // 2-A. if inferred_ty is already a sort, through
    if let Exp::Sort(s) = inferred_ty {
        return Ok(builder.build_sort(s, true));
    }

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return Err(builder.cause("Type is not convertible to a sort"));
    };

    Ok(builder.build_sort(s, false))
}

// given ctx, return derivation of (ctx |= prop) with prop defined by command
pub fn prove_command(
    ctx: &Context,
    command: &ProveCommandBy,
) -> Result<DerivationSuccess, DerivationFail> {
    let mut builder = Builder::new_command(ctx.clone());
    match command {
        ProveCommandBy::Construct(exp) => {
            builder.rule("Construct");

            // 1. infer (ctx |- exp : prop)
            let prop = builder.add_infer(ctx, exp, "infer proof term")?;

            // 2. check prop: \Prop
            builder.add_check(ctx, &prop, &Exp::Sort(Sort::Prop), "check proposition type")?;

            // 3. conclude (ctx |= prop)
            Ok(builder.build_prop(prop))
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            builder.rule("ExactElem");

            // 1. check (ctx |- elem : ty)
            builder.add_check(ctx, elem, ty, "check element type")?;

            // 2. check (ctx |- ty : Set(i)) for some i
            let sort = builder.add_sort(ctx, ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("type is not of Set(i)"));
            }

            // 3. conclude (ctx |= Exists(ty))
            let prop = Exp::Exists {
                set: Box::new(ty.clone()),
            };
            Ok(builder.build_prop(prop))
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
            builder.add_check(ctx, elem, &typelift, "check subset elimination")?;

            // 2. check (ctx |- Typelift(superset, subset) : Set(i)) for some i
            let sort = builder.add_sort(ctx, &typelift, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("type is not of Set(i)"));
            }

            // 3. conclude (ctx |= Pred(superset, subset, elem))
            let prop = Exp::Pred {
                superset: Box::new(superset.clone()),
                subset: Box::new(subset.clone()),
                element: Box::new(elem.clone()),
            };
            Ok(builder.build_prop(prop))
        }
        ProveCommandBy::IdRefl { elem } => {
            builder.rule("IdRefl");

            // 1. infer (ctx |- elem : ?ty)
            let ty = builder.add_infer(ctx, elem, "infer element type")?;

            // 2. check (ctx |- ty : Set(i)) for some i
            let sort = builder.add_sort(ctx, &ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("type is not of Set(i)"));
            }

            // 3. conclude (ctx |= elem = elem)
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(elem.clone()),
            };
            Ok(builder.build_prop(prop))
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
            let sort = builder.add_sort(ctx, ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(builder.cause("type is not of Set(i)"));
            }

            // 2. check (ctx |- left : ty)
            builder.add_check(ctx, left, ty, "check left element type")?;

            // 3. check (ctx |- right : ty)
            builder.add_check(ctx, right, ty, "check right element type")?;

            // 4. check (ctx::(var, ty) |- predicate : Prop)
            let extend = ctx_extend(ctx, (var.clone(), ty.clone()));
            builder.add_check(
                &extend,
                predicate,
                &Exp::Sort(Sort::Prop),
                "check predicate in extended context",
            )?;

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
            builder.add_unproved_goal(ctx.clone(), prop1);

            // 6. add (ctx |= elem1 = elem2) as unproved goal
            let prop2 = Exp::Equal {
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            builder.add_unproved_goal(ctx.clone(), prop2);

            // 7. conclude (ctx |= predicate(right))
            let prop = Exp::App {
                func: Box::new(apply.clone()),
                arg: Box::new(right.clone()),
            };
            Ok(builder.build_prop(prop))
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
            builder.add_check(ctx, &take_ty, codomain, "check take type")?;

            // 2. check (ctx |- func : (domain -> codomain))
            let func_ty = Exp::Prod {
                var: Var::dummy(),
                ty: Box::new(domain.clone()),
                body: Box::new(codomain.clone()),
            };
            builder.add_check(ctx, func, &func_ty, "check function type")?;

            // 3. check (ctx |- elem : domain)
            builder.add_check(ctx, elem, domain, "check element type")?;

            // 4. conclude (ctx |= elem = Take(func)(elem))
            let take_app = Exp::App {
                func: Box::new(take_ty),
                arg: Box::new(elem.clone()),
            };
            let prop = Exp::Equal {
                left: Box::new(elem.clone()),
                right: Box::new(take_app),
            };
            Ok(builder.build_prop(prop))
        }
        ProveCommandBy::Axiom(_) => {
            todo!("implement axiom proving")
        }
    }
}

pub fn check_wellformed_ctx(ctx: &Context) -> (Vec<DerivationSuccess>, Option<DerivationFail>) {
    let mut ders = vec![];
    let mut cur_ctx = vec![];
    for (v, ty) in ctx {
        let der = infer_sort(ctx, ty);
        match der {
            Ok(success) => {
                ders.push(success);
                cur_ctx.push((v.clone(), ty.clone()));
            }
            Err(fail) => {
                return (ders, Some(fail));
            }
        }
    }
    (ders, None)
}
