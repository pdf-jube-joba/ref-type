use crate::calculus::*;
use crate::exp::*;
use crate::inductive::eliminator_type;
use crate::utils;
use std::rc::Rc;
use tracing::{debug, error};

macro_rules! add_check {
    ($rule:expr, $phase:expr, $ctx:expr, $term:expr, $ty:expr, $expected:expr $(,)?) => {
        check($ctx, $term, $ty)
            .map(|_| ())
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_infer {
    ($rule:expr, $phase:expr, $ctx:expr, $term:expr, $expected:expr $(,)?) => {
        infer($ctx, $term)
            .map(|result| result.type_of().expect("infer must produce a type").clone())
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_sort {
    ($rule:expr, $phase:expr, $ctx:expr, $term:expr, $expected:expr $(,)?) => {
        infer_sort($ctx, $term)
            .map(|result| match result.type_of() {
                Some(Exp::Sort(sort)) => *sort,
                _ => unreachable!("infer_sort must produce a sort"),
            })
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

fn success_checked() -> JudgementSuccess {
    debug!(target: "ref_type::typing", outcome = "success");
    JudgementSuccess {
        head: SuccessHead::Checked,
    }
}

fn success_type(ty: Exp) -> JudgementSuccess {
    debug!(target: "ref_type::typing", outcome = "success", result = ?ty);
    JudgementSuccess {
        head: SuccessHead::TypeJudgement { ty },
    }
}

fn failure(rule: &str, phase: &str, cause: &str) -> Box<JudgementError> {
    error!(target: "ref_type::typing", outcome = "failure", cause);
    Box::new(JudgementError::caused(cause).with_frame(rule, phase, "current judgement"))
}

fn propagate(
    error: Box<JudgementError>,
    rule: &str,
    phase: &str,
    expected: &str,
) -> Box<JudgementError> {
    Box::new(error.with_frame(rule, phase, expected))
}

// Check (ctx |- term : ty).
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> Result<JudgementSuccess, Box<JudgementError>> {
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "check",
        rule = "Check",
        ctx_len = ctx.len(),
        term = ?term,
        expected = ?ty,
    );
    let _entered = span.enter();
    let rule = "Check";
    let phase = "check";

    // 1. infer (ctx |- term : ?inferred_ty)
    let inferred_ty = add_infer!(rule, phase, ctx, term, "infer given term")?;

    // 2-if. inferred_ty == ty by strict equivalence => this function through the result
    if exp_strict_equivalence(ty, &inferred_ty) {
        return Ok(success_checked());
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let _sort = add_sort!(rule, phase, ctx, ty, "infer given")?;

    // 3 get normal(inferred_ty) & normal(ty)
    let inferred_ty_result = normalize(&inferred_ty);
    let ty = normalize(ty);

    // 3-A-if. check ty =(alpha)= inferred_ty
    // conclude (ctx |- term : ty) by conversion rule
    if convertible(&ty, &inferred_ty_result) {
        return Ok(success_checked());
    }

    // 3-B-if inferred_ty == s1, ty == s2 ... lift universe rule
    if let (Exp::Sort(s1), Exp::Sort(s2)) = (&inferred_ty_result, &ty) {
        if s1.can_lift_to(*s2) {
            return Ok(success_checked());
        } else {
            // if inferred_ty == s1, ty == s2 with s1 not liftable to s2 ... fails
            return Err(failure(rule, phase, "fail universe lift"));
        }
    }

    // 3-C-if check inferred_ty =(alpha)= TypeLift(ty, some) ... inferred_ty < ty
    // conclude (ctx |- term : ty) by subset weak rule
    if let Exp::TypeLift {
        superset,
        subset: _,
    } = &inferred_ty_result
    {
        if exp_is_alpha_eq(superset.as_ref(), &ty) {
            return Ok(success_checked());
        } else {
            // if inferred_ty =(alpha)= TypeLift(ty1, some) with ty1 != ty ... fails
            return Err(failure(rule, phase, "fail subset weak"));
        }
    }

    // 4. fails
    Err(failure(rule, phase, "ty, inferred_ty not convertible"))
}

// Infer a type while emitting the rule traversal through tracing spans.
pub fn infer(ctx: &Context, term: &Exp) -> Result<JudgementSuccess, Box<JudgementError>> {
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "infer",
        rule = exp_rule(term),
        ctx_len = ctx.len(),
        term = ?term,
    );
    let _entered = span.enter();
    let rule = exp_rule(term);
    let phase = "infer";

    match term {
        Exp::Sort(sort) => {
            // 1. conclude (ctx |- s : ?s1) where s: s1 in rules
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = Exp::Sort(sort_of_sort);
                    Ok(success_type(ty))
                }
                None => Err(failure(rule, phase, "no sort of sort found")),
            }
        }
        Exp::Var(index) => {
            // 1. conclude (ctx |- var : ?ty) where (var: ty) in ctx
            match ctx_get(ctx, index) {
                Some(ty) => Ok(success_type(ty.clone())),
                None => Err(failure(rule, phase, "var not found")),
            }
        }
        Exp::Prod { var, ty, body } => {
            // 1) infer (ctx |- ty : ?s1)
            let s1 = add_sort!(rule, phase, ctx, ty, "infer domain sort for product")?;

            // 2) infer (ctx, (var, ty) |- body : ?s2)
            let extend = ctx_extend(ctx, (var.clone(), *(*ty).clone()));
            let s2 = add_sort!(
                rule,
                phase,
                &extend,
                body,
                "infer codomain sort for product"
            )?;

            // 3) (s1, s2) から product sort s3 を得る
            match s1.relation_of_sort(s2) {
                Some(s3) => Ok(success_type(Exp::Sort(s3))),
                None => Err(failure(rule, phase, "no (s1, s2, s3) relation for product")),
            }
        }
        Exp::Lam { var, ty, body } => {
            // 1. infer (ctx |- ty : ?s) for some sort s
            let _sort = add_sort!(rule, phase, ctx, ty, "infer domain sort for lambda")?;

            // 2. infer (ctx, (var, ty) |- body : ?body_ty)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            let body_ty = add_infer!(rule, phase, &extend, body, "infer body type for lambda")?;

            // 3. conclude (ctx |- Lam(var, ty, body) : lam_ty)
            let lam_ty = Exp::Prod {
                var: var.clone(),
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            add_sort!(
                rule,
                phase,
                ctx,
                &lam_ty,
                "lambda product type should be well-sorted"
            )?;
            Ok(success_type(lam_ty))
        }
        Exp::App { func, arg } => {
            // 1. infer (ctx |- func : ?(x: arg_ty) -> ret_ty)
            let func_ty = add_infer!(
                rule,
                phase,
                ctx,
                func,
                "infer function type for application"
            )?;
            let Exp::Prod {
                var,
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return Err(failure(rule, phase, "type is not a product"));
            };

            // 2. check (ctx |- arg : arg_ty)
            add_check!(
                rule,
                phase,
                ctx,
                arg,
                &arg_ty,
                "check argument type for application"
            )?;

            // 3. conclude (ctx |- App(func, arg) : ret_ty[var := arg])
            let ret_ty_substituted = exp_subst(&ret_ty, &var, arg);
            Ok(success_type(ret_ty_substituted))
        }
        Exp::DefinedConstant(rc) => {
            // we assume rc: DefinedConstant is well-typed

            let DefinedConstant { ty, body: _ } = rc.as_ref();
            // conclude (ctx |- DefinedConstant(name, ty, inner) : ty)
            Ok(success_type(ty.clone()))
        }
        Exp::IndType {
            indspec,
            parameters,
        } => {
            let parameter_indty_defined = indspec.parameters.clone();

            // 1. check parameters length
            if parameters.len() != parameter_indty_defined.len() {
                return Err(failure(rule, phase, "Mismatch in parameter length"));
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
                add_check!(
                    rule,
                    phase,
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
            Ok(success_type(arity_substituted))
        }
        Exp::IndCtor {
            indspec,
            idx,
            parameters,
        } => {
            let parameter_indty_defined = indspec.parameters.clone();

            // 1. check parameter length
            if parameters.len() != parameter_indty_defined.len() {
                return Err(failure(rule, phase, "mismatch length"));
            }
            if *idx >= indspec.constructors.len() {
                return Err(failure(rule, phase, "constructor index out of bounds"));
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
                add_check!(
                    rule,
                    phase,
                    ctx,
                    param,
                    &substituted_param_ty,
                    "parameter type mismatch"
                )?;
                // push current (var, param) to subst_varexp
                subst_varexp.push((var.clone(), param.clone()));
            }

            // 3. conclude (ctx |- IndTypeCst(ty, idx, parameter) : ty.Constructors[idx] where THIS = ty)
            let constructor_type = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                indspec,
                *idx,
                parameters.clone(),
            );

            let subst_constructor_type = exp_subst_map(&constructor_type, &subst_varexp);

            Ok(success_type(subst_constructor_type))
        }
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            // 1. infer (ctx |- elim : IndType(ty, parameters) a[])
            let inferred_indty = add_infer!(rule, phase, ctx, elim, "infer eliminator type")?;
            let (inferred_indty_base, a) = utils::decompose_app(inferred_indty);
            let Exp::IndType {
                indspec: inferred_indty,
                parameters,
            } = inferred_indty_base
            else {
                return Err(failure(rule, phase, "type of elim is not inductive"));
            };

            // 2. check indty is the same as inferred_indty
            if !Rc::ptr_eq(indspec, &inferred_indty) {
                return Err(failure(rule, phase, "inductive type mismatch"));
            }
            let subst_varexp = indspec.parameter_subst_mapping(&parameters);

            // 3. infer kind of return_type
            let return_type_kind =
                add_infer!(rule, phase, ctx, return_type, "infer return type kind")?;
            let (telescope, sort) = utils::decompose_prod(normalize(&return_type_kind));
            let Exp::Sort(sort) = sort else {
                return Err(failure(
                    rule,
                    phase,
                    "return type kind not ending with a sort",
                ));
            };

            // 4. check (ty.sort, sort) can form an elimination
            if indspec.sort.relation_of_sort_indelim(sort).is_none() {
                return Err(failure(rule, phase, "cannot form eliminator"));
            }

            // 5. check convertibility of kind of return_type
            let expected_return_type_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
                indspec,
                parameters.clone(),
                sort,
            );
            let current_return_type_kind = utils::assoc_prod(telescope, Exp::Sort(sort));
            if !convertible(&current_return_type_kind, &expected_return_type_kind) {
                return Err(failure(
                    rule,
                    phase,
                    "return type kind is not convertible to expected",
                ));
            }

            // 6. check each case has type eliminator_type of constructor
            if cases.len() != indspec.constructors.len() {
                return Err(failure(rule, phase, "constructor length mismatch"));
            }

            for (idx, case) in cases.iter().enumerate() {
                let ctor_type = indspec.constructors[idx].subst(&subst_varexp);
                let ctor = Exp::IndCtor {
                    indspec: indspec.clone(),
                    parameters: parameters.clone(),
                    idx,
                };
                let eliminator_ty = eliminator_type(
                    &ctor_type,
                    return_type,
                    &ctor,
                    &Exp::IndType {
                        indspec: indspec.clone(),
                        parameters: parameters.clone(),
                    },
                );
                add_check!(rule, phase, ctx, case, &eliminator_ty, "check case type")?;
            }

            // 7. conclude (ctx |- IndTypeElim(ty, elim, return_type, sort, cases) : q a[] c)
            let ty = Exp::App {
                func: Box::new(utils::assoc_apply(*return_type.clone(), a.clone())),
                arg: elim.clone(),
            };
            Ok(success_type(ty))
        }
        // type check (ctx |- exp: to)
        Exp::Cast { exp, to, proof } => {
            let normalized_to = normalize(to);
            if let Exp::TypeLift { superset, subset } = &normalized_to {
                let inferred = add_infer!(rule, phase, ctx, exp, "infer refined expression")?;
                if !convertible(&inferred, superset) {
                    return Err(failure(
                        rule,
                        phase,
                        "refined expression has wrong superset type",
                    ));
                }
                let Some(proof) = proof else {
                    return Err(failure(
                        rule,
                        phase,
                        "refinement cast requires a membership proof",
                    ));
                };
                let membership = Exp::Pred {
                    superset: superset.clone(),
                    subset: subset.clone(),
                    element: exp.clone(),
                };
                add_check!(
                    rule,
                    phase,
                    ctx,
                    proof,
                    &membership,
                    "check refinement membership proof"
                )?;
            } else {
                if proof.is_some() {
                    return Err(failure(
                        rule,
                        phase,
                        "ordinary cast cannot have an obligation proof",
                    ));
                }
                add_check!(rule, phase, ctx, exp, to, "check casted expression")?;
            }

            Ok(success_type(to.as_ref().clone()))
        }
        Exp::PowerSet { set } => {
            // 1. check (ctx |- set : Set(?i))
            let sort = add_sort!(rule, phase, ctx, set, "check set sort")?;
            let Sort::Set(level) = sort else {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            };

            // 2. conclude (ctx |- PowerSet(set) : Set(i))
            Ok(success_type(Exp::Sort(Sort::Set(level))))
        }
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            // 1. check (ctx |- set : Set(?i))
            let sort = add_sort!(rule, phase, ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }

            // 2. check (ctx, (var, set) |- predicate : \Prop)
            let extended_ctx = ctx_extend(ctx, (var.clone(), *set.clone()));
            add_check!(
                rule,
                phase,
                &extended_ctx,
                predicate,
                &Exp::Sort(Sort::Prop),
                "check predicate",
            )?;

            // 3. conclude (ctx |- SubSet(var, set, predicate) : PowerSet(set))
            Ok(success_type(Exp::PowerSet { set: set.clone() }))
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            // add_sort!set(ctx, superset, "check superset sort")?;
            let sort = add_sort!(rule, phase, ctx, superset, "check superset sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            }

            // 2. check (ctx |- subset : PowerSet(superset))
            add_check!(
                rule,
                phase,
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
                "check subset type",
            )?;

            // 3. check (ctx |- element : superset)
            add_check!(rule, phase, ctx, element, superset, "check element type")?;

            // 4. conclude (ctx |- Pred(superset, subset, element) : \Prop)
            Ok(success_type(Exp::Sort(Sort::Prop)))
        }
        Exp::TypeLift { superset, subset } => {
            // 1. check (ctx |- superset : Set(i))
            let sort = add_sort!(rule, phase, ctx, superset, "check superset sort")?;
            let Sort::Set(level) = sort else {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            };

            // 2. check (ctx |- subset : PowerSet(superset))
            add_check!(
                rule,
                phase,
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
                "check subset type",
            )?;

            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            Ok(success_type(Exp::Sort(Sort::Set(level))))
        }
        Exp::Equal { left, right } => {
            // 1. infer (ctx |- left : ?ty)
            let left_ty = add_infer!(rule, phase, ctx, left, "infer left type")?;

            // 2. check (ctx |- left_ty : Set(i))
            let sort = add_sort!(rule, phase, ctx, &left_ty, "infer equality carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "equality carrier is not of Set(i)"));
            }

            // 3. check (ctx |- right : left_ty)
            add_check!(
                rule,
                phase,
                ctx,
                right,
                &left_ty,
                "check right element type"
            )?;

            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            Ok(success_type(Exp::Sort(Sort::Prop)))
        }
        Exp::Exists { set } => {
            // 1. check (ctx |- set : Set(i))
            let sort = add_sort!(rule, phase, ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }

            // 2. conclude (ctx |- Exists(set) : \Prop)
            Ok(success_type(Exp::Sort(Sort::Prop)))
        }
        Exp::Take {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => {
            // 1. check (ctx |- domain : Set(i))
            let domain_sort = add_sort!(rule, phase, ctx, domain, "check take domain sort")?;
            if !matches!(domain_sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "take domain is not of Set(i)"));
            }

            // 2. check codomain sort and (ctx |- map : domain -> codomain)
            let codomain_sort = add_sort!(rule, phase, ctx, codomain, "check take codomain sort")?;
            let map_ty = Exp::Prod {
                var: Var::dummy(),
                ty: domain.clone(),
                body: codomain.clone(),
            };
            add_check!(rule, phase, ctx, map, &map_ty, "check take map type")?;

            // 3. check (ctx |- map_ty : sort) with the expected sort side.
            let map_ty_sort = add_sort!(rule, phase, ctx, &map_ty, "check take map type sort")?;

            // 4. check the proof premises carried by the term.
            let existence_prop = Exp::Exists {
                set: domain.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                existence,
                &existence_prop,
                "check take existence proof",
            )?;
            match codomain_sort {
                Sort::Set(_) => {
                    if !matches!(map_ty_sort, Sort::Set(_)) {
                        return Err(failure(rule, phase, "take map type is not of Set(i)"));
                    }

                    let x1 = Var::new("x1");
                    let x2 = Var::new("x2");
                    let uniqueness_prop = Exp::Prod {
                        var: x1.clone(),
                        ty: domain.clone(),
                        body: Box::new(Exp::Prod {
                            var: x2.clone(),
                            ty: domain.clone(),
                            body: Box::new(Exp::Equal {
                                left: Box::new(Exp::App {
                                    func: map.clone(),
                                    arg: Box::new(Exp::Var(x1)),
                                }),
                                right: Box::new(Exp::App {
                                    func: map.clone(),
                                    arg: Box::new(Exp::Var(x2)),
                                }),
                            }),
                        }),
                    };
                    let Some(uniqueness) = uniqueness else {
                        return Err(failure(
                            rule,
                            phase,
                            "set-valued take requires a uniqueness proof",
                        ));
                    };
                    add_check!(
                        rule,
                        phase,
                        ctx,
                        uniqueness,
                        &uniqueness_prop,
                        "check take uniqueness proof",
                    )?;
                }
                Sort::Prop => {
                    if map_ty_sort != Sort::Prop {
                        return Err(failure(rule, phase, "take map type is not of Prop"));
                    }
                    if uniqueness.is_some() {
                        return Err(failure(
                            rule,
                            phase,
                            "proposition-valued take has no uniqueness proof",
                        ));
                    }
                }
                _ => {
                    return Err(failure(
                        rule,
                        phase,
                        "take codomain is neither Set(i) nor Prop",
                    ));
                }
            }

            // 5. conclude (ctx |- Take(domain, codomain, map) : codomain)
            Ok(success_type(codomain.as_ref().clone()))
        }
        Exp::ExistsIntro { .. }
        | Exp::SubsetElim { .. }
        | Exp::IdRefl { .. }
        | Exp::IdElim { .. }
        | Exp::TakeEq { .. } => infer_proof_constructor(ctx, term),
    }
}

fn exp_rule(term: &Exp) -> &'static str {
    match term {
        Exp::Sort(_) => "Sort",
        Exp::Var(_) => "Var",
        Exp::Prod { .. } => "Prod",
        Exp::Lam { .. } => "Lam",
        Exp::App { .. } => "App",
        Exp::DefinedConstant(_) => "DefinedConstant",
        Exp::IndType { .. } => "IndType",
        Exp::IndCtor { .. } => "IndCtor",
        Exp::IndElim { .. } => "IndTypeElim",
        Exp::Cast { .. } => "Cast",
        Exp::PowerSet { .. } => "PowerSet",
        Exp::SubSet { .. } => "SubSet",
        Exp::Pred { .. } => "Pred",
        Exp::TypeLift { .. } => "TypeLift",
        Exp::Equal { .. } => "Equal",
        Exp::Exists { .. } => "Exists",
        Exp::Take { .. } => "Take",
        Exp::ExistsIntro { .. } => "ExistsIntro",
        Exp::SubsetElim { .. } => "SubsetElim",
        Exp::IdRefl { .. } => "IdRefl",
        Exp::IdElim { .. } => "IdElim",
        Exp::TakeEq { .. } => "TakeEq",
    }
}

// infer sort of term
pub fn infer_sort(ctx: &Context, term: &Exp) -> Result<JudgementSuccess, Box<JudgementError>> {
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "infer_sort",
        rule = "Conv",
        ctx_len = ctx.len(),
        term = ?term,
    );
    let _entered = span.enter();
    let rule = "Conv";
    let phase = "infer(sort)";

    // 1. infer type of term
    let inferred_ty = add_infer!(rule, phase, ctx, term, "infer type of term")?;

    // 2-A. if inferred_ty is already a sort, through
    if let Exp::Sort(s) = inferred_ty {
        return Ok(success_type(Exp::Sort(s)));
    }

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = normalize(&inferred_ty) else {
        return Err(failure(rule, phase, "Type is not convertible to a sort"));
    };

    Ok(success_type(Exp::Sort(s)))
}

fn infer_proof_constructor(
    ctx: &Context,
    term: &Exp,
) -> Result<JudgementSuccess, Box<JudgementError>> {
    let rule = exp_rule(term);
    let phase = "infer";
    match term {
        Exp::ExistsIntro {
            element: elem,
            set: ty,
        } => {
            // 1. check (ctx |- elem : ty)
            add_check!(rule, phase, ctx, elem, ty, "check element type")?;

            // 2. check (ctx |- ty : Set(i)) for some i
            let sort = add_sort!(rule, phase, ctx, ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "type is not of Set(i)"));
            }

            // 3. return Exists(ty) as the term's inferred type
            let prop = Exp::Exists { set: ty.clone() };
            Ok(success_type(prop))
        }
        Exp::SubsetElim {
            element: elem,
            subset,
            superset,
        } => {
            // 1. check (ctx |- elem : Typelift(superset, subset))
            let typelift = Exp::TypeLift {
                superset: superset.clone(),
                subset: subset.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                elem,
                &typelift,
                "check subset elimination"
            )?;

            // 2. check (ctx |- Typelift(superset, subset) : Set(i)) for some i
            let sort = add_sort!(rule, phase, ctx, &typelift, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "type is not of Set(i)"));
            }

            // 3. return Pred(superset, subset, elem) as the term's inferred type
            let prop = Exp::Pred {
                superset: superset.clone(),
                subset: subset.clone(),
                element: elem.clone(),
            };
            Ok(success_type(prop))
        }
        Exp::IdRefl { element: elem } => {
            // 1. infer (ctx |- elem : ?ty)
            let ty = add_infer!(rule, phase, ctx, elem, "infer element type")?;

            // 2. check (ctx |- ty : Set(i)) for some i
            let sort = add_sort!(rule, phase, ctx, &ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "type is not of Set(i)"));
            }

            // 3. return elem = elem as the term's inferred type
            let prop = Exp::Equal {
                left: elem.clone(),
                right: elem.clone(),
            };
            Ok(success_type(prop))
        }
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => {
            // 1. check (ctx |- ty : Set(i)) for some i
            let sort = add_sort!(rule, phase, ctx, ty, "infer type sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "type is not of Set(i)"));
            }

            // 2. check (ctx |- left : ty)
            add_check!(rule, phase, ctx, left, ty, "check left element type")?;

            // 3. check (ctx |- right : ty)
            add_check!(rule, phase, ctx, right, ty, "check right element type")?;

            // 4. check (ctx::(var, ty) |- predicate : Prop)
            let extend = ctx_extend(ctx, (var.clone(), *ty.clone()));
            add_check!(
                rule,
                phase,
                &extend,
                predicate,
                &Exp::Sort(Sort::Prop),
                "check predicate in extended context",
            )?;

            // apply = (var: ty) => predicate
            let apply = Exp::Lam {
                var: var.clone(),
                ty: ty.clone(),
                body: predicate.clone(),
            };

            // 5. check the base case carried by the eliminator.
            let base_prop = Exp::App {
                func: Box::new(apply.clone()),
                arg: left.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                base,
                &base_prop,
                "check identity elimination base"
            )?;

            // 6. check the equality proof carried by the eliminator.
            let equality_prop = Exp::Equal {
                left: left.clone(),
                right: right.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                equality,
                &equality_prop,
                "check identity proof"
            )?;

            // 7. return predicate(right) as the term's inferred type
            let prop = Exp::App {
                func: Box::new(apply.clone()),
                arg: right.clone(),
            };
            Ok(success_type(prop))
        }
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element: elem,
            existence,
            uniqueness,
        } => {
            // 1. check (ctx |- Take(domain, codomain, func) : codomain)
            let take = Exp::Take {
                domain: domain.clone(),
                codomain: codomain.clone(),
                map: func.clone(),
                existence: existence.clone(),
                uniqueness: uniqueness.clone(),
            };
            add_check!(rule, phase, ctx, &take, codomain, "check take type")?;

            // 2. check (ctx |- func : (domain -> codomain))
            let func_ty = Exp::Prod {
                var: Var::dummy(),
                ty: domain.clone(),
                body: codomain.clone(),
            };
            add_check!(rule, phase, ctx, func, &func_ty, "check function type")?;

            // 3. check (ctx |- elem : domain)
            add_check!(rule, phase, ctx, elem, domain, "check element type")?;

            // 4. check (ctx |- func @ elem : codomain)
            let mapped_elem = Exp::App {
                func: func.clone(),
                arg: elem.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                &mapped_elem,
                codomain,
                "check mapped element type"
            )?;

            // 5. return the equality as the term's inferred type
            let prop = Exp::Equal {
                left: Box::new(take),
                right: Box::new(mapped_elem),
            };
            Ok(success_type(prop))
        }
        _ => unreachable!("infer_proof_constructor called for a non-proof constructor"),
    }
}

pub fn check_wellformed_ctx(ctx: &Context) -> (Vec<JudgementSuccess>, Option<Box<JudgementError>>) {
    let mut ders = vec![];
    let mut cur_ctx: Context = vec![];
    for (v, ty) in ctx {
        if cur_ctx.iter().any(|(existing, _)| existing.is_eq_ptr(v)) {
            return (
                ders,
                Some(Box::new(
                    JudgementError::caused("variable already exists in context").with_frame(
                        "ContextWellFormed",
                        "duplicate variable",
                        "unique context variable",
                    ),
                )),
            );
        }

        let der = infer_sort(&cur_ctx, ty);
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
