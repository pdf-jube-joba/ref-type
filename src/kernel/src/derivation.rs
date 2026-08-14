use crate::calculus::*;
use crate::exp::*;
use crate::inductive::eliminator_type;
use crate::utils;
use serde::Serialize;
use std::rc::Rc;
use tracing::{debug, error};

#[derive(Debug, Clone, Serialize)]
pub struct ErrorFrame {
    pub rule: String,
    pub phase: String,
    pub expected: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct JudgementError {
    pub cause: String,
    pub frames: Vec<ErrorFrame>,
}

impl JudgementError {
    pub fn caused(cause: impl Into<String>) -> Self {
        Self {
            cause: cause.into(),
            frames: Vec::new(),
        }
    }

    pub fn with_frame(
        mut self,
        rule: impl Into<String>,
        phase: impl Into<String>,
        expected: impl Into<String>,
    ) -> Self {
        self.frames.push(ErrorFrame {
            rule: rule.into(),
            phase: phase.into(),
            expected: expected.into(),
        });
        self
    }
}

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
            .inspect(|ty| {
                debug!(
                    target: "ref_type::typing",
                    premise = $expected,
                    result = ?ty,
                );
            })
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_sort {
    ($rule:expr, $phase:expr, $ctx:expr, $term:expr, $expected:expr $(,)?) => {
        infer_sort($ctx, $term)
            .inspect(|sort| {
                debug!(
                    target: "ref_type::typing",
                    premise = $expected,
                    result = ?sort,
                );
            })
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

fn failure(rule: &str, phase: &str, cause: &str) -> Box<JudgementError> {
    error!(target: "ref_type::typing", outcome = "failure", cause);
    Box::new(JudgementError::caused(cause).with_frame(rule, phase, "current judgement"))
}

fn propagate(
    mut error: Box<JudgementError>,
    rule: &str,
    phase: &str,
    expected: &str,
) -> Box<JudgementError> {
    error.frames.push(ErrorFrame {
        rule: rule.to_owned(),
        phase: phase.to_owned(),
        expected: expected.to_owned(),
    });
    error
}

// Check (ctx |- term : ty).
pub fn check(ctx: &Context, term: &Exp, ty: &Exp) -> Result<(), Box<JudgementError>> {
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

    // Top-level kinds have no sort of their own.  An already identical
    // inferred type must therefore be accepted before checking the expected
    // type's sort.
    if matches!(ty, Exp::Sort(sort) if sort.type_of_sort().is_none())
        && exp_is_alpha_eq(ty, &inferred_ty)
    {
        return Ok(());
    }

    // 2. check (ctx |- ty : ?s) for some sort s
    let _sort = add_sort!(rule, phase, ctx, ty, "infer given")?;

    // 3. Compare the original, checked types. Erasure remains internal to
    // conversion and its result is never sent back through typing.
    if erased_convertible(ty, &inferred_ty) {
        return Ok(());
    }

    // 3-B-if inferred_ty == s1, ty == s2 ... lift universe rule
    let inferred_ty_result = type_head_normal(&inferred_ty);
    let normalized_ty = type_head_normal(ty);
    if let (Exp::Sort(s1), Exp::Sort(s2)) = (&inferred_ty_result, &normalized_ty) {
        if s1.can_lift_to(*s2) {
            return Ok(());
        } else {
            // if inferred_ty == s1, ty == s2 with s1 not liftable to s2 ... fails
            return Err(failure(rule, phase, "fail universe lift"));
        }
    }

    // 3-C. conclude by the one-way subset weakening relation.
    if can_weaken_to(&inferred_ty, ty) {
        return Ok(());
    }

    // 4. fails
    Err(failure(rule, phase, "ty, inferred_ty not convertible"))
}

// Infer a type while emitting the rule traversal through tracing spans.
pub fn infer(ctx: &Context, term: &Exp) -> Result<Exp, Box<JudgementError>> {
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
                    Ok(ty)
                }
                None => Err(failure(rule, phase, "no sort of sort found")),
            }
        }
        Exp::Var(index) => {
            // 1. conclude (ctx |- var : ?ty) where (var: ty) in ctx
            match ctx_get(ctx, index) {
                Some(ty) => Ok(ty.clone()),
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
                Some(s3) => Ok(Exp::Sort(s3)),
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
            Ok(lam_ty)
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
            let Some((var, arg_ty, ret_ty)) = expose_product(&func_ty) else {
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
            Ok(ret_ty_substituted)
        }
        Exp::DefinedConstant(rc) => {
            // we assume rc: DefinedConstant is well-typed

            let DefinedConstant { ty, body: _ } = rc.as_ref();
            // conclude (ctx |- DefinedConstant(name, ty, inner) : ty)
            Ok(ty.clone())
        }
        Exp::IndType {
            indspec,
            parameters,
        } => {
            let parameter_indty_defined = indspec.parameters();

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
                    utils::assoc_prod(indspec.indices().to_vec(), Exp::Sort(indspec.sort()));
                for (v, e) in &subst_varexp {
                    substituted = exp_subst(&substituted, v, e);
                }
                substituted
            };
            Ok(arity_substituted)
        }
        Exp::IndCtor {
            indspec,
            idx,
            parameters,
        } => {
            let parameter_indty_defined = indspec.parameters();

            // 1. check parameter length
            if parameters.len() != parameter_indty_defined.len() {
                return Err(failure(rule, phase, "mismatch length"));
            }
            if *idx >= indspec.constructor_len() {
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

            Ok(subst_constructor_type)
        }
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            // 1. infer (ctx |- elim : IndType(ty, parameters) a[])
            let inferred_indty = add_infer!(rule, phase, ctx, elim, "infer eliminator type")?;
            // A refinement of an inductive type has the same computational
            // eliminator as its explicitly recorded carrier.  Observe that
            // carrier locally instead of globally erasing refinement types.
            let inferred_indty = base_carrier(&inferred_indty);
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
            let (telescope, sort) = utils::decompose_prod(type_head_normal(&return_type_kind));
            let Exp::Sort(sort) = sort else {
                return Err(failure(
                    rule,
                    phase,
                    "return type kind not ending with a sort",
                ));
            };

            // 4. check (ty.sort, sort) can form an elimination
            if indspec.sort().relation_of_sort_indelim(sort).is_none() {
                return Err(failure(rule, phase, "cannot form eliminator"));
            }

            // 5. check convertibility of kind of return_type
            let expected_return_type_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
                indspec,
                parameters.clone(),
                sort,
            );
            let current_return_type_kind = utils::assoc_prod(telescope, Exp::Sort(sort));
            if !erased_convertible(&current_return_type_kind, &expected_return_type_kind) {
                return Err(failure(
                    rule,
                    phase,
                    "return type kind is not convertible to expected",
                ));
            }

            // 6. check each case has type eliminator_type of constructor
            if cases.len() != indspec.constructor_len() {
                return Err(failure(rule, phase, "constructor length mismatch"));
            }

            for (idx, case) in cases.iter().enumerate() {
                let ctor_type = indspec.constructors()[idx].subst(&subst_varexp);
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
            Ok(ty)
        }
        // Introduce an element into an explicitly given subset of a carrier.
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            let sort = add_sort!(rule, phase, ctx, superset, "check refinement carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "SubsetIntro carrier is not of Set(i)"));
            }
            add_check!(
                rule,
                phase,
                ctx,
                subset,
                &Exp::PowerSet {
                    set: superset.clone(),
                },
                "check subset of refinement carrier"
            )?;
            add_check!(
                rule,
                phase,
                ctx,
                element,
                superset,
                "check refinement element"
            )?;
            let membership = Exp::Pred {
                superset: superset.clone(),
                subset: subset.clone(),
                element: element.clone(),
            };
            add_check!(
                rule,
                phase,
                ctx,
                proof,
                &membership,
                "check refinement membership proof"
            )?;

            Ok(Exp::TypeLift {
                superset: superset.clone(),
                subset: subset.clone(),
            })
        }
        Exp::PowerSet { set } => {
            // 1. check (ctx |- set : Set(?i))
            let sort = add_sort!(rule, phase, ctx, set, "check set sort")?;
            let Sort::Set(level) = sort else {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            };

            // 2. conclude (ctx |- PowerSet(set) : Set(i))
            Ok(Exp::Sort(Sort::Set(level)))
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
            Ok(Exp::PowerSet { set: set.clone() })
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
            Ok(Exp::Sort(Sort::Prop))
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
            Ok(Exp::Sort(Sort::Set(level)))
        }
        Exp::Equal { left, right } => {
            // 1. infer (ctx |- left : ?ty)
            let left_ty = add_infer!(rule, phase, ctx, left, "infer left type")?;

            // 2. Infer the right type independently and forget all refinement
            // layers on both sides. Equality is formed only when their base
            // carriers agree.
            let right_ty = add_infer!(rule, phase, ctx, right, "infer right type")?;
            let Some(carrier) = common_ambient_carrier(&left_ty, &right_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "equality operands have different base carriers",
                ));
            };

            // 3. check that the base carrier is a set.
            let sort = add_sort!(rule, phase, ctx, &carrier, "infer equality carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "equality carrier is not of Set(i)"));
            }

            // 4. conclude (ctx |- Equal(left, right) : \Prop)
            Ok(Exp::Sort(Sort::Prop))
        }
        Exp::Exists { set } => {
            // 1. check (ctx |- set : Set(i))
            let sort = add_sort!(rule, phase, ctx, set, "check set sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }

            // 2. conclude (ctx |- Exists(set) : \Prop)
            Ok(Exp::Sort(Sort::Prop))
        }
        Exp::TakeSet {
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

            // 2. check the set-valued codomain and map.
            let codomain_sort = add_sort!(rule, phase, ctx, codomain, "check take codomain sort")?;
            if !matches!(codomain_sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "TakeSet codomain is not of Set(i)"));
            }
            let map_ty = Exp::Prod {
                var: Var::dummy(),
                ty: domain.clone(),
                body: codomain.clone(),
            };
            add_check!(rule, phase, ctx, map, &map_ty, "check take map type")?;

            // 3. check the proof premises carried by the term.
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
            add_check!(
                rule,
                phase,
                ctx,
                uniqueness,
                &uniqueness_prop,
                "check take uniqueness proof",
            )?;

            // 4. conclude (ctx |- TakeSet(domain, codomain, map) : codomain)
            Ok(codomain.as_ref().clone())
        }
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => {
            // 1. check (ctx |- domain : Set(i))
            let domain_sort = add_sort!(rule, phase, ctx, domain, "check take domain sort")?;
            if !matches!(domain_sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "take domain is not of Set(i)"));
            }

            // 2. check the proposition-valued codomain and map.
            let proposition_sort =
                add_sort!(rule, phase, ctx, proposition, "check take proposition sort")?;
            if proposition_sort != Sort::Prop {
                return Err(failure(rule, phase, "TakeProp codomain is not of Prop"));
            }
            let map_ty = Exp::Prod {
                var: Var::dummy(),
                ty: domain.clone(),
                body: proposition.clone(),
            };
            add_check!(rule, phase, ctx, map, &map_ty, "check take map type")?;
            // 3. check the existence proof; no uniqueness proof is part of
            // the proposition-valued constructor.
            add_check!(
                rule,
                phase,
                ctx,
                existence,
                &Exp::Exists {
                    set: domain.clone(),
                },
                "check take existence proof",
            )?;

            Ok(proposition.as_ref().clone())
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
        Exp::SubsetIntro { .. } => "SubsetIntro",
        Exp::PowerSet { .. } => "PowerSet",
        Exp::SubSet { .. } => "SubSet",
        Exp::Pred { .. } => "Pred",
        Exp::TypeLift { .. } => "TypeLift",
        Exp::Equal { .. } => "Equal",
        Exp::Exists { .. } => "Exists",
        Exp::TakeSet { .. } => "TakeSet",
        Exp::TakeProp { .. } => "TakeProp",
        Exp::ExistsIntro { .. } => "ExistsIntro",
        Exp::SubsetElim { .. } => "SubsetElim",
        Exp::IdRefl { .. } => "IdRefl",
        Exp::IdElim { .. } => "IdElim",
        Exp::TakeEq { .. } => "TakeEq",
    }
}

// infer sort of term
pub fn infer_sort(ctx: &Context, term: &Exp) -> Result<Sort, Box<JudgementError>> {
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
        return Ok(s);
    }

    // 2. converting inferred_ty to sort
    let Exp::Sort(s) = type_head_normal(&inferred_ty) else {
        return Err(failure(rule, phase, "Type is not convertible to a sort"));
    };

    Ok(s)
}

fn infer_proof_constructor(ctx: &Context, term: &Exp) -> Result<Exp, Box<JudgementError>> {
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
            Ok(prop)
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
            Ok(prop)
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
            Ok(prop)
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
            Ok(prop)
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
            let take = Exp::TakeSet {
                domain: domain.clone(),
                codomain: codomain.clone(),
                map: func.clone(),
                existence: existence.clone(),
                uniqueness: uniqueness.clone(),
            };
            add_check!(rule, phase, ctx, &take, codomain, "check take type")?;

            // 2. check (ctx |- elem : domain)
            add_check!(rule, phase, ctx, elem, domain, "check element type")?;

            // 3. form (func @ elem); its type follows from the checked Take
            // and element premises.
            let mapped_elem = Exp::App {
                func: func.clone(),
                arg: elem.clone(),
            };

            // 4. return the equality as the term's inferred type
            let prop = Exp::Equal {
                left: Box::new(take),
                right: Box::new(mapped_elem),
            };
            Ok(prop)
        }
        _ => unreachable!("infer_proof_constructor called for a non-proof constructor"),
    }
}

pub fn check_wellformed_ctx(ctx: &Context) -> Result<(), Box<JudgementError>> {
    let mut cur_ctx: Context = vec![];
    for (v, ty) in ctx {
        if cur_ctx.iter().any(|(existing, _)| existing.is_eq_ptr(v)) {
            return Err(Box::new(
                JudgementError::caused("variable already exists in context").with_frame(
                    "ContextWellFormed",
                    "duplicate variable",
                    "unique context variable",
                ),
            ));
        }

        infer_sort(&cur_ctx, ty)?;
        cur_ctx.push((v.clone(), ty.clone()));
    }
    Ok(())
}
