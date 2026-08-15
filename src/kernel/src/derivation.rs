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
    ($arena:expr, $rule:expr, $phase:expr, $ctx:expr, $term:expr, $ty:expr, $expected:expr $(,)?) => {
        check($arena, $ctx, $term, $ty)
            .map(|_| ())
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_infer {
    ($arena:expr, $rule:expr, $phase:expr, $ctx:expr, $term:expr, $expected:expr $(,)?) => {
        infer($arena, $ctx, $term)
            .inspect(|ty| {
                debug!(target: "ref_type::typing", premise = $expected, result = ?ty);
            })
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_sort {
    ($arena:expr, $rule:expr, $phase:expr, $ctx:expr, $term:expr, $expected:expr $(,)?) => {
        infer_sort($arena, $ctx, $term)
            .inspect(|sort| {
                debug!(target: "ref_type::typing", premise = $expected, result = ?sort);
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

pub fn check(arena: &Arena, ctx: &Context, term: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
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
    let inferred_ty = add_infer!(arena, rule, phase, ctx, term, "infer given term")?;

    if matches!(arena.get(ty), Node::Sort(sort) if sort.type_of_sort().is_none())
        && exp_is_alpha_eq(arena, ty, inferred_ty)
    {
        return Ok(());
    }
    add_sort!(arena, rule, phase, ctx, ty, "infer expected type sort")?;
    if erased_convertible(arena, ty, inferred_ty) {
        return Ok(());
    }

    let inferred_head = type_head_normal(arena, inferred_ty);
    let expected_head = type_head_normal(arena, ty);
    if let (Node::Sort(inferred), Node::Sort(expected)) =
        (arena.get(inferred_head), arena.get(expected_head))
    {
        if inferred.can_lift_to(expected) {
            return Ok(());
        }
        return Err(failure(rule, phase, "fail universe lift"));
    }
    if can_weaken_to(arena, inferred_ty, ty) {
        return Ok(());
    }
    Err(failure(rule, phase, "ty, inferred_ty not convertible"))
}

pub fn infer(arena: &Arena, ctx: &Context, term: Exp) -> Result<Exp, Box<JudgementError>> {
    let rule = exp_rule(arena, term);
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "infer",
        rule,
        ctx_len = ctx.len(),
        term = ?term,
    );
    let _entered = span.enter();
    let phase = "infer";

    match arena.get(term) {
        Node::Sort(sort) => sort
            .type_of_sort()
            .map(|sort| arena.sort(sort))
            .ok_or_else(|| failure(rule, phase, "no sort of sort found")),
        Node::Bound(index) => ctx
            .get(ctx.len().checked_sub(index + 1).ok_or_else(|| {
                failure(rule, phase, "bound variable index is outside the context")
            })?)
            .map(|(_, ty)| shift_bound_indices(arena, *ty, index + 1, 0))
            .ok_or_else(|| failure(rule, phase, "bound variable index is outside the context")),
        Node::Var(var) => ctx_get(ctx, &var).ok_or_else(|| failure(rule, phase, "var not found")),
        Node::Prod { var, ty, body } => {
            let domain_sort =
                add_sort!(arena, rule, phase, ctx, ty, "infer domain sort for product")?;
            let mut extended = ctx.clone();
            extended.push((var, ty));
            let body_sort = add_sort!(
                arena,
                rule,
                phase,
                &extended,
                body,
                "infer codomain sort for product"
            )?;
            domain_sort
                .relation_of_sort(body_sort)
                .map(|sort| arena.sort(sort))
                .ok_or_else(|| failure(rule, phase, "no sort relation for product"))
        }
        Node::Lam { var, ty, body } => {
            add_sort!(arena, rule, phase, ctx, ty, "infer domain sort for lambda")?;
            let mut extended = ctx.clone();
            extended.push((var.clone(), ty));
            let body_ty = add_infer!(
                arena,
                rule,
                phase,
                &extended,
                body,
                "infer body type for lambda"
            )?;
            let lambda_ty = arena.alloc(Node::Prod {
                var,
                ty,
                body: body_ty,
            });
            add_sort!(
                arena,
                rule,
                phase,
                ctx,
                lambda_ty,
                "lambda product type should be well-sorted"
            )?;
            Ok(lambda_ty)
        }
        Node::App { func, arg } => {
            let func_ty = add_infer!(
                arena,
                rule,
                phase,
                ctx,
                func,
                "infer function type for application"
            )?;
            let Some((var, arg_ty, ret_ty)) = expose_product(arena, func_ty) else {
                return Err(failure(rule, phase, "type is not a product"));
            };
            add_check!(
                arena,
                rule,
                phase,
                ctx,
                arg,
                arg_ty,
                "check argument type for application"
            )?;
            Ok(instantiate(arena, ret_ty, &var, arg))
        }
        Node::DefinedConstant(definition) => Ok(definition.ty),
        Node::IndType {
            indspec,
            parameters,
        } => {
            check_parameters(arena, rule, phase, ctx, &parameters, indspec.parameters())?;
            let substitutions = indspec.parameter_subst_mapping(&parameters);
            Ok(exp_subst_map(arena, indspec.arity(arena), &substitutions))
        }
        Node::IndCtor {
            indspec,
            idx,
            parameters,
        } => {
            if idx >= indspec.constructor_len() {
                return Err(failure(rule, phase, "constructor index out of bounds"));
            }
            check_parameters(arena, rule, phase, ctx, &parameters, indspec.parameters())?;
            let substitutions = indspec.parameter_subst_mapping(&parameters);
            let constructor = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                arena, &indspec, idx, parameters,
            );
            Ok(exp_subst_map(arena, constructor, &substitutions))
        }
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => infer_ind_elim(arena, ctx, rule, phase, indspec, elim, return_type, cases),
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            let sort = add_sort!(arena, rule, phase, ctx, superset, "check carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "SubsetIntro carrier is not Set(i)"));
            }
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(arena, rule, phase, ctx, subset, power, "check subset")?;
            add_check!(arena, rule, phase, ctx, element, superset, "check element")?;
            let membership = arena.alloc(Node::Pred {
                superset,
                subset,
                element,
            });
            add_check!(
                arena,
                rule,
                phase,
                ctx,
                proof,
                membership,
                "check membership proof"
            )?;
            Ok(arena.alloc(Node::TypeLift { superset, subset }))
        }
        Node::PowerSet { set } => {
            match add_sort!(arena, rule, phase, ctx, set, "check set sort")? {
                Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
                _ => Err(failure(rule, phase, "set is not of Set(i)")),
            }
        }
        Node::SubSet {
            var,
            set,
            predicate,
        } => {
            if !matches!(
                add_sort!(arena, rule, phase, ctx, set, "check set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }
            let mut extended = ctx.clone();
            extended.push((var, set));
            let proposition = arena.sort(Sort::Prop);
            add_check!(
                arena,
                rule,
                phase,
                &extended,
                predicate,
                proposition,
                "check predicate"
            )?;
            Ok(arena.alloc(Node::PowerSet { set }))
        }
        Node::Pred {
            superset,
            subset,
            element,
        } => {
            if !matches!(
                add_sort!(arena, rule, phase, ctx, superset, "check superset sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            }
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(arena, rule, phase, ctx, subset, power, "check subset type")?;
            add_check!(
                arena,
                rule,
                phase,
                ctx,
                element,
                superset,
                "check element type"
            )?;
            Ok(arena.sort(Sort::Prop))
        }
        Node::TypeLift { superset, subset } => {
            let Sort::Set(level) =
                add_sort!(arena, rule, phase, ctx, superset, "check superset sort")?
            else {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            };
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(arena, rule, phase, ctx, subset, power, "check subset type")?;
            Ok(arena.sort(Sort::Set(level)))
        }
        Node::Equal { left, right } => {
            let left_ty = add_infer!(arena, rule, phase, ctx, left, "infer left type")?;
            let right_ty = add_infer!(arena, rule, phase, ctx, right, "infer right type")?;
            let Some(carrier) = common_ambient_carrier(arena, left_ty, right_ty) else {
                return Err(failure(rule, phase, "different equality carriers"));
            };
            if !matches!(
                add_sort!(arena, rule, phase, ctx, carrier, "infer carrier sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "equality carrier is not Set(i)"));
            }
            Ok(arena.sort(Sort::Prop))
        }
        Node::Exists { set } => {
            if !matches!(
                add_sort!(arena, rule, phase, ctx, set, "check set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }
            Ok(arena.sort(Sort::Prop))
        }
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => infer_take_set(
            arena, ctx, rule, phase, domain, codomain, map, existence, uniqueness,
        ),
        Node::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => infer_take_prop(arena, ctx, rule, phase, domain, proposition, map, existence),
        Node::ExistsIntro { .. }
        | Node::SubsetElim { .. }
        | Node::IdRefl { .. }
        | Node::IdElim { .. }
        | Node::TakeEq { .. } => infer_proof_constructor(arena, ctx, term),
    }
}

fn check_parameters(
    arena: &Arena,
    rule: &str,
    phase: &str,
    ctx: &Context,
    parameters: &[Exp],
    expected: &[(Var, Exp)],
) -> Result<(), Box<JudgementError>> {
    if parameters.len() != expected.len() {
        return Err(failure(rule, phase, "mismatch parameter length"));
    }
    let mut substitutions = vec![];
    for (parameter, (var, parameter_ty)) in parameters.iter().zip(expected) {
        let expected_ty = exp_subst_map(arena, *parameter_ty, &substitutions);
        add_check!(
            arena,
            rule,
            phase,
            ctx,
            *parameter,
            expected_ty,
            "parameter type mismatch"
        )?;
        substitutions.push((var.clone(), *parameter));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn infer_ind_elim(
    arena: &Arena,
    ctx: &Context,
    rule: &str,
    phase: &str,
    indspec: Rc<crate::inductive::InductiveTypeSpecs>,
    elim: Exp,
    return_type: Exp,
    cases: Vec<Exp>,
) -> Result<Exp, Box<JudgementError>> {
    let inferred = add_infer!(arena, rule, phase, ctx, elim, "infer eliminator type")?;
    let inferred = base_carrier(arena, inferred);
    let (head, indices) = utils::decompose_app(arena, inferred);
    let Node::IndType {
        indspec: inferred_spec,
        parameters,
    } = arena.get(head)
    else {
        return Err(failure(rule, phase, "type of elim is not inductive"));
    };
    if !Rc::ptr_eq(&indspec, &inferred_spec) {
        return Err(failure(rule, phase, "inductive type mismatch"));
    }
    let substitutions = indspec.parameter_subst_mapping(&parameters);
    let return_kind = add_infer!(
        arena,
        rule,
        phase,
        ctx,
        return_type,
        "infer return type kind"
    )?;
    let (telescope, result) = utils::decompose_prod(arena, type_head_normal(arena, return_kind));
    let Node::Sort(sort) = arena.get(result) else {
        return Err(failure(rule, phase, "return kind does not end in sort"));
    };
    if indspec.sort().relation_of_sort_indelim(sort).is_none() {
        return Err(failure(rule, phase, "cannot form eliminator"));
    }
    let expected_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
        arena,
        &indspec,
        parameters.clone(),
        sort,
    );
    let current_kind = utils::assoc_prod(arena, telescope, arena.sort(sort));
    if !erased_convertible(arena, current_kind, expected_kind) {
        return Err(failure(rule, phase, "unexpected return type kind"));
    }
    if cases.len() != indspec.constructor_len() {
        return Err(failure(rule, phase, "constructor length mismatch"));
    }
    let this = arena.alloc(Node::IndType {
        indspec: indspec.clone(),
        parameters: parameters.clone(),
    });
    for (index, case) in cases.iter().enumerate() {
        let constructor_ty = indspec.constructors()[index].subst(arena, &substitutions);
        let constructor = arena.alloc(Node::IndCtor {
            indspec: indspec.clone(),
            parameters: parameters.clone(),
            idx: index,
        });
        let case_ty = eliminator_type(arena, &constructor_ty, return_type, constructor, this);
        add_check!(arena, rule, phase, ctx, *case, case_ty, "check case type")?;
    }
    let motive = utils::assoc_apply(arena, return_type, indices);
    Ok(arena.alloc(Node::App {
        func: motive,
        arg: elim,
    }))
}

#[allow(clippy::too_many_arguments)]
fn infer_take_set(
    arena: &Arena,
    ctx: &Context,
    rule: &str,
    phase: &str,
    domain: Exp,
    codomain: Exp,
    map: Exp,
    existence: Exp,
    uniqueness: Exp,
) -> Result<Exp, Box<JudgementError>> {
    if !matches!(
        add_sort!(arena, rule, phase, ctx, domain, "check domain sort")?,
        Sort::Set(_)
    ) || !matches!(
        add_sort!(arena, rule, phase, ctx, codomain, "check codomain sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(
            rule,
            phase,
            "TakeSet domain/codomain is not Set(i)",
        ));
    }
    let map_ty = arena.alloc(Node::Prod {
        var: Var::dummy(),
        ty: domain,
        body: codomain,
    });
    add_check!(arena, rule, phase, ctx, map, map_ty, "check map type")?;
    let exists = arena.alloc(Node::Exists { set: domain });
    add_check!(
        arena,
        rule,
        phase,
        ctx,
        existence,
        exists,
        "check existence"
    )?;

    let x1 = Var::new("x1");
    let x2 = Var::new("x2");
    let map_x1 = arena.alloc(Node::App {
        func: map,
        arg: arena.var(x1.clone()),
    });
    let map_x2 = arena.alloc(Node::App {
        func: map,
        arg: arena.var(x2.clone()),
    });
    let equality = arena.alloc(Node::Equal {
        left: map_x1,
        right: map_x2,
    });
    let inner = arena.alloc(Node::Prod {
        var: x2,
        ty: domain,
        body: equality,
    });
    let uniqueness_ty = arena.alloc(Node::Prod {
        var: x1,
        ty: domain,
        body: inner,
    });
    add_check!(
        arena,
        rule,
        phase,
        ctx,
        uniqueness,
        uniqueness_ty,
        "check uniqueness"
    )?;
    Ok(codomain)
}

#[allow(clippy::too_many_arguments)]
fn infer_take_prop(
    arena: &Arena,
    ctx: &Context,
    rule: &str,
    phase: &str,
    domain: Exp,
    proposition: Exp,
    map: Exp,
    existence: Exp,
) -> Result<Exp, Box<JudgementError>> {
    if !matches!(
        add_sort!(arena, rule, phase, ctx, domain, "check domain sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "take domain is not Set(i)"));
    }
    if add_sort!(
        arena,
        rule,
        phase,
        ctx,
        proposition,
        "check proposition sort"
    )? != Sort::Prop
    {
        return Err(failure(rule, phase, "TakeProp codomain is not Prop"));
    }
    let map_ty = arena.alloc(Node::Prod {
        var: Var::dummy(),
        ty: domain,
        body: proposition,
    });
    add_check!(arena, rule, phase, ctx, map, map_ty, "check map")?;
    let exists = arena.alloc(Node::Exists { set: domain });
    add_check!(
        arena,
        rule,
        phase,
        ctx,
        existence,
        exists,
        "check existence"
    )?;
    Ok(proposition)
}

fn exp_rule(arena: &Arena, term: Exp) -> &'static str {
    match arena.get(term) {
        Node::Sort(_) => "Sort",
        Node::Bound(_) => "Bound",
        Node::Var(_) => "Var",
        Node::Prod { .. } => "Prod",
        Node::Lam { .. } => "Lam",
        Node::App { .. } => "App",
        Node::DefinedConstant(_) => "DefinedConstant",
        Node::IndType { .. } => "IndType",
        Node::IndCtor { .. } => "IndCtor",
        Node::IndElim { .. } => "IndTypeElim",
        Node::SubsetIntro { .. } => "SubsetIntro",
        Node::PowerSet { .. } => "PowerSet",
        Node::SubSet { .. } => "SubSet",
        Node::Pred { .. } => "Pred",
        Node::TypeLift { .. } => "TypeLift",
        Node::Equal { .. } => "Equal",
        Node::Exists { .. } => "Exists",
        Node::TakeSet { .. } => "TakeSet",
        Node::TakeProp { .. } => "TakeProp",
        Node::ExistsIntro { .. } => "ExistsIntro",
        Node::SubsetElim { .. } => "SubsetElim",
        Node::IdRefl { .. } => "IdRefl",
        Node::IdElim { .. } => "IdElim",
        Node::TakeEq { .. } => "TakeEq",
    }
}

pub fn infer_sort(arena: &Arena, ctx: &Context, term: Exp) -> Result<Sort, Box<JudgementError>> {
    let rule = "Conv";
    let phase = "infer(sort)";
    let inferred_ty = add_infer!(arena, rule, phase, ctx, term, "infer type of term")?;
    if let Node::Sort(sort) = arena.get(inferred_ty) {
        return Ok(sort);
    }
    let normalized = type_head_normal(arena, inferred_ty);
    let Node::Sort(sort) = arena.get(normalized) else {
        return Err(failure(rule, phase, "Type is not convertible to a sort"));
    };
    Ok(sort)
}

fn infer_proof_constructor(
    arena: &Arena,
    ctx: &Context,
    term: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let rule = exp_rule(arena, term);
    let phase = "infer";
    match arena.get(term) {
        Node::ExistsIntro { element, set } => {
            add_check!(arena, rule, phase, ctx, element, set, "check element")?;
            if !matches!(
                add_sort!(arena, rule, phase, ctx, set, "infer set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            Ok(arena.alloc(Node::Exists { set }))
        }
        Node::SubsetElim {
            element,
            subset,
            superset,
        } => {
            let lifted = arena.alloc(Node::TypeLift { superset, subset });
            add_check!(
                arena,
                rule,
                phase,
                ctx,
                element,
                lifted,
                "check subset elimination"
            )?;
            Ok(arena.alloc(Node::Pred {
                superset,
                subset,
                element,
            }))
        }
        Node::IdRefl { element } => {
            let ty = add_infer!(arena, rule, phase, ctx, element, "infer element type")?;
            if !matches!(
                add_sort!(arena, rule, phase, ctx, ty, "infer type sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            Ok(arena.alloc(Node::Equal {
                left: element,
                right: element,
            }))
        }
        Node::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => {
            if !matches!(
                add_sort!(arena, rule, phase, ctx, ty, "infer type sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            add_check!(arena, rule, phase, ctx, left, ty, "check left")?;
            add_check!(arena, rule, phase, ctx, right, ty, "check right")?;
            let mut extended = ctx.clone();
            extended.push((var.clone(), ty));
            let prop = arena.sort(Sort::Prop);
            add_check!(
                arena,
                rule,
                phase,
                &extended,
                predicate,
                prop,
                "check predicate"
            )?;
            let apply = arena.alloc(Node::Lam {
                var,
                ty,
                body: predicate,
            });
            let base_prop = arena.alloc(Node::App {
                func: apply,
                arg: left,
            });
            add_check!(arena, rule, phase, ctx, base, base_prop, "check base")?;
            let equality_prop = arena.alloc(Node::Equal { left, right });
            add_check!(
                arena,
                rule,
                phase,
                ctx,
                equality,
                equality_prop,
                "check equality"
            )?;
            Ok(arena.alloc(Node::App {
                func: apply,
                arg: right,
            }))
        }
        Node::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            let take = arena.alloc(Node::TakeSet {
                domain,
                codomain,
                map: func,
                existence,
                uniqueness,
            });
            add_check!(arena, rule, phase, ctx, take, codomain, "check take")?;
            add_check!(arena, rule, phase, ctx, element, domain, "check element")?;
            let mapped = arena.alloc(Node::App { func, arg: element });
            Ok(arena.alloc(Node::Equal {
                left: take,
                right: mapped,
            }))
        }
        _ => unreachable!(),
    }
}

pub fn check_wellformed_ctx(arena: &Arena, ctx: &Context) -> Result<(), Box<JudgementError>> {
    let mut current = vec![];
    for (var, ty) in ctx {
        if current
            .iter()
            .any(|(existing, _): &(Var, Exp)| existing.is_eq_ptr(var))
        {
            return Err(Box::new(
                JudgementError::caused("variable already exists in context").with_frame(
                    "ContextWellFormed",
                    "duplicate variable",
                    "unique context variable",
                ),
            ));
        }
        infer_sort(arena, &current, *ty)?;
        current.push((var.clone(), *ty));
    }
    Ok(())
}
