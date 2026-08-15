use crate::calculus::*;
use crate::environment::CrateEnv;
use crate::exp::*;
use crate::inductive::eliminator_type;
use crate::utils;
use serde::Serialize;
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

pub struct CheckSession<'env, 'context> {
    env: &'env CrateEnv,
    current_module: ModuleId,
    context: &'context mut Context,
}

impl<'env, 'context> CheckSession<'env, 'context> {
    pub fn new(
        env: &'env CrateEnv,
        current_module: ModuleId,
        context: &'context mut Context,
    ) -> Self {
        Self {
            env,
            current_module,
            context,
        }
    }

    pub fn env(&self) -> &'env CrateEnv {
        self.env
    }

    pub fn arena(&self) -> &'env Arena {
        self.env.arena()
    }

    pub fn current_module(&self) -> ModuleId {
        self.current_module
    }

    pub fn context(&self) -> &Context {
        self.context
    }

    pub fn push(&mut self, var: Var, ty: Exp) {
        self.context.push((var, ty));
    }

    pub fn pop(&mut self) {
        self.context
            .pop()
            .expect("CheckSession context stack underflow");
    }

    pub fn check(&mut self, term: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
        check(self, term, ty)
    }

    pub fn infer(&mut self, term: Exp) -> Result<Exp, Box<JudgementError>> {
        infer(self, term)
    }

    pub fn infer_sort(&mut self, term: Exp) -> Result<Sort, Box<JudgementError>> {
        infer_sort(self, term)
    }

    pub fn check_wellformed_context(&mut self) -> Result<(), Box<JudgementError>> {
        check_wellformed_context(self)
    }
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
    ($session:expr, $rule:expr, $phase:expr, $term:expr, $ty:expr, $expected:expr $(,)?) => {
        $session
            .check($term, $ty)
            .map(|_| ())
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_infer {
    ($session:expr, $rule:expr, $phase:expr, $term:expr, $expected:expr $(,)?) => {
        $session.infer($term)
            .inspect(|ty| {
                debug!(target: "ref_type::typing", premise = $expected, result = ?ty);
            })
            .map_err(|error| propagate(error, $rule, $phase, $expected))
    };
}

macro_rules! add_sort {
    ($session:expr, $rule:expr, $phase:expr, $term:expr, $expected:expr $(,)?) => {
        $session.infer_sort($term)
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

fn check(
    session: &mut CheckSession<'_, '_>,
    term: Exp,
    ty: Exp,
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "check",
        rule = "Check",
        ctx_len = session.context.len(),
        term = ?term,
        expected = ?ty,
    );
    let _entered = span.enter();
    let rule = "Check";
    let phase = "check";
    let inferred_ty = add_infer!(session, rule, phase, term, "infer given term")?;

    if matches!(arena.get(ty), Node::Sort(sort) if sort.type_of_sort().is_none())
        && exp_is_alpha_eq(session.env(), ty, inferred_ty)
    {
        return Ok(());
    }
    add_sort!(session, rule, phase, ty, "infer expected type sort")?;
    if erased_convertible(session.env(), ty, inferred_ty) {
        return Ok(());
    }

    let inferred_head = type_head_normal(session.env(), inferred_ty);
    let expected_head = type_head_normal(session.env(), ty);
    if let (Node::Sort(inferred), Node::Sort(expected)) =
        (arena.get(inferred_head), arena.get(expected_head))
    {
        if inferred.can_lift_to(expected) {
            return Ok(());
        }
        return Err(failure(rule, phase, "fail universe lift"));
    }
    if can_weaken_to(session.env(), inferred_ty, ty) {
        return Ok(());
    }
    Err(failure(rule, phase, "ty, inferred_ty not convertible"))
}

fn infer(session: &mut CheckSession<'_, '_>, term: Exp) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = exp_rule(arena, term);
    let span = tracing::debug_span!(
        target: "ref_type::typing",
        "infer",
        rule,
        ctx_len = session.context.len(),
        term = ?term,
    );
    let _entered = span.enter();
    let phase = "infer";

    match arena.get(term) {
        Node::Sort(sort) => sort
            .type_of_sort()
            .map(|sort| arena.sort(sort))
            .ok_or_else(|| failure(rule, phase, "no sort of sort found")),
        Node::Bound(index) => session
            .context
            .get(
                session
                    .context
                    .len()
                    .checked_sub(index + 1)
                    .ok_or_else(|| {
                        failure(rule, phase, "bound variable index is outside the context")
                    })?,
            )
            .map(|(_, ty)| shift_bound_indices(arena, *ty, index + 1, 0))
            .ok_or_else(|| failure(rule, phase, "bound variable index is outside the context")),
        Node::Var(var) => {
            ctx_get(session.context, &var).ok_or_else(|| failure(rule, phase, "var not found"))
        }
        Node::Prod { var, ty, body } => {
            let domain_sort = add_sort!(session, rule, phase, ty, "infer domain sort for product")?;
            session.push(var, ty);
            let body_sort = add_sort!(
                session,
                rule,
                phase,
                body,
                "infer codomain sort for product"
            );
            session.pop();
            let body_sort = body_sort?;
            domain_sort
                .relation_of_sort(body_sort)
                .map(|sort| arena.sort(sort))
                .ok_or_else(|| failure(rule, phase, "no sort relation for product"))
        }
        Node::Lam { var, ty, body } => {
            add_sort!(session, rule, phase, ty, "infer domain sort for lambda")?;
            session.push(var.clone(), ty);
            let body_ty = add_infer!(session, rule, phase, body, "infer body type for lambda");
            session.pop();
            let body_ty = body_ty?;
            let lambda_ty = arena.alloc(Node::Prod {
                var,
                ty,
                body: body_ty,
            });
            add_sort!(
                session,
                rule,
                phase,
                lambda_ty,
                "lambda product type should be well-sorted"
            )?;
            Ok(lambda_ty)
        }
        Node::App { func, arg } => {
            let func_ty = add_infer!(
                session,
                rule,
                phase,
                func,
                "infer function type for application"
            )?;
            let Some((var, arg_ty, ret_ty)) = expose_product(session.env(), func_ty) else {
                return Err(failure(rule, phase, "type is not a product"));
            };
            add_check!(
                session,
                rule,
                phase,
                arg,
                arg_ty,
                "check argument type for application"
            )?;
            Ok(instantiate(arena, ret_ty, &var, arg))
        }
        Node::DefinedConstant(definition) => Ok(session.env().definition(definition).ty),
        Node::IndType {
            indspec,
            parameters,
        } => {
            let env = session.env();
            let spec = env.inductive(indspec);
            check_parameters(session, rule, phase, &parameters, spec.parameters())?;
            let substitutions = spec.parameter_subst_mapping(&parameters);
            Ok(exp_subst_map(arena, spec.arity(arena), &substitutions))
        }
        Node::IndCtor {
            indspec,
            idx,
            parameters,
        } => {
            let env = session.env();
            let spec = env.inductive(indspec);
            if idx >= spec.constructor_len() {
                return Err(failure(rule, phase, "constructor index out of bounds"));
            }
            check_parameters(session, rule, phase, &parameters, spec.parameters())?;
            let substitutions = spec.parameter_subst_mapping(&parameters);
            let constructor = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                arena, indspec, spec, idx, parameters,
            );
            Ok(exp_subst_map(arena, constructor, &substitutions))
        }
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => infer_ind_elim(session, rule, phase, indspec, elim, return_type, cases),
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            let sort = add_sort!(session, rule, phase, superset, "check carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "SubsetIntro carrier is not Set(i)"));
            }
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(session, rule, phase, subset, power, "check subset")?;
            add_check!(session, rule, phase, element, superset, "check element")?;
            let membership = arena.alloc(Node::Pred {
                superset,
                subset,
                element,
            });
            add_check!(
                session,
                rule,
                phase,
                proof,
                membership,
                "check membership proof"
            )?;
            Ok(arena.alloc(Node::TypeLift { superset, subset }))
        }
        Node::PowerSet { set } => match add_sort!(session, rule, phase, set, "check set sort")? {
            Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
            _ => Err(failure(rule, phase, "set is not of Set(i)")),
        },
        Node::SubSet {
            var,
            set,
            predicate,
        } => {
            if !matches!(
                add_sort!(session, rule, phase, set, "check set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }
            session.push(var, set);
            let proposition = arena.sort(Sort::Prop);
            let result = add_check!(
                session,
                rule,
                phase,
                predicate,
                proposition,
                "check predicate"
            );
            session.pop();
            result?;
            Ok(arena.alloc(Node::PowerSet { set }))
        }
        Node::Pred {
            superset,
            subset,
            element,
        } => {
            if !matches!(
                add_sort!(session, rule, phase, superset, "check superset sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            }
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(session, rule, phase, subset, power, "check subset type")?;
            add_check!(
                session,
                rule,
                phase,
                element,
                superset,
                "check element type"
            )?;
            Ok(arena.sort(Sort::Prop))
        }
        Node::TypeLift { superset, subset } => {
            let Sort::Set(level) =
                add_sort!(session, rule, phase, superset, "check superset sort")?
            else {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            };
            let power = arena.alloc(Node::PowerSet { set: superset });
            add_check!(session, rule, phase, subset, power, "check subset type")?;
            Ok(arena.sort(Sort::Set(level)))
        }
        Node::Equal { left, right } => {
            let left_ty = add_infer!(session, rule, phase, left, "infer left type")?;
            let right_ty = add_infer!(session, rule, phase, right, "infer right type")?;
            let Some(carrier) = common_ambient_carrier(session.env(), left_ty, right_ty) else {
                return Err(failure(rule, phase, "different equality carriers"));
            };
            if !matches!(
                add_sort!(session, rule, phase, carrier, "infer carrier sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "equality carrier is not Set(i)"));
            }
            Ok(arena.sort(Sort::Prop))
        }
        Node::Exists { set } => {
            if !matches!(
                add_sort!(session, rule, phase, set, "check set sort")?,
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
            session, rule, phase, domain, codomain, map, existence, uniqueness,
        ),
        Node::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => infer_take_prop(session, rule, phase, domain, proposition, map, existence),
        Node::ExistsIntro { .. }
        | Node::SubsetElim { .. }
        | Node::IdRefl { .. }
        | Node::IdElim { .. }
        | Node::TakeEq { .. } => infer_proof_constructor(session, term),
    }
}

fn check_parameters(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    parameters: &[Exp],
    expected: &[(Var, Exp)],
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    if parameters.len() != expected.len() {
        return Err(failure(rule, phase, "mismatch parameter length"));
    }
    let mut substitutions = vec![];
    for (parameter, (var, parameter_ty)) in parameters.iter().zip(expected) {
        let expected_ty = exp_subst_map(arena, *parameter_ty, &substitutions);
        add_check!(
            session,
            rule,
            phase,
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
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    indspec: InductiveId,
    elim: Exp,
    return_type: Exp,
    cases: Vec<Exp>,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let inferred = add_infer!(session, rule, phase, elim, "infer eliminator type")?;
    let inferred = base_carrier(session.env(), inferred);
    let (head, indices) = utils::decompose_app(arena, inferred);
    let Node::IndType {
        indspec: inferred_spec,
        parameters,
    } = arena.get(head)
    else {
        return Err(failure(rule, phase, "type of elim is not inductive"));
    };
    if indspec != inferred_spec {
        return Err(failure(rule, phase, "inductive type mismatch"));
    }
    let env = session.env();
    let spec = env.inductive(indspec);
    let substitutions = spec.parameter_subst_mapping(&parameters);
    let return_kind = add_infer!(session, rule, phase, return_type, "infer return type kind")?;
    let (telescope, result) = utils::decompose_prod(arena, type_head_normal(env, return_kind));
    let Node::Sort(sort) = arena.get(result) else {
        return Err(failure(rule, phase, "return kind does not end in sort"));
    };
    if spec.sort().relation_of_sort_indelim(sort).is_none() {
        return Err(failure(rule, phase, "cannot form eliminator"));
    }
    let expected_kind = crate::inductive::InductiveTypeSpecs::return_type_kind(
        arena,
        indspec,
        spec,
        parameters.clone(),
        sort,
    );
    let current_kind = utils::assoc_prod(arena, telescope, arena.sort(sort));
    if !erased_convertible(env, current_kind, expected_kind) {
        return Err(failure(rule, phase, "unexpected return type kind"));
    }
    if cases.len() != spec.constructor_len() {
        return Err(failure(rule, phase, "constructor length mismatch"));
    }
    let this = arena.alloc(Node::IndType {
        indspec,
        parameters: parameters.clone(),
    });
    for (index, case) in cases.iter().enumerate() {
        let constructor_ty = spec.constructors()[index].subst(arena, &substitutions);
        let constructor = arena.alloc(Node::IndCtor {
            indspec,
            parameters: parameters.clone(),
            idx: index,
        });
        let case_ty = eliminator_type(arena, &constructor_ty, return_type, constructor, this);
        add_check!(session, rule, phase, *case, case_ty, "check case type")?;
    }
    let motive = utils::assoc_apply(arena, return_type, indices);
    Ok(arena.alloc(Node::App {
        func: motive,
        arg: elim,
    }))
}

#[allow(clippy::too_many_arguments)]
fn infer_take_set(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    domain: Exp,
    codomain: Exp,
    map: Exp,
    existence: Exp,
    uniqueness: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    if !matches!(
        add_sort!(session, rule, phase, domain, "check domain sort")?,
        Sort::Set(_)
    ) || !matches!(
        add_sort!(session, rule, phase, codomain, "check codomain sort")?,
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
    add_check!(session, rule, phase, map, map_ty, "check map type")?;
    let exists = arena.alloc(Node::Exists { set: domain });
    add_check!(session, rule, phase, existence, exists, "check existence")?;

    let x1 = Var::new("x1");
    let x2 = Var::new("x2");
    let map = shift_bound_indices(arena, map, 2, 0);
    let map_x1 = arena.alloc(Node::App {
        func: map,
        arg: arena.bound(1),
    });
    let map_x2 = arena.alloc(Node::App {
        func: map,
        arg: arena.bound(0),
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
        session,
        rule,
        phase,
        uniqueness,
        uniqueness_ty,
        "check uniqueness"
    )?;
    Ok(codomain)
}

#[allow(clippy::too_many_arguments)]
fn infer_take_prop(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    domain: Exp,
    proposition: Exp,
    map: Exp,
    existence: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    if !matches!(
        add_sort!(session, rule, phase, domain, "check domain sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "take domain is not Set(i)"));
    }
    if add_sort!(session, rule, phase, proposition, "check proposition sort")? != Sort::Prop {
        return Err(failure(rule, phase, "TakeProp codomain is not Prop"));
    }
    let map_ty = arena.alloc(Node::Prod {
        var: Var::dummy(),
        ty: domain,
        body: proposition,
    });
    add_check!(session, rule, phase, map, map_ty, "check map")?;
    let exists = arena.alloc(Node::Exists { set: domain });
    add_check!(session, rule, phase, existence, exists, "check existence")?;
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

fn infer_sort(session: &mut CheckSession<'_, '_>, term: Exp) -> Result<Sort, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Conv";
    let phase = "infer(sort)";
    let inferred_ty = add_infer!(session, rule, phase, term, "infer type of term")?;
    if let Node::Sort(sort) = arena.get(inferred_ty) {
        return Ok(sort);
    }
    let normalized = type_head_normal(session.env(), inferred_ty);
    let Node::Sort(sort) = arena.get(normalized) else {
        return Err(failure(rule, phase, "Type is not convertible to a sort"));
    };
    Ok(sort)
}

fn infer_proof_constructor(
    session: &mut CheckSession<'_, '_>,
    term: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = exp_rule(arena, term);
    let phase = "infer";
    match arena.get(term) {
        Node::ExistsIntro { element, set } => {
            add_check!(session, rule, phase, element, set, "check element")?;
            if !matches!(
                add_sort!(session, rule, phase, set, "infer set sort")?,
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
                session,
                rule,
                phase,
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
            let ty = add_infer!(session, rule, phase, element, "infer element type")?;
            if !matches!(
                add_sort!(session, rule, phase, ty, "infer type sort")?,
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
                add_sort!(session, rule, phase, ty, "infer type sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            add_check!(session, rule, phase, left, ty, "check left")?;
            add_check!(session, rule, phase, right, ty, "check right")?;
            session.push(var.clone(), ty);
            let prop = arena.sort(Sort::Prop);
            let result = add_check!(session, rule, phase, predicate, prop, "check predicate");
            session.pop();
            result?;
            let apply = arena.alloc(Node::Lam {
                var,
                ty,
                body: predicate,
            });
            let base_prop = arena.alloc(Node::App {
                func: apply,
                arg: left,
            });
            add_check!(session, rule, phase, base, base_prop, "check base")?;
            let equality_prop = arena.alloc(Node::Equal { left, right });
            add_check!(
                session,
                rule,
                phase,
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
            add_check!(session, rule, phase, take, codomain, "check take")?;
            add_check!(session, rule, phase, element, domain, "check element")?;
            let mapped = arena.alloc(Node::App { func, arg: element });
            Ok(arena.alloc(Node::Equal {
                left: take,
                right: mapped,
            }))
        }
        _ => unreachable!(),
    }
}

fn check_wellformed_context(session: &mut CheckSession<'_, '_>) -> Result<(), Box<JudgementError>> {
    let original = std::mem::take(session.context);
    let result = check_context_entries(session, &original);
    session.context.clear();
    *session.context = original;
    result
}

fn check_context_entries(
    session: &mut CheckSession<'_, '_>,
    entries: &Context,
) -> Result<(), Box<JudgementError>> {
    for (var, ty) in entries {
        if session
            .context
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
        session.infer_sort(*ty)?;
        session.push(var.clone(), *ty);
    }
    Ok(())
}
