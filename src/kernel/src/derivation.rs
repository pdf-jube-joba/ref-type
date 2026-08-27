use crate::calculus::*;
use crate::environment::{CrateEnv, DefinitionKind, ModuleParameterKind};
use crate::exp::*;
use crate::ids::{InductiveId, ModuleId, SymbolId};
use crate::inductive::eliminator_type;
use crate::sort::Sort;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProgramTypeClass {
    Value,
    Computation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum Judgement {
    Pts { ty: Exp },
    ValueType,
    ComputationType,
    Value { ty: Exp },
    Computation { ty: Exp },
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

    pub fn push(&mut self, var: SymbolId, ty: Exp) {
        self.push_pts(var, ty);
    }

    pub fn push_pts(&mut self, var: SymbolId, ty: Exp) {
        self.context.push(ContextEntry::Pts { var, ty });
    }

    pub fn push_program_type(&mut self, var: SymbolId) {
        self.context.push(ContextEntry::ProgramType { var });
    }

    pub fn push_program_value(&mut self, var: SymbolId, ty: Exp) {
        self.context.push(ContextEntry::ProgramValue { var, ty });
    }

    pub fn pop(&mut self) {
        self.context
            .pop()
            .expect("CheckSession context stack underflow");
    }

    pub fn check(&mut self, term: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
        check(self, term, ty)
    }

    pub fn check_pts(&mut self, term: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
        check(self, term, ty)
    }

    pub fn infer(&mut self, term: Exp) -> Result<Exp, Box<JudgementError>> {
        infer(self, term)
    }

    pub fn infer_pts(&mut self, term: Exp) -> Result<Exp, Box<JudgementError>> {
        infer(self, term)
    }

    pub fn infer_sort(&mut self, term: Exp) -> Result<Sort, Box<JudgementError>> {
        infer_sort(self, term)
    }

    pub fn check_wellformed_context(&mut self) -> Result<(), Box<JudgementError>> {
        check_wellformed_context(self)
    }

    pub fn check_value_type(&mut self, ty: Exp) -> Result<(), Box<JudgementError>> {
        check_value_type(self, ty)
    }

    pub fn check_computation_type(&mut self, ty: Exp) -> Result<(), Box<JudgementError>> {
        check_computation_type(self, ty)
    }

    pub fn infer_value(&mut self, value: Exp) -> Result<Exp, Box<JudgementError>> {
        infer_value(self, value)
    }

    pub fn check_value(&mut self, value: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
        check_value(self, value, ty)
    }

    pub fn infer_computation(&mut self, computation: Exp) -> Result<Exp, Box<JudgementError>> {
        infer_computation(self, computation)
    }

    pub fn check_computation(
        &mut self,
        computation: Exp,
        ty: Exp,
    ) -> Result<(), Box<JudgementError>> {
        check_computation(self, computation, ty)
    }

    pub fn infer_any(&mut self, exp: Exp) -> Result<Judgement, Box<JudgementError>> {
        if let Ok(ty) = self.infer_pts(exp) {
            return Ok(Judgement::Pts { ty });
        }
        if self.check_value_type(exp).is_ok() {
            return Ok(Judgement::ValueType);
        }
        if self.check_computation_type(exp).is_ok() {
            return Ok(Judgement::ComputationType);
        }
        if let Ok(ty) = self.infer_value(exp) {
            return Ok(Judgement::Value { ty });
        }
        self.infer_computation(exp)
            .map(|ty| Judgement::Computation { ty })
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
                debug!(
                    target: "ref_type::typing",
                    premise = $expected,
                    result = %crate::printing::format_exp($session.env(), *ty),
                );
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
        term = %crate::printing::format_exp(session.env(), term),
        expected = %crate::printing::format_exp(session.env(), ty),
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
        term = %crate::printing::format_exp(session.env(), term),
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
            .and_then(|entry| match entry {
                ContextEntry::Pts { ty, .. } => Some(shift_bound_indices(arena, *ty, index + 1, 0)),
                ContextEntry::ProgramType { .. } | ContextEntry::ProgramValue { .. } => None,
            })
            .ok_or_else(|| failure(rule, phase, "bound variable index is outside the context")),
        Node::ModuleParam(parameter) => session
            .env()
            .module_parameter_opt(parameter)
            .and_then(|parameter| match parameter.kind {
                ModuleParameterKind::Pts { ty } => Some(ty),
                ModuleParameterKind::ProgramType | ModuleParameterKind::ProgramValue { .. } => None,
            })
            .ok_or_else(|| failure(rule, phase, "module parameter is not a PTS term")),
        Node::Meta { .. } => Err(failure(
            rule,
            phase,
            "unresolved metavariable reached the strict kernel checker",
        )),
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
            session.push(var, ty);
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
            let Some((_var, arg_ty, ret_ty)) = expose_product(session.env(), func_ty) else {
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
            Ok(instantiate(arena, ret_ty, arg))
        }
        Node::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::Pts {
                Ok(definition.ty)
            } else {
                Err(failure(rule, phase, "definition is not a PTS term"))
            }
        }
        Node::IndType {
            indspec,
            parameters,
        } => {
            let env = session.env();
            let spec = env.inductive(indspec);
            check_parameters(session, rule, phase, &parameters, spec.parameters())?;
            Ok(instantiate_telescope(arena, spec.arity(arena), &parameters))
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
            let constructor = crate::inductive::InductiveTypeSpecs::type_of_constructor(
                arena, indspec, spec, idx, parameters,
            );
            Ok(constructor)
        }
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => infer_ind_elim(session, rule, phase, indspec, elim, return_type, cases),
        Node::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            let reflected_state_ty = reflected_type(arena, state_ty);
            add_check!(
                session,
                rule,
                phase,
                state,
                reflected_state_ty,
                "check reflected state"
            )?;
            Ok(arena.sort(Sort::Prop))
        }
        Node::RfType { compute_ty } => {
            check_program_type(session, compute_ty)?;
            Ok(arena.sort(Sort::Set(0)))
        }
        Node::RfTerm { compute_ty, term } => {
            match check_program_type(session, compute_ty)? {
                ProgramTypeClass::Value => check_value(session, term, compute_ty)?,
                ProgramTypeClass::Computation => check_computation(session, term, compute_ty)?,
            }
            Ok(reflected_type(arena, compute_ty))
        }
        Node::ThunkType { .. }
        | Node::ReturnType { .. }
        | Node::ComputationFunction { .. }
        | Node::RunStep { .. }
        | Node::ProgramIndType { .. }
        | Node::Thunk { .. }
        | Node::Continue { .. }
        | Node::Finish { .. }
        | Node::ProgramIndCtor { .. }
        | Node::Return { .. }
        | Node::Force { .. }
        | Node::ComputationLam { .. }
        | Node::ComputationApp { .. }
        | Node::Sequence { .. }
        | Node::ValueLet { .. }
        | Node::ProgramCase { .. }
        | Node::Run { .. }
        | Node::RunCase { .. } => Err(failure(
            rule,
            phase,
            "Program expression used in the PTS judgement",
        )),
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
        | Node::TakeEq { .. }
        | Node::AccIntro { .. }
        | Node::AccDescent { .. } => infer_proof_constructor(session, term),
    }
}

fn context_entry<'a>(
    session: &'a CheckSession<'_, '_>,
    index: usize,
) -> Result<&'a ContextEntry, Box<JudgementError>> {
    session
        .context
        .len()
        .checked_sub(index + 1)
        .and_then(|position| session.context.get(position))
        .ok_or_else(|| {
            failure(
                "Variable",
                "lookup",
                "bound variable index is outside the context",
            )
        })
}

fn check_program_type(
    session: &mut CheckSession<'_, '_>,
    ty: Exp,
) -> Result<ProgramTypeClass, Box<JudgementError>> {
    if check_value_type(session, ty).is_ok() {
        Ok(ProgramTypeClass::Value)
    } else {
        check_computation_type(session, ty).map(|()| ProgramTypeClass::Computation)
    }
}

fn check_value_type(
    session: &mut CheckSession<'_, '_>,
    ty: Exp,
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    let rule = "ValueType";
    let phase = "formation";
    match arena.get(ty) {
        Node::Bound(index) => match context_entry(session, index)? {
            ContextEntry::ProgramType { .. } => Ok(()),
            _ => Err(failure(
                rule,
                phase,
                "bound variable is not a Program type variable",
            )),
        },
        Node::ModuleParam(parameter) => match &session
            .env()
            .module_parameter_opt(parameter)
            .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
            .kind
        {
            ModuleParameterKind::ProgramType => Ok(()),
            _ => Err(failure(
                rule,
                phase,
                "module parameter is not a Program type variable",
            )),
        },
        Node::ThunkType { computation_ty } => check_computation_type(session, computation_ty),
        Node::RunStep {
            state_ty,
            result_ty,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)
        }
        Node::ProgramIndType {
            indspec,
            parameters,
        } => {
            let spec = session.env().program_inductive(indspec);
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program datatype parameter count mismatch",
                ));
            }
            for parameter in parameters {
                check_value_type(session, parameter)?;
            }
            Ok(())
        }
        _ => Err(failure(rule, phase, "expression is not a value type")),
    }
}

fn check_computation_type(
    session: &mut CheckSession<'_, '_>,
    ty: Exp,
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    let rule = "ComputationType";
    let phase = "formation";
    match arena.get(ty) {
        Node::ReturnType { value_ty } => check_value_type(session, value_ty),
        Node::ComputationFunction { domain, codomain } => {
            check_value_type(session, domain)?;
            check_computation_type(session, codomain)
        }
        _ => Err(failure(rule, phase, "expression is not a computation type")),
    }
}

fn check_value(
    session: &mut CheckSession<'_, '_>,
    value: Exp,
    expected: Exp,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, expected)?;
    let inferred = infer_value(session, value)?;
    if exp_is_alpha_eq(session.env(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Value", "check", "value type mismatch"))
    }
}

fn infer_value(session: &mut CheckSession<'_, '_>, value: Exp) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Value";
    let phase = "infer";
    match arena.get(value) {
        Node::Bound(index) => match context_entry(session, index)? {
            ContextEntry::ProgramValue { ty, .. } => {
                Ok(shift_bound_indices(arena, *ty, index + 1, 0))
            }
            _ => Err(failure(
                rule,
                phase,
                "bound variable is not a Program value",
            )),
        },
        Node::ModuleParam(parameter) => {
            match &session
                .env()
                .module_parameter_opt(parameter)
                .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
                .kind
            {
                ModuleParameterKind::ProgramValue { ty } => Ok(*ty),
                _ => Err(failure(
                    rule,
                    phase,
                    "module parameter is not a Program value",
                )),
            }
        }
        Node::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::ProgramValue {
                Ok(definition.ty)
            } else {
                Err(failure(rule, phase, "definition is not a Program value"))
            }
        }
        Node::Thunk { computation } => {
            let computation_ty = infer_computation(session, computation)?;
            Ok(arena.alloc(Node::ThunkType { computation_ty }))
        }
        Node::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, next, state_ty)?;
            Ok(run_step_type(arena, state_ty, result_ty))
        }
        Node::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, output, result_ty)?;
            Ok(run_step_type(arena, state_ty, result_ty))
        }
        Node::ProgramIndCtor {
            indspec,
            parameters,
            idx,
            fields,
        } => {
            let spec = session.env().program_inductive(indspec);
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program constructor parameter count mismatch",
                ));
            }
            for parameter in &parameters {
                check_value_type(session, *parameter)?;
            }
            let constructor = spec
                .constructors()
                .get(idx)
                .ok_or_else(|| failure(rule, phase, "Program constructor index out of bounds"))?;
            let expected_fields = constructor.instantiated_fields(arena, &parameters);
            if fields.len() != expected_fields.len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program constructor field count mismatch",
                ));
            }
            let mut preceding = Vec::new();
            for (field, (_, expected)) in fields.into_iter().zip(expected_fields) {
                let expected = instantiate_telescope(arena, expected, &preceding);
                check_value(session, field, expected)?;
                preceding.push(field);
            }
            Ok(arena.alloc(Node::ProgramIndType {
                indspec,
                parameters,
            }))
        }
        _ => Err(failure(rule, phase, "expression is not a Program value")),
    }
}

fn check_computation(
    session: &mut CheckSession<'_, '_>,
    computation: Exp,
    expected: Exp,
) -> Result<(), Box<JudgementError>> {
    check_computation_type(session, expected)?;
    let inferred = infer_computation(session, computation)?;
    if exp_is_alpha_eq(session.env(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Computation", "check", "computation type mismatch"))
    }
}

fn infer_computation(
    session: &mut CheckSession<'_, '_>,
    computation: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Computation";
    let phase = "infer";
    match arena.get(computation) {
        Node::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::ProgramComputation {
                Ok(definition.ty)
            } else {
                Err(failure(
                    rule,
                    phase,
                    "definition is not a Program computation",
                ))
            }
        }
        Node::Return { value } => {
            let value_ty = infer_value(session, value)?;
            Ok(arena.alloc(Node::ReturnType { value_ty }))
        }
        Node::Force { value } => {
            let value_ty = infer_value(session, value)?;
            let Node::ThunkType { computation_ty } = arena.get(value_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "forced value does not have a thunk type",
                ));
            };
            Ok(computation_ty)
        }
        Node::ComputationLam {
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            Ok(arena.alloc(Node::ComputationFunction {
                domain: value_ty,
                codomain: body_ty?,
            }))
        }
        Node::ComputationApp { computation, value } => {
            let computation_ty = infer_computation(session, computation)?;
            let Node::ComputationFunction { domain, codomain } = arena.get(computation_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "application head is not a computation function",
                ));
            };
            check_value(session, value, domain)?;
            Ok(codomain)
        }
        Node::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            let expected_source = arena.alloc(Node::ReturnType { value_ty });
            check_computation(session, computation, expected_source)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            body_ty
        }
        Node::ValueLet { var, value, body } => {
            let value_ty = infer_value(session, value)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            body_ty
        }
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            termination,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            let reflected_initial = arena.alloc(Node::RfTerm {
                compute_ty: state_ty,
                term: initial,
            });
            let terminates =
                accessibility_type(arena, state_ty, result_ty, step, reflected_initial);
            session.check_pts(termination, terminates)?;
            Ok(arena.alloc(Node::ReturnType {
                value_ty: result_ty,
            }))
        }
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            termination,
            invariant,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            let transition_ty = arena.alloc(Node::ReturnType {
                value_ty: run_step_type(arena, state_ty, result_ty),
            });
            check_computation(session, transition, transition_ty)?;
            let reflected_initial = arena.alloc(Node::RfTerm {
                compute_ty: state_ty,
                term: initial,
            });
            let terminates =
                accessibility_type(arena, state_ty, result_ty, step, reflected_initial);
            session.check_pts(termination, terminates)?;
            let expected_invariant =
                run_invariant(arena, state_ty, result_ty, step, initial, transition);
            session.check_pts(invariant, expected_invariant)?;
            Ok(arena.alloc(Node::ReturnType {
                value_ty: result_ty,
            }))
        }
        Node::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let scrutinee_ty = infer_value(session, scrutinee)?;
            let Node::ProgramIndType {
                indspec: inferred_spec,
                parameters,
            } = arena.get(scrutinee_ty)
            else {
                return Err(failure(
                    rule,
                    phase,
                    "case scrutinee is not a Program datatype",
                ));
            };
            if inferred_spec != indspec {
                return Err(failure(rule, phase, "case datatype annotation mismatch"));
            }
            let spec = session.env().program_inductive(indspec);
            if branches.len() != spec.constructors().len() {
                return Err(failure(
                    rule,
                    phase,
                    "case must contain exactly one branch per constructor",
                ));
            }
            let mut result_ty = None;
            for (branch, constructor) in branches.into_iter().zip(spec.constructors()) {
                let fields = constructor.instantiated_fields(arena, &parameters);
                if branch.binders.len() != fields.len() {
                    return Err(failure(rule, phase, "case branch binder count mismatch"));
                }
                for (binder, (_, field_ty)) in branch.binders.iter().copied().zip(fields) {
                    session.push_program_value(binder, field_ty);
                }
                let branch_ty = infer_computation(session, branch.body);
                for _ in &branch.binders {
                    session.pop();
                }
                let branch_ty =
                    remove_unused_ambient_binders(arena, branch_ty?, branch.binders.len())
                        .ok_or_else(|| {
                            failure(rule, phase, "case result type depends on branch values")
                        })?;
                check_computation_type(session, branch_ty)?;
                if let Some(expected) = result_ty {
                    if !exp_is_alpha_eq(session.env(), expected, branch_ty) {
                        return Err(failure(rule, phase, "case branch result type mismatch"));
                    }
                } else {
                    result_ty = Some(branch_ty);
                }
            }
            result_ty.ok_or_else(|| failure(rule, phase, "cannot infer an empty Program case"))
        }
        _ => Err(failure(
            rule,
            phase,
            "expression is not a Program computation",
        )),
    }
}

fn run_step_type(arena: &Arena, state_ty: Exp, result_ty: Exp) -> Exp {
    arena.alloc(Node::RunStep {
        state_ty,
        result_ty,
    })
}

fn reflected_type(arena: &Arena, compute_ty: Exp) -> Exp {
    arena.alloc(Node::RfType { compute_ty })
}

fn nondependent_product(arena: &Arena, domain: Exp, codomain: Exp) -> Exp {
    arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    })
}

fn step_function_type(arena: &Arena, state_ty: Exp, result_ty: Exp) -> Exp {
    let step_result = arena.alloc(Node::ReturnType {
        value_ty: run_step_type(arena, state_ty, result_ty),
    });
    let function = arena.alloc(Node::ComputationFunction {
        domain: state_ty,
        codomain: step_result,
    });
    arena.alloc(Node::ThunkType {
        computation_ty: function,
    })
}

fn accessibility_type(arena: &Arena, state_ty: Exp, result_ty: Exp, step: Exp, state: Exp) -> Exp {
    arena.alloc(Node::Acc {
        state_ty,
        result_ty,
        step,
        state,
    })
}

fn check_recursion_signature(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    state_ty: Exp,
    result_ty: Exp,
    step: Exp,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, state_ty)?;
    check_value_type(session, result_ty)?;
    let expected_step = step_function_type(session.arena(), state_ty, result_ty);
    check_value(session, step, expected_step)
        .map_err(|error| propagate(error, rule, phase, "check CBPV step function"))
}

fn check_parameters(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    parameters: &[Exp],
    expected: &[(SymbolId, Exp)],
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    if parameters.len() != expected.len() {
        return Err(failure(rule, phase, "mismatch parameter length"));
    }
    let mut preceding = Vec::new();
    for (parameter, (_, parameter_ty)) in parameters.iter().zip(expected) {
        let expected_ty = instantiate_telescope(arena, *parameter_ty, &preceding);
        add_check!(
            session,
            rule,
            phase,
            *parameter,
            expected_ty,
            "parameter type mismatch"
        )?;
        preceding.push(*parameter);
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
        let constructor_ty = spec.constructors()[index].instantiate_parameters(arena, &parameters);
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
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    });
    add_check!(session, rule, phase, map, map_ty, "check map type")?;
    let exists = arena.alloc(Node::Exists { set: domain });
    add_check!(session, rule, phase, existence, exists, "check existence")?;

    let x1 = SymbolId::ANONYMOUS;
    let x2 = SymbolId::ANONYMOUS;
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
        ty: shift_bound_indices(arena, domain, 1, 0),
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
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, proposition, 1, 0),
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
        Node::ModuleParam(_) => "ModuleParam",
        Node::Meta { .. } => "Meta",
        Node::Prod { .. } => "Prod",
        Node::Lam { .. } => "Lam",
        Node::App { .. } => "App",
        Node::DefinedConstant(_) => "DefinedConstant",
        Node::IndType { .. } => "IndType",
        Node::IndCtor { .. } => "IndCtor",
        Node::IndElim { .. } => "IndTypeElim",
        Node::ThunkType { .. } => "ThunkType",
        Node::ReturnType { .. } => "ReturnType",
        Node::ComputationFunction { .. } => "ComputationFunction",
        Node::RunStep { .. } => "RunStep",
        Node::ProgramIndType { .. } => "ProgramIndType",
        Node::Thunk { .. } => "Thunk",
        Node::Continue { .. } => "Continue",
        Node::Finish { .. } => "Finish",
        Node::ProgramIndCtor { .. } => "ProgramIndCtor",
        Node::Return { .. } => "Return",
        Node::Force { .. } => "Force",
        Node::ComputationLam { .. } => "ComputationLam",
        Node::ComputationApp { .. } => "ComputationApp",
        Node::Sequence { .. } => "Sequence",
        Node::ValueLet { .. } => "ValueLet",
        Node::ProgramCase { .. } => "ProgramCase",
        Node::Acc { .. } => "Acc",
        Node::RfType { .. } => "RfType",
        Node::RfTerm { .. } => "RfTerm",
        Node::Run { .. } => "Run",
        Node::RunCase { .. } => "RunCase",
        Node::AccIntro { .. } => "AccIntro",
        Node::AccDescent { .. } => "AccDescent",
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

fn continue_function(arena: &Arena, state_ty: Exp, result_ty: Exp) -> Exp {
    let body = arena.alloc(Node::Continue {
        state_ty: shift_bound_indices(arena, state_ty, 1, 0),
        result_ty: shift_bound_indices(arena, result_ty, 1, 0),
        next: arena.bound(0),
    });
    let returned = arena.alloc(Node::Return { value: body });
    let function = arena.alloc(Node::ComputationLam {
        var: SymbolId::ANONYMOUS,
        value_ty: state_ty,
        body: returned,
    });
    arena.alloc(Node::Thunk {
        computation: function,
    })
}

fn transition_equality(
    arena: &Arena,
    state_ty: Exp,
    result_ty: Exp,
    step: Exp,
    from: Exp,
    to: Exp,
) -> Exp {
    let step_ty = step_function_type(arena, state_ty, result_ty);
    let reflected_step = arena.alloc(Node::RfTerm {
        compute_ty: step_ty,
        term: step,
    });
    let continue_fun = continue_function(arena, state_ty, result_ty);
    let reflected_continue = arena.alloc(Node::RfTerm {
        compute_ty: step_ty,
        term: continue_fun,
    });
    let left = arena.alloc(Node::App {
        func: reflected_step,
        arg: from,
    });
    let right = arena.alloc(Node::App {
        func: reflected_continue,
        arg: to,
    });
    arena.alloc(Node::Equal { left, right })
}

fn run_invariant(
    arena: &Arena,
    state_ty: Exp,
    result_ty: Exp,
    step: Exp,
    initial: Exp,
    transition: Exp,
) -> Exp {
    let step_result = arena.alloc(Node::ReturnType {
        value_ty: run_step_type(arena, state_ty, result_ty),
    });
    let forced = arena.alloc(Node::Force { value: step });
    let applied = arena.alloc(Node::ComputationApp {
        computation: forced,
        value: initial,
    });
    let left = arena.alloc(Node::RfTerm {
        compute_ty: step_result,
        term: applied,
    });
    let right = arena.alloc(Node::RfTerm {
        compute_ty: step_result,
        term: transition,
    });
    arena.alloc(Node::Equal { left, right })
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
            session.push(var, ty);
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
        Node::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            let reflected_state_ty = reflected_type(arena, state_ty);
            add_check!(
                session,
                rule,
                phase,
                state,
                reflected_state_ty,
                "check accessible state"
            )?;

            // Build the premise under b : RfType(A). All outer expressions
            // move out by one de Bruijn level; b itself is Bound(0).
            let nested_state_ty = shift_bound_indices(arena, state_ty, 1, 0);
            let nested_result_ty = shift_bound_indices(arena, result_ty, 1, 0);
            let nested_step = shift_bound_indices(arena, step, 1, 0);
            let nested_state = shift_bound_indices(arena, state, 1, 0);
            let predecessor = arena.bound(0);
            let transition = transition_equality(
                arena,
                nested_state_ty,
                nested_result_ty,
                nested_step,
                nested_state,
                predecessor,
            );
            let predecessor_acc = accessibility_type(
                arena,
                nested_state_ty,
                nested_result_ty,
                nested_step,
                predecessor,
            );
            let implication = nondependent_product(arena, transition, predecessor_acc);
            let expected_predecessors = arena.alloc(Node::Prod {
                var: SymbolId::ANONYMOUS,
                ty: reflected_state_ty,
                body: implication,
            });
            add_check!(
                session,
                rule,
                phase,
                predecessors,
                expected_predecessors,
                "check accessibility predecessors"
            )?;
            Ok(accessibility_type(arena, state_ty, result_ty, step, state))
        }
        Node::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            let reflected_state_ty = reflected_type(arena, state_ty);
            add_check!(
                session,
                rule,
                phase,
                from,
                reflected_state_ty,
                "check source state"
            )?;
            add_check!(
                session,
                rule,
                phase,
                to,
                reflected_state_ty,
                "check target state"
            )?;
            let source_acc = accessibility_type(arena, state_ty, result_ty, step, from);
            add_check!(
                session,
                rule,
                phase,
                accessibility,
                source_acc,
                "check source accessibility"
            )?;
            let expected_transition =
                transition_equality(arena, state_ty, result_ty, step, from, to);
            add_check!(
                session,
                rule,
                phase,
                transition,
                expected_transition,
                "check recursive transition"
            )?;
            Ok(accessibility_type(arena, state_ty, result_ty, step, to))
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
    for entry in entries {
        match *entry {
            ContextEntry::Pts { var, ty } => {
                session.infer_sort(ty)?;
                session.push_pts(var, ty);
            }
            ContextEntry::ProgramType { var } => session.push_program_type(var),
            ContextEntry::ProgramValue { var, ty } => {
                session.check_value_type(ty)?;
                session.push_program_value(var, ty);
            }
        }
    }
    Ok(())
}
