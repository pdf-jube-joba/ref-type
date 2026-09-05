use crate::calculus::*;
use crate::environment::{CrateEnv, DefinitionKind, ModuleParameterKind};
use crate::exp::*;
use crate::ids::{InductiveId, ModuleId, SymbolId};
use crate::inductive::{CtorBinder, eliminator_type};
use crate::reflection::{reflect_context, reflect_term, reflect_type};
use crate::sort::Sort;
use crate::utils;
use serde::Serialize;
use std::cell::RefCell;
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
    proof_mode: ProofMode<'context>,
}

#[derive(Clone, Copy)]
enum ProofMode<'a> {
    Strict,
    Collect(&'a RefCell<Vec<ProofObligation>>),
    Provided(&'a [ProofEvidence]),
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
            proof_mode: ProofMode::Strict,
        }
    }

    /// Construct a checker which records judgement-level provability
    /// premises instead of silently accepting them.
    pub fn collecting(
        env: &'env CrateEnv,
        current_module: ModuleId,
        context: &'context mut Context,
        obligations: &'context RefCell<Vec<ProofObligation>>,
    ) -> Self {
        Self {
            env,
            current_module,
            context,
            proof_mode: ProofMode::Collect(obligations),
        }
    }

    /// Construct a strict checker with explicit witnesses for every
    /// judgement-level provability premise.
    pub fn with_evidence(
        env: &'env CrateEnv,
        current_module: ModuleId,
        context: &'context mut Context,
        evidence: &'context [ProofEvidence],
    ) -> Self {
        Self {
            env,
            current_module,
            context,
            proof_mode: ProofMode::Provided(evidence),
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

    /// Check both Program typing and the reflected PTS typing judgement for a
    /// value under the current Program context.
    pub fn check_well_terminated_value(
        &mut self,
        value: Exp,
        ty: Exp,
    ) -> Result<(), Box<JudgementError>> {
        check_value(self, value, ty)?;
        check_reflected_program_typing(self, value, ty)
    }

    /// Check both Program typing and the reflected PTS typing judgement for a
    /// computation under the current Program context.
    pub fn check_well_terminated_computation(
        &mut self,
        computation: Exp,
        ty: Exp,
    ) -> Result<(), Box<JudgementError>> {
        check_computation(self, computation, ty)?;
        check_reflected_program_typing(self, computation, ty)
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

    fn require_provable(
        &mut self,
        proposition: Exp,
        rule: &'static str,
    ) -> Result<(), Box<JudgementError>> {
        // Weakening of a proof already present in the PTS context is the only
        // automatic proof search performed by the kernel.
        if self.context.iter().any(|entry| match entry {
            ContextEntry::Pts { ty, .. } => convertible(self.env, *ty, proposition),
            ContextEntry::ProgramType { .. } | ContextEntry::ProgramValue { .. } => false,
        }) {
            return Ok(());
        }

        match self.proof_mode {
            ProofMode::Strict => Err(failure(
                rule,
                "provability",
                "provability premise has no explicit evidence",
            )),
            ProofMode::Collect(obligations) => {
                let context = self.context.clone();
                let duplicate = obligations.borrow().iter().any(|obligation| {
                    contexts_alpha_eq(self.env, &obligation.context, &context)
                        && convertible(self.env, obligation.proposition, proposition)
                });
                if !duplicate {
                    obligations.borrow_mut().push(ProofObligation {
                        context,
                        proposition,
                        rule,
                    });
                }
                Ok(())
            }
            ProofMode::Provided(evidence) => {
                let Some(candidate) = evidence.iter().find(|candidate| {
                    contexts_alpha_eq(self.env, &candidate.context, self.context)
                        && convertible(self.env, candidate.proposition, proposition)
                }) else {
                    return Err(failure(
                        rule,
                        "provability",
                        "no proof-block entry matches this context and proposition",
                    ));
                };
                let mut context = candidate.context.clone();
                CheckSession::new(self.env, self.current_module, &mut context)
                    .check_pts(candidate.witness, proposition)
                    .map_err(|error| {
                        Box::new(error.with_frame(
                            rule,
                            "provability evidence",
                            "proof witness checks against the required proposition",
                        ))
                    })
            }
        }
    }
}

fn contexts_alpha_eq(env: &CrateEnv, left: &Context, right: &Context) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (ContextEntry::Pts { ty: left, .. }, ContextEntry::Pts { ty: right, .. })
                | (
                    ContextEntry::ProgramValue { ty: left, .. },
                    ContextEntry::ProgramValue { ty: right, .. },
                ) => exp_is_alpha_eq(env, *left, *right),
                (ContextEntry::ProgramType { .. }, ContextEntry::ProgramType { .. }) => true,
                _ => false,
            })
}

/// Whether supplied evidence addresses a particular judgement-level proof
/// obligation.  The witness itself is checked separately by
/// [`CheckSession::with_evidence`].
pub fn evidence_matches_obligation(
    env: &CrateEnv,
    evidence: &ProofEvidence,
    obligation: &ProofObligation,
) -> bool {
    contexts_alpha_eq(env, &evidence.context, &obligation.context)
        && convertible(env, evidence.proposition, obligation.proposition)
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
        Node::ValueType => Err(failure(
            rule,
            phase,
            "Program type universe used in the PTS judgement",
        )),
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
                ModuleParameterKind::Pts { ty }
                    if session.context.iter().any(
                        |entry| matches!(entry, ContextEntry::Pts { var, .. } if *var == parameter.name),
                    ) =>
                {
                    Some(ty)
                }
                ModuleParameterKind::ProgramType | ModuleParameterKind::ProgramValue { .. } => None,
                ModuleParameterKind::Pts { .. } => None,
            })
            .ok_or_else(|| failure(rule, phase, "module parameter is not a PTS term")),
        Node::ReflectedProgramParam(parameter) => session
            .env()
            .module_parameter_opt(parameter)
            .and_then(|parameter| {
                let visible = session.context.iter().any(
                    |entry| matches!(entry, ContextEntry::Pts { var, .. } if *var == parameter.name),
                );
                if !visible {
                    return None;
                }
                match parameter.kind {
                    ModuleParameterKind::ProgramType => Some(arena.sort(Sort::Set(0))),
                    ModuleParameterKind::ProgramValue { ty } => reflect_type(session.env(), ty).ok(),
                    ModuleParameterKind::Pts { .. } => None,
                }
            })
            .ok_or_else(|| {
                failure(
                    rule,
                    phase,
                    "reflected Program parameter is not present in the reflected context",
                )
            }),
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
        Node::IndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let spec = session.env().inductive(indspec);
            if spec.constructor_len() != 1 {
                return Err(failure(rule, phase, "projection target is not a structure"));
            }
            check_parameters(session, rule, phase, &parameters, spec.parameters())?;
            let structure_ty = arena.alloc(Node::IndType {
                indspec,
                parameters: parameters.clone(),
            });
            add_check!(
                session,
                rule,
                phase,
                value,
                structure_ty,
                "check projected structure"
            )?;
            let constructor = spec.constructors()[0].instantiate_parameters(arena, &parameters);
            let Some(CtorBinder::Simple((_, field_ty))) = constructor.telescope.get(field) else {
                return Err(failure(rule, phase, "structure field index out of bounds"));
            };
            let preceding = (0..field)
                .map(|field| {
                    arena.alloc(Node::IndProjection {
                        indspec,
                        parameters: parameters.clone(),
                        value,
                        field,
                    })
                })
                .collect::<Vec<_>>();
            Ok(instantiate_telescope(arena, *field_ty, &preceding))
        }
        Node::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => infer_reflected_program_case(session, rule, phase, indspec, scrutinee, branches),
        Node::RunStep {
            state_ty,
            result_ty,
        } => {
            let state_sort = add_sort!(session, rule, phase, state_ty, "check state Set")?;
            let result_sort = add_sort!(session, rule, phase, result_ty, "check result Set")?;
            match (state_sort, result_sort) {
                (Sort::Set(i), Sort::Set(j)) => Ok(arena.sort(Sort::Set(i.max(j)))),
                _ => Err(failure(rule, phase, "RunStep arguments must inhabit Set(i)")),
            }
        }
        Node::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
            add_check!(session, rule, phase, next, state_ty, "check next state")?;
            Ok(arena.alloc(Node::RunStep {
                state_ty,
                result_ty,
            }))
        }
        Node::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
            add_check!(session, rule, phase, output, result_ty, "check final result")?;
            Ok(arena.alloc(Node::RunStep {
                state_ty,
                result_ty,
            }))
        }
        Node::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => {
            check_set_recursion_signature(
                session,
                rule,
                phase,
                state_ty,
                result_ty,
                Some(step),
            )?;
            add_check!(
                session,
                rule,
                phase,
                state,
                state_ty,
                "check accessible state"
            )?;
            Ok(arena.sort(Sort::Prop))
        }
        Node::Proof { proposition } => {
            if add_sort!(session, rule, phase, proposition, "check proposition")? != Sort::Prop {
                return Err(failure(rule, phase, "Proof argument is not a proposition"));
            }
            session.require_provable(proposition, "Proof")?;
            Ok(proposition)
        }
        Node::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            check_set_recursion_signature(
                session,
                rule,
                phase,
                state_ty,
                result_ty,
                Some(step),
            )?;
            add_check!(session, rule, phase, initial, state_ty, "check initial state")?;
            let accessibility = arena.alloc(Node::Acc {
                state_ty,
                result_ty,
                step,
                state: initial,
            });
            session.require_provable(accessibility, "SetRun")?;
            Ok(result_ty)
        }
        Node::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            check_set_recursion_signature(
                session,
                rule,
                phase,
                state_ty,
                result_ty,
                Some(step),
            )?;
            add_check!(session, rule, phase, initial, state_ty, "check current state")?;
            let run_step = arena.alloc(Node::RunStep {
                state_ty,
                result_ty,
            });
            add_check!(session, rule, phase, transition, run_step, "check transition")?;
            session.require_provable(
                arena.alloc(Node::Acc {
                    state_ty,
                    result_ty,
                    step,
                    state: initial,
                }),
                "SetRunCase",
            )?;
            session.require_provable(
                arena.alloc(Node::Equal {
                    left: arena.alloc(Node::App {
                        func: step,
                        arg: initial,
                    }),
                    right: transition,
                }),
                "SetRunCase",
            )?;
            Ok(result_ty)
        }
        Node::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => infer_run_step_recursor(
            session,
            rule,
            phase,
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        ),
        Node::BoxType { program_ty } => {
            check_closed_program_type(session, program_ty)?;
            Ok(arena.sort(Sort::Set(0)))
        }
        Node::BoxProgram {
            program_ty,
            program,
        } => {
            check_closed_well_terminated_program(session, program_ty, program)?;
            Ok(arena.alloc(Node::BoxType { program_ty }))
        }
        Node::ForceBox { program_ty, boxed } => {
            check_closed_program_type(session, program_ty)?;
            add_check!(
                session,
                rule,
                phase,
                boxed,
                arena.alloc(Node::BoxType { program_ty }),
                "check boxed Program"
            )?;
            reflect_type(session.env(), program_ty)
                .map_err(|error| failure(rule, phase, &format!("cannot reflect type: {error}")))
        }
        Node::BoxApp { function, argument } => {
            let function_ty = add_infer!(session, rule, phase, function, "infer boxed function")?;
            let Node::BoxType { program_ty } = arena.get(type_head_normal(session.env(), function_ty)) else {
                return Err(failure(rule, phase, "boxed application head is not Box(P)"));
            };
            let Node::ComputationFunction { domain, codomain } = arena.get(program_ty) else {
                return Err(failure(rule, phase, "boxed application head is not a computation function"));
            };
            add_check!(
                session,
                rule,
                phase,
                argument,
                arena.alloc(Node::BoxType { program_ty: domain }),
                "check boxed argument"
            )?;
            Ok(arena.alloc(Node::BoxType { program_ty: codomain }))
        }
        Node::RfType { compute_ty } => {
            Err(failure(
                rule,
                phase,
                &format!(
                    "RfType is no longer a term; meta-level reflection of {} is required",
                    crate::printing::format_exp(session.env(), compute_ty)
                ),
            ))
        }
        Node::RfTerm { .. } => Err(failure(
            rule,
            phase,
            "RfTerm is no longer a term; reflection is a meta-level map",
        )),
        Node::ThunkType { .. }
        | Node::ReturnType { .. }
        | Node::ComputationFunction { .. }
        | Node::ProgramIndType { .. }
        | Node::Thunk { .. }
        | Node::ProgramIndCtor { .. }
        | Node::ProgramIndProjection { .. }
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
        | Node::AxiomSetExt { .. }
        | Node::AxiomFunExt { .. }
        | Node::AxiomClassicalIndefiniteChoice { .. }
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
        Node::ModuleParam(parameter) => match session
            .env()
            .module_parameter_opt(parameter)
            .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
        {
            parameter
                if matches!(parameter.kind, ModuleParameterKind::ProgramType)
                    && session.context.iter().any(
                        |entry| matches!(entry, ContextEntry::ProgramType { var } if *var == parameter.name),
                    ) => Ok(()),
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
        Node::Prod { var, ty, body } => {
            if matches!(arena.get(ty), Node::ValueType) {
                session.push_program_type(var);
            } else {
                check_value_type(session, ty)?;
                session.push_program_value(var, ty);
            }
            let result = check_value_type(session, body);
            session.pop();
            result
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
            match session
                .env()
                .module_parameter_opt(parameter)
                .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
            {
                parameter
                    if matches!(parameter.kind, ModuleParameterKind::ProgramValue { .. })
                        && session.context.iter().any(
                            |entry| matches!(entry, ContextEntry::ProgramValue { var, .. } if *var == parameter.name),
                        ) => match parameter.kind {
                            ModuleParameterKind::ProgramValue { ty } => Ok(ty),
                            _ => unreachable!(),
                        },
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
        Node::Lam { var, ty, body } => {
            if matches!(arena.get(ty), Node::ValueType) {
                session.push_program_type(var);
            } else {
                check_value_type(session, ty)?;
                session.push_program_value(var, ty);
            }
            let body_ty = infer_value(session, body);
            session.pop();
            let body_ty = body_ty?;
            Ok(arena.alloc(Node::Prod {
                var,
                ty,
                body: body_ty,
            }))
        }
        Node::App { func, arg } => {
            let func_ty = infer_value(session, func)?;
            let Some((_var, domain, codomain)) = expose_product(session.env(), func_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "Program value application head is not a function",
                ));
            };
            if matches!(arena.get(domain), Node::ValueType) {
                check_value_type(session, arg)?;
            } else {
                check_value(session, arg, domain)?;
            }
            Ok(instantiate(arena, codomain, arg))
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
        Node::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let spec = session.env().program_inductive(indspec);
            if spec.constructors().len() != 1 {
                return Err(failure(
                    rule,
                    phase,
                    "Program projection requires a one-constructor structure",
                ));
            }
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program projection parameter count mismatch",
                ));
            }
            for parameter in &parameters {
                check_value_type(session, *parameter)?;
            }
            let structure_ty = arena.alloc(Node::ProgramIndType {
                indspec,
                parameters: parameters.clone(),
            });
            check_value(session, value, structure_ty)?;
            let fields = spec.constructors()[0].instantiated_fields(arena, &parameters);
            let (_, field_ty) = fields
                .get(field)
                .copied()
                .ok_or_else(|| failure(rule, phase, "Program projection field out of bounds"))?;
            let preceding = (0..field)
                .map(|preceding_field| {
                    arena.alloc(Node::ProgramIndProjection {
                        indspec,
                        parameters: parameters.clone(),
                        value,
                        field: preceding_field,
                    })
                })
                .collect::<Vec<_>>();
            Ok(instantiate_telescope(arena, field_ty, &preceding))
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
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
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
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            let transition_ty = arena.alloc(Node::ReturnType {
                value_ty: run_step_type(arena, state_ty, result_ty),
            });
            check_computation(session, transition, transition_ty)?;
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

fn check_set_recursion_signature(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    state_ty: Exp,
    result_ty: Exp,
    step: Option<Exp>,
) -> Result<(), Box<JudgementError>> {
    let state_sort = session.infer_sort(state_ty)?;
    let result_sort = session.infer_sort(result_ty)?;
    if !matches!(state_sort, Sort::Set(_)) || !matches!(result_sort, Sort::Set(_)) {
        return Err(failure(
            rule,
            phase,
            "Set RunStep state and result types must inhabit Set(i)",
        ));
    }
    if let Some(step) = step {
        let run_step = session.arena().alloc(Node::RunStep {
            state_ty,
            result_ty,
        });
        let expected = nondependent_product(session.arena(), state_ty, run_step);
        session
            .check_pts(step, expected)
            .map_err(|error| propagate(error, rule, phase, "check Set step function"))?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn infer_run_step_recursor(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    state_ty: Exp,
    result_ty: Exp,
    motive: Exp,
    on_continue: Exp,
    on_finish: Exp,
    scrutinee: Exp,
) -> Result<Exp, Box<JudgementError>> {
    check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
    let arena = session.arena();
    let run_step = arena.alloc(Node::RunStep {
        state_ty,
        result_ty,
    });
    let motive_ty = session.infer_pts(motive)?;
    let Some((_, motive_domain, motive_body)) = expose_product(session.env(), motive_ty) else {
        return Err(failure(
            rule,
            phase,
            "RunStep recursor motive is not a family",
        ));
    };
    if !convertible(session.env(), motive_domain, run_step) {
        return Err(failure(
            rule,
            phase,
            "RunStep recursor motive has the wrong domain",
        ));
    }
    if !matches!(
        arena.get(type_head_normal(session.env(), motive_body)),
        Node::Sort(_)
    ) {
        return Err(failure(
            rule,
            phase,
            "RunStep recursor motive does not return a sort",
        ));
    }

    let shifted_state = shift_bound_indices(arena, state_ty, 1, 0);
    let shifted_result = shift_bound_indices(arena, result_ty, 1, 0);
    let continue_value = arena.alloc(Node::Continue {
        state_ty: shifted_state,
        result_ty: shifted_result,
        next: arena.bound(0),
    });
    let continue_result = arena.alloc(Node::App {
        func: shift_bound_indices(arena, motive, 1, 0),
        arg: continue_value,
    });
    session.check_pts(
        on_continue,
        arena.alloc(Node::Prod {
            var: SymbolId::ANONYMOUS,
            ty: state_ty,
            body: continue_result,
        }),
    )?;

    let finish_value = arena.alloc(Node::Finish {
        state_ty: shifted_state,
        result_ty: shifted_result,
        output: arena.bound(0),
    });
    let finish_result = arena.alloc(Node::App {
        func: shift_bound_indices(arena, motive, 1, 0),
        arg: finish_value,
    });
    session.check_pts(
        on_finish,
        arena.alloc(Node::Prod {
            var: SymbolId::ANONYMOUS,
            ty: result_ty,
            body: finish_result,
        }),
    )?;
    session.check_pts(scrutinee, run_step)?;
    Ok(arena.alloc(Node::App {
        func: motive,
        arg: scrutinee,
    }))
}

fn infer_reflected_program_case(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    indspec: crate::ids::ProgramInductiveId,
    scrutinee: Exp,
    branches: Vec<ProgramCaseBranch>,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let scrutinee_ty = session.infer_pts(scrutinee)?;
    let program_spec = session.env().program_inductive(indspec);
    let Node::IndType {
        indspec: reflected,
        parameters,
    } = arena.get(type_head_normal(session.env(), scrutinee_ty))
    else {
        return Err(failure(
            rule,
            phase,
            "reflected case scrutinee is not an inductive",
        ));
    };
    if reflected != program_spec.reflected() || branches.len() != program_spec.constructors().len()
    {
        return Err(failure(
            rule,
            phase,
            "reflected case declaration or branch count mismatch",
        ));
    }
    let reflected_spec = session.env().inductive(reflected);
    let this = arena.alloc(Node::IndType {
        indspec: reflected,
        parameters: parameters.clone(),
    });
    let mut result_ty = None;
    for (index, branch) in branches.into_iter().enumerate() {
        let constructor =
            reflected_spec.constructors()[index].instantiate_parameters(arena, &parameters);
        let constructor_ty = constructor.as_exp_with_type(arena, this);
        let (fields, _) = utils::decompose_prod(arena, constructor_ty);
        if fields.len() != branch.binders.len() {
            return Err(failure(rule, phase, "reflected case binder count mismatch"));
        }
        for (binder, (_, field_ty)) in branch.binders.iter().copied().zip(fields) {
            session.push_pts(binder, field_ty);
        }
        let branch_ty = session.infer_pts(branch.body);
        for _ in &branch.binders {
            session.pop();
        }
        let branch_ty = remove_unused_ambient_binders(arena, branch_ty?, branch.binders.len())
            .ok_or_else(|| {
                failure(
                    rule,
                    phase,
                    "reflected case result depends on branch fields",
                )
            })?;
        session.infer_sort(branch_ty)?;
        if let Some(expected) = result_ty {
            if !convertible(session.env(), expected, branch_ty) {
                return Err(failure(rule, phase, "reflected case branch type mismatch"));
            }
        } else {
            result_ty = Some(branch_ty);
        }
    }
    result_ty.ok_or_else(|| failure(rule, phase, "cannot infer an empty reflected case"))
}

fn check_closed_program_type(
    session: &mut CheckSession<'_, '_>,
    program_ty: Exp,
) -> Result<ProgramTypeClass, Box<JudgementError>> {
    let mut empty = Vec::new();
    let mut nested = CheckSession {
        env: session.env,
        current_module: session.current_module,
        context: &mut empty,
        proof_mode: session.proof_mode,
    };
    check_program_type(&mut nested, program_ty).map_err(|error| {
        Box::new(error.with_frame(
            "Box",
            "closed Program type",
            "Program type is well formed under the empty Program context",
        ))
    })
}

fn check_closed_well_terminated_program(
    session: &mut CheckSession<'_, '_>,
    program_ty: Exp,
    program: Exp,
) -> Result<(), Box<JudgementError>> {
    let class = check_closed_program_type(session, program_ty)?;
    let mut empty_program = Vec::new();
    let mut program_session = CheckSession {
        env: session.env,
        current_module: session.current_module,
        context: &mut empty_program,
        proof_mode: session.proof_mode,
    };
    match class {
        ProgramTypeClass::Value => program_session.check_well_terminated_value(program, program_ty),
        ProgramTypeClass::Computation => {
            program_session.check_well_terminated_computation(program, program_ty)
        }
    }
}

fn check_reflected_program_typing(
    session: &mut CheckSession<'_, '_>,
    program: Exp,
    program_ty: Exp,
) -> Result<(), Box<JudgementError>> {
    let reflected_ty = reflect_type(session.env(), program_ty)
        .map_err(|error| failure("WellTerminated", "reflection", &error.to_string()))?;
    let reflected_term = reflect_term(
        session.env(),
        session.current_module,
        session.context,
        program,
    )
    .map_err(|error| failure("WellTerminated", "reflection", &error.to_string()))?;
    let mut reflected_context = reflect_context(session.env(), session.context)
        .map_err(|error| failure("WellTerminated", "reflection", &error.to_string()))?;
    let mut reflected_session = CheckSession {
        env: session.env,
        current_module: session.current_module,
        context: &mut reflected_context,
        proof_mode: session.proof_mode,
    };
    reflected_session.check_pts(reflected_term, reflected_ty)
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
        Node::ValueType => "ValueType",
        Node::Bound(_) => "Bound",
        Node::ModuleParam(_) => "ModuleParam",
        Node::ReflectedProgramParam(_) => "ReflectedProgramParam",
        Node::Meta { .. } => "Meta",
        Node::Prod { .. } => "Prod",
        Node::Lam { .. } => "Lam",
        Node::App { .. } => "App",
        Node::DefinedConstant(_) => "DefinedConstant",
        Node::IndType { .. } => "IndType",
        Node::IndCtor { .. } => "IndCtor",
        Node::IndElim { .. } => "IndTypeElim",
        Node::IndProjection { .. } => "IndProjection",
        Node::ReflectedProgramCase { .. } => "ReflectedProgramCase",
        Node::ThunkType { .. } => "ThunkType",
        Node::ReturnType { .. } => "ReturnType",
        Node::ComputationFunction { .. } => "ComputationFunction",
        Node::RunStep { .. } => "RunStep",
        Node::ProgramIndType { .. } => "ProgramIndType",
        Node::Thunk { .. } => "Thunk",
        Node::Continue { .. } => "Continue",
        Node::Finish { .. } => "Finish",
        Node::ProgramIndCtor { .. } => "ProgramIndCtor",
        Node::ProgramIndProjection { .. } => "ProgramIndProjection",
        Node::Return { .. } => "Return",
        Node::Force { .. } => "Force",
        Node::ComputationLam { .. } => "ComputationLam",
        Node::ComputationApp { .. } => "ComputationApp",
        Node::Sequence { .. } => "Sequence",
        Node::ValueLet { .. } => "ValueLet",
        Node::ProgramCase { .. } => "ProgramCase",
        Node::Acc { .. } => "Acc",
        Node::Proof { .. } => "Proof",
        Node::RunStepRec { .. } => "RunStepRec",
        Node::SetRun { .. } => "SetRun",
        Node::SetRunCase { .. } => "SetRunCase",
        Node::BoxType { .. } => "BoxType",
        Node::BoxProgram { .. } => "BoxProgram",
        Node::ForceBox { .. } => "ForceBox",
        Node::BoxApp { .. } => "BoxApp",
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
        Node::AxiomSetExt { .. } => "AxiomSetExt",
        Node::AxiomFunExt { .. } => "AxiomFunExt",
        Node::AxiomClassicalIndefiniteChoice { .. } => "AxiomClassicalIndefiniteChoice",
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

fn transition_equality(
    arena: &Arena,
    state_ty: Exp,
    result_ty: Exp,
    step: Exp,
    from: Exp,
    to: Exp,
) -> Exp {
    let left = arena.alloc(Node::App {
        func: step,
        arg: from,
    });
    let right = arena.alloc(Node::Continue {
        state_ty,
        result_ty,
        next: to,
    });
    arena.alloc(Node::Equal { left, right })
}

fn set_ext_direction(arena: &Arena, carrier: Exp, source: Exp, target: Exp) -> Exp {
    let element = arena.bound(0);
    let source_membership = arena.alloc(Node::Pred {
        superset: shift_bound_indices(arena, carrier, 1, 0),
        subset: shift_bound_indices(arena, source, 1, 0),
        element,
    });
    let target_membership = arena.alloc(Node::Pred {
        superset: shift_bound_indices(arena, carrier, 2, 0),
        subset: shift_bound_indices(arena, target, 2, 0),
        element: arena.bound(1),
    });
    let implication = arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: source_membership,
        body: target_membership,
    });
    arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: carrier,
        body: implication,
    })
}

fn infer_axiom_set_ext(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    left: Exp,
    right: Exp,
    left_to_right: Exp,
    right_to_left: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let left_ty = add_infer!(session, rule, phase, left, "infer left subset type")?;
    let Node::PowerSet { set: carrier } = arena.get(type_head_normal(session.env(), left_ty))
    else {
        return Err(failure(
            rule,
            phase,
            "setext argument is not a powerset element",
        ));
    };
    if !matches!(
        add_sort!(session, rule, phase, carrier, "check setext carrier sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "setext carrier is not Set(i)"));
    }
    add_check!(session, rule, phase, right, left_ty, "check right subset")?;
    let forward_ty = set_ext_direction(arena, carrier, left, right);
    let backward_ty = set_ext_direction(arena, carrier, right, left);
    add_check!(
        session,
        rule,
        phase,
        left_to_right,
        forward_ty,
        "check forward inclusion"
    )?;
    add_check!(
        session,
        rule,
        phase,
        right_to_left,
        backward_ty,
        "check backward inclusion"
    )?;
    Ok(arena.alloc(Node::Equal { left, right }))
}

fn infer_axiom_fun_ext(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    left: Exp,
    right: Exp,
    pointwise: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    let function_ty = add_infer!(session, rule, phase, left, "infer function type")?;
    if !matches!(
        add_sort!(
            session,
            rule,
            phase,
            function_ty,
            "check function type sort"
        )?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "funext functions are not in Set(i)"));
    }
    let Node::Prod { ty: domain, .. } = arena.get(type_head_normal(session.env(), function_ty))
    else {
        return Err(failure(rule, phase, "funext argument is not a function"));
    };
    add_check!(
        session,
        rule,
        phase,
        right,
        function_ty,
        "check right function"
    )?;
    let argument = arena.bound(0);
    let left_application = arena.alloc(Node::App {
        func: shift_bound_indices(arena, left, 1, 0),
        arg: argument,
    });
    let right_application = arena.alloc(Node::App {
        func: shift_bound_indices(arena, right, 1, 0),
        arg: argument,
    });
    let pointwise_equality = arena.alloc(Node::Equal {
        left: left_application,
        right: right_application,
    });
    let pointwise_ty = arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: pointwise_equality,
    });
    add_check!(
        session,
        rule,
        phase,
        pointwise,
        pointwise_ty,
        "check pointwise equality"
    )?;
    Ok(arena.alloc(Node::Equal { left, right }))
}

fn infer_axiom_classical_indefinite_choice(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    domain: Exp,
    family: Exp,
    inhabited: Exp,
) -> Result<Exp, Box<JudgementError>> {
    let arena = session.arena();
    if !matches!(
        add_sort!(session, rule, phase, domain, "check choice domain sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "choice domain is not Set(i)"));
    }
    let family_ty = add_infer!(session, rule, phase, family, "infer choice family type")?;
    let Node::Prod {
        ty: family_domain,
        body: family_sort,
        ..
    } = arena.get(type_head_normal(session.env(), family_ty))
    else {
        return Err(failure(
            rule,
            phase,
            "choice family is not a dependent function",
        ));
    };
    if !erased_convertible(session.env(), domain, family_domain) {
        return Err(failure(rule, phase, "choice family has the wrong domain"));
    }
    if !matches!(
        arena.get(type_head_normal(session.env(), family_sort)),
        Node::Sort(Sort::Set(_))
    ) {
        return Err(failure(rule, phase, "choice family does not return Set(i)"));
    }
    let family_at = arena.alloc(Node::App {
        func: shift_bound_indices(arena, family, 1, 0),
        arg: arena.bound(0),
    });
    let exists_at = arena.alloc(Node::Exists { set: family_at });
    let inhabited_ty = arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: exists_at,
    });
    add_check!(
        session,
        rule,
        phase,
        inhabited,
        inhabited_ty,
        "check pointwise inhabitation"
    )?;
    let choice_function = arena.alloc(Node::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: family_at,
    });
    Ok(arena.alloc(Node::Exists {
        set: choice_function,
    }))
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
        Node::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => infer_axiom_set_ext(
            session,
            rule,
            phase,
            left,
            right,
            left_to_right,
            right_to_left,
        ),
        Node::AxiomFunExt {
            left,
            right,
            pointwise,
        } => infer_axiom_fun_ext(session, rule, phase, left, right, pointwise),
        Node::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            infer_axiom_classical_indefinite_choice(session, rule, phase, domain, family, inhabited)
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
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, Some(step))?;
            add_check!(
                session,
                rule,
                phase,
                state,
                state_ty,
                "check accessible state"
            )?;

            // Build the premise under b : A. All outer expressions
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
                ty: state_ty,
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
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, Some(step))?;
            add_check!(session, rule, phase, from, state_ty, "check source state")?;
            add_check!(session, rule, phase, to, state_ty, "check target state")?;
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
