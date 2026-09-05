use crate::calculus::*;
use crate::environment::{CrateEnv, DefinitionKind, ModuleParameterKind};
use crate::exp::*;
use crate::ids::{InductiveId, ModuleId, SymbolId};
use crate::inductive::{CtorBinder, eliminator_type};
use crate::program::{Program, ProgramJudgement, WellTypedProgram};
use crate::reflection::{reflect_context, reflect_term, reflect_type};
use crate::sort::Sort;
use crate::utils;
use serde::Serialize;
use std::cell::RefCell;
use tracing::{debug, error};

#[path = "program_derivation.rs"]
mod program_derivation;
pub use program_derivation::ProgramTypeClass;
use program_derivation::*;

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
pub enum RawJudgement {
    Pts { ty: RawExp },
    ValueType,
    ComputationType,
    Value { ty: RawExp },
    Computation { ty: RawExp },
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

    pub fn push(&mut self, var: SymbolId, ty: RawExp) {
        self.push_pts(var, ty);
    }

    pub fn push_pts(&mut self, var: SymbolId, ty: RawExp) {
        self.context.push(ContextEntry::Pts { var, ty });
    }

    pub fn push_program_type(&mut self, var: SymbolId) {
        self.context.push(ContextEntry::ProgramType { var });
    }

    pub fn push_program_value(&mut self, var: SymbolId, ty: RawExp) {
        self.context.push(ContextEntry::ProgramValue { var, ty });
    }

    pub fn pop(&mut self) {
        self.context
            .pop()
            .expect("CheckSession context stack underflow");
    }

    pub fn check(&mut self, term: RawExp, ty: RawExp) -> Result<(), Box<JudgementError>> {
        check(self, term, ty)
    }

    pub fn check_pts(&mut self, term: RawExp, ty: RawExp) -> Result<(), Box<JudgementError>> {
        check(self, term, ty)
    }

    pub fn infer(&mut self, term: RawExp) -> Result<RawExp, Box<JudgementError>> {
        infer(self, term)
    }

    pub fn infer_pts(&mut self, term: RawExp) -> Result<RawExp, Box<JudgementError>> {
        infer(self, term)
    }

    /// Infer a Set/Prop term and return only classified `Exp` handles.
    pub fn infer_exp_judgement(
        &mut self,
        term: RawExp,
    ) -> Result<ExpJudgement, Box<JudgementError>> {
        let ty = infer(self, term)?;
        Ok(ExpJudgement {
            term: Exp::checked(term),
            ty: Exp::checked(ty),
        })
    }

    pub fn infer_sort(&mut self, term: RawExp) -> Result<Sort, Box<JudgementError>> {
        infer_sort(self, term)
    }

    pub fn check_wellformed_context(&mut self) -> Result<(), Box<JudgementError>> {
        check_wellformed_context(self)
    }

    pub fn check_value_type(&mut self, ty: RawExp) -> Result<(), Box<JudgementError>> {
        check_value_type(self, ty)
    }

    pub fn check_computation_type(&mut self, ty: RawExp) -> Result<(), Box<JudgementError>> {
        check_computation_type(self, ty)
    }

    pub fn infer_value(&mut self, value: RawExp) -> Result<RawExp, Box<JudgementError>> {
        infer_value(self, value)
    }

    pub fn check_value(&mut self, value: RawExp, ty: RawExp) -> Result<(), Box<JudgementError>> {
        check_value(self, value, ty)
    }

    pub fn infer_computation(
        &mut self,
        computation: RawExp,
    ) -> Result<RawExp, Box<JudgementError>> {
        infer_computation(self, computation)
    }

    /// Check both Program typing and the reflected PTS typing judgement for a
    /// value under the current Program context.
    pub fn check_well_terminated_value(
        &mut self,
        value: RawExp,
        ty: RawExp,
    ) -> Result<(), Box<JudgementError>> {
        check_value(self, value, ty)?;
        check_reflected_program_typing(self, value, ty)
    }

    /// Check both Program typing and the reflected PTS typing judgement for a
    /// computation under the current Program context.
    pub fn check_well_terminated_computation(
        &mut self,
        computation: RawExp,
        ty: RawExp,
    ) -> Result<(), Box<JudgementError>> {
        check_computation(self, computation, ty)?;
        check_reflected_program_typing(self, computation, ty)
    }

    pub fn check_computation(
        &mut self,
        computation: RawExp,
        ty: RawExp,
    ) -> Result<(), Box<JudgementError>> {
        check_computation(self, computation, ty)
    }

    pub fn infer_any(&mut self, exp: RawExp) -> Result<RawJudgement, Box<JudgementError>> {
        if let Ok(ty) = self.infer_pts(exp) {
            return Ok(RawJudgement::Pts { ty });
        }
        if self.check_value_type(exp).is_ok() {
            return Ok(RawJudgement::ValueType);
        }
        if self.check_computation_type(exp).is_ok() {
            return Ok(RawJudgement::ComputationType);
        }
        if let Ok(ty) = self.infer_value(exp) {
            return Ok(RawJudgement::Value { ty });
        }
        self.infer_computation(exp)
            .map(|ty| RawJudgement::Computation { ty })
    }

    /// Classify a raw term using only Program formation/typing judgements.
    /// A [`Program`] handle is created only after the corresponding kernel
    /// judgement succeeds.
    pub fn infer_program_judgement(
        &mut self,
        raw: RawExp,
    ) -> Result<WellTypedProgram, Box<JudgementError>> {
        if self.check_value_type(raw).is_ok() {
            return Ok(WellTypedProgram {
                program: Program::checked(raw),
                judgement: ProgramJudgement::ValueType,
            });
        }
        if self.check_computation_type(raw).is_ok() {
            return Ok(WellTypedProgram {
                program: Program::checked(raw),
                judgement: ProgramJudgement::ComputationType,
            });
        }
        if let Ok(ty) = self.infer_value(raw) {
            return Ok(WellTypedProgram {
                program: Program::checked(raw),
                judgement: ProgramJudgement::Value {
                    ty: Program::checked(ty),
                },
            });
        }
        let ty = self.infer_computation(raw)?;
        Ok(WellTypedProgram {
            program: Program::checked(raw),
            judgement: ProgramJudgement::Computation {
                ty: Program::checked(ty),
            },
        })
    }

    fn require_provable(
        &mut self,
        proposition: RawExp,
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
    term: RawExp,
    ty: RawExp,
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

    if matches!(arena.get(ty), RawNode::Sort(sort) if sort.type_of_sort().is_none())
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
    if let (RawNode::Sort(inferred), RawNode::Sort(expected)) =
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

fn infer(session: &mut CheckSession<'_, '_>, term: RawExp) -> Result<RawExp, Box<JudgementError>> {
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
        RawNode::Sort(sort) => sort
            .type_of_sort()
            .map(|sort| arena.sort(sort))
            .ok_or_else(|| failure(rule, phase, "no sort of sort found")),
        RawNode::ValueType => Err(failure(
            rule,
            phase,
            "Program type universe used in the PTS judgement",
        )),
        RawNode::Bound(index) => session
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
        RawNode::ModuleParam(parameter) => session
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
        RawNode::ReflectedProgramParam(parameter) => session
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
        RawNode::Meta { .. } => Err(failure(
            rule,
            phase,
            "unresolved metavariable reached the strict kernel checker",
        )),
        RawNode::Prod { var, ty, body } => {
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
        RawNode::Lam { var, ty, body } => {
            add_sort!(session, rule, phase, ty, "infer domain sort for lambda")?;
            session.push(var, ty);
            let body_ty = add_infer!(session, rule, phase, body, "infer body type for lambda");
            session.pop();
            let body_ty = body_ty?;
            let lambda_ty = arena.alloc(RawNode::Prod {
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
        RawNode::App { func, arg } => {
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
        RawNode::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::Pts {
                Ok(definition.ty)
            } else {
                Err(failure(rule, phase, "definition is not a PTS term"))
            }
        }
        RawNode::IndType {
            indspec,
            parameters,
        } => {
            let env = session.env();
            let spec = env.inductive(indspec);
            check_parameters(session, rule, phase, &parameters, spec.parameters())?;
            Ok(instantiate_telescope(arena, spec.arity(arena), &parameters))
        }
        RawNode::IndCtor {
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
        RawNode::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => infer_ind_elim(session, rule, phase, indspec, elim, return_type, cases),
        RawNode::IndProjection {
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
            let structure_ty = arena.alloc(RawNode::IndType {
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
                    arena.alloc(RawNode::IndProjection {
                        indspec,
                        parameters: parameters.clone(),
                        value,
                        field,
                    })
                })
                .collect::<Vec<_>>();
            Ok(instantiate_telescope(arena, *field_ty, &preceding))
        }
        RawNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => infer_reflected_program_case(session, rule, phase, indspec, scrutinee, branches),
        RawNode::RunStep {
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
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
            add_check!(session, rule, phase, next, state_ty, "check next state")?;
            Ok(arena.alloc(RawNode::RunStep {
                state_ty,
                result_ty,
            }))
        }
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
            add_check!(session, rule, phase, output, result_ty, "check final result")?;
            Ok(arena.alloc(RawNode::RunStep {
                state_ty,
                result_ty,
            }))
        }
        RawNode::Acc {
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
        RawNode::Proof { proposition } => {
            if add_sort!(session, rule, phase, proposition, "check proposition")? != Sort::Prop {
                return Err(failure(rule, phase, "Proof argument is not a proposition"));
            }
            session.require_provable(proposition, "Proof")?;
            Ok(proposition)
        }
        RawNode::SetRun {
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
            let accessibility = arena.alloc(RawNode::Acc {
                state_ty,
                result_ty,
                step,
                state: initial,
            });
            session.require_provable(accessibility, "SetRun")?;
            Ok(result_ty)
        }
        RawNode::SetRunCase {
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
            let run_step = arena.alloc(RawNode::RunStep {
                state_ty,
                result_ty,
            });
            add_check!(session, rule, phase, transition, run_step, "check transition")?;
            session.require_provable(
                arena.alloc(RawNode::Acc {
                    state_ty,
                    result_ty,
                    step,
                    state: initial,
                }),
                "SetRunCase",
            )?;
            session.require_provable(
                arena.alloc(RawNode::Equal {
                    left: arena.alloc(RawNode::App {
                        func: step,
                        arg: initial,
                    }),
                    right: transition,
                }),
                "SetRunCase",
            )?;
            Ok(result_ty)
        }
        RawNode::RunStepRec {
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
        RawNode::BoxType { program_ty } => {
            check_closed_program_type(session, program_ty)?;
            Ok(arena.sort(Sort::Set(0)))
        }
        RawNode::BoxProgram {
            program_ty,
            program,
        } => {
            check_closed_well_terminated_program(session, program_ty, program)?;
            Ok(arena.alloc(RawNode::BoxType { program_ty }))
        }
        RawNode::ForceBox { program_ty, boxed } => {
            check_closed_program_type(session, program_ty)?;
            add_check!(
                session,
                rule,
                phase,
                boxed,
                arena.alloc(RawNode::BoxType { program_ty }),
                "check boxed Program"
            )?;
            reflect_type(session.env(), program_ty)
                .map_err(|error| failure(rule, phase, &format!("cannot reflect type: {error}")))
        }
        RawNode::BoxApp { function, argument } => {
            let function_ty = add_infer!(session, rule, phase, function, "infer boxed function")?;
            let RawNode::BoxType { program_ty } = arena.get(type_head_normal(session.env(), function_ty)) else {
                return Err(failure(rule, phase, "boxed application head is not Box(P)"));
            };
            let RawNode::ComputationFunction { domain, codomain } = arena.get(program_ty) else {
                return Err(failure(rule, phase, "boxed application head is not a computation function"));
            };
            add_check!(
                session,
                rule,
                phase,
                argument,
                arena.alloc(RawNode::BoxType { program_ty: domain }),
                "check boxed argument"
            )?;
            Ok(arena.alloc(RawNode::BoxType { program_ty: codomain }))
        }
        RawNode::RfType { compute_ty } => {
            Err(failure(
                rule,
                phase,
                &format!(
                    "RfType is no longer a term; meta-level reflection of {} is required",
                    crate::printing::format_exp(session.env(), compute_ty)
                ),
            ))
        }
        RawNode::RfTerm { .. } => Err(failure(
            rule,
            phase,
            "RfTerm is no longer a term; reflection is a meta-level map",
        )),
        RawNode::ThunkType { .. }
        | RawNode::ReturnType { .. }
        | RawNode::ComputationFunction { .. }
        | RawNode::ProgramIndType { .. }
        | RawNode::Thunk { .. }
        | RawNode::ProgramIndCtor { .. }
        | RawNode::ProgramIndProjection { .. }
        | RawNode::Return { .. }
        | RawNode::Force { .. }
        | RawNode::ComputationLam { .. }
        | RawNode::ComputationApp { .. }
        | RawNode::Sequence { .. }
        | RawNode::ValueLet { .. }
        | RawNode::ProgramCase { .. }
        | RawNode::Run { .. }
        | RawNode::RunCase { .. } => Err(failure(
            rule,
            phase,
            "Program expression used in the PTS judgement",
        )),
        RawNode::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            let sort = add_sort!(session, rule, phase, superset, "check carrier sort")?;
            if !matches!(sort, Sort::Set(_)) {
                return Err(failure(rule, phase, "SubsetIntro carrier is not Set(i)"));
            }
            let power = arena.alloc(RawNode::PowerSet { set: superset });
            add_check!(session, rule, phase, subset, power, "check subset")?;
            add_check!(session, rule, phase, element, superset, "check element")?;
            let membership = arena.alloc(RawNode::Pred {
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
            Ok(arena.alloc(RawNode::TypeLift { superset, subset }))
        }
        RawNode::PowerSet { set } => match add_sort!(session, rule, phase, set, "check set sort")? {
            Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
            _ => Err(failure(rule, phase, "set is not of Set(i)")),
        },
        RawNode::SubSet {
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
            Ok(arena.alloc(RawNode::PowerSet { set }))
        }
        RawNode::Pred {
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
            let power = arena.alloc(RawNode::PowerSet { set: superset });
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
        RawNode::TypeLift { superset, subset } => {
            let Sort::Set(level) =
                add_sort!(session, rule, phase, superset, "check superset sort")?
            else {
                return Err(failure(rule, phase, "superset is not of Set(i)"));
            };
            let power = arena.alloc(RawNode::PowerSet { set: superset });
            add_check!(session, rule, phase, subset, power, "check subset type")?;
            Ok(arena.sort(Sort::Set(level)))
        }
        RawNode::Equal { left, right } => {
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
        RawNode::Exists { set } => {
            if !matches!(
                add_sort!(session, rule, phase, set, "check set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "set is not of Set(i)"));
            }
            Ok(arena.sort(Sort::Prop))
        }
        RawNode::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => infer_take_set(
            session, rule, phase, domain, codomain, map, existence, uniqueness,
        ),
        RawNode::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => infer_take_prop(session, rule, phase, domain, proposition, map, existence),
        RawNode::ExistsIntro { .. }
        | RawNode::SubsetElim { .. }
        | RawNode::IdRefl { .. }
        | RawNode::IdElim { .. }
        | RawNode::AxiomSetExt { .. }
        | RawNode::AxiomFunExt { .. }
        | RawNode::AxiomClassicalIndefiniteChoice { .. }
        | RawNode::TakeEq { .. }
        | RawNode::AccIntro { .. }
        | RawNode::AccDescent { .. } => infer_proof_constructor(session, term),
    }
}

fn run_step_type(arena: &Arena, state_ty: RawExp, result_ty: RawExp) -> RawExp {
    arena.alloc(RawNode::RunStep {
        state_ty,
        result_ty,
    })
}

fn nondependent_product(arena: &Arena, domain: RawExp, codomain: RawExp) -> RawExp {
    arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    })
}

fn accessibility_type(
    arena: &Arena,
    state_ty: RawExp,
    result_ty: RawExp,
    step: RawExp,
    state: RawExp,
) -> RawExp {
    arena.alloc(RawNode::Acc {
        state_ty,
        result_ty,
        step,
        state,
    })
}

fn check_set_recursion_signature(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    state_ty: RawExp,
    result_ty: RawExp,
    step: Option<RawExp>,
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
        let run_step = session.arena().alloc(RawNode::RunStep {
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
    state_ty: RawExp,
    result_ty: RawExp,
    motive: RawExp,
    on_continue: RawExp,
    on_finish: RawExp,
    scrutinee: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    check_set_recursion_signature(session, rule, phase, state_ty, result_ty, None)?;
    let arena = session.arena();
    let run_step = arena.alloc(RawNode::RunStep {
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
        RawNode::Sort(_)
    ) {
        return Err(failure(
            rule,
            phase,
            "RunStep recursor motive does not return a sort",
        ));
    }

    let shifted_state = shift_bound_indices(arena, state_ty, 1, 0);
    let shifted_result = shift_bound_indices(arena, result_ty, 1, 0);
    let continue_value = arena.alloc(RawNode::Continue {
        state_ty: shifted_state,
        result_ty: shifted_result,
        next: arena.bound(0),
    });
    let continue_result = arena.alloc(RawNode::App {
        func: shift_bound_indices(arena, motive, 1, 0),
        arg: continue_value,
    });
    session.check_pts(
        on_continue,
        arena.alloc(RawNode::Prod {
            var: SymbolId::ANONYMOUS,
            ty: state_ty,
            body: continue_result,
        }),
    )?;

    let finish_value = arena.alloc(RawNode::Finish {
        state_ty: shifted_state,
        result_ty: shifted_result,
        output: arena.bound(0),
    });
    let finish_result = arena.alloc(RawNode::App {
        func: shift_bound_indices(arena, motive, 1, 0),
        arg: finish_value,
    });
    session.check_pts(
        on_finish,
        arena.alloc(RawNode::Prod {
            var: SymbolId::ANONYMOUS,
            ty: result_ty,
            body: finish_result,
        }),
    )?;
    session.check_pts(scrutinee, run_step)?;
    Ok(arena.alloc(RawNode::App {
        func: motive,
        arg: scrutinee,
    }))
}

fn infer_reflected_program_case(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    indspec: crate::ids::ProgramInductiveId,
    scrutinee: RawExp,
    branches: Vec<ProgramCaseBranch>,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let scrutinee_ty = session.infer_pts(scrutinee)?;
    let program_spec = session.env().program_inductive(indspec);
    let RawNode::IndType {
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
    let this = arena.alloc(RawNode::IndType {
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
    program_ty: RawExp,
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
    program_ty: RawExp,
    program: RawExp,
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
    program: RawExp,
    program_ty: RawExp,
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
    parameters: &[RawExp],
    expected: &[(SymbolId, RawExp)],
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
    elim: RawExp,
    return_type: RawExp,
    cases: Vec<RawExp>,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let inferred = add_infer!(session, rule, phase, elim, "infer eliminator type")?;
    let inferred = base_carrier(session.env(), inferred);
    let (head, indices) = utils::decompose_app(arena, inferred);
    let RawNode::IndType {
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
    let RawNode::Sort(sort) = arena.get(result) else {
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
    let this = arena.alloc(RawNode::IndType {
        indspec,
        parameters: parameters.clone(),
    });
    for (index, case) in cases.iter().enumerate() {
        let constructor_ty = spec.constructors()[index].instantiate_parameters(arena, &parameters);
        let constructor = arena.alloc(RawNode::IndCtor {
            indspec,
            parameters: parameters.clone(),
            idx: index,
        });
        let case_ty = eliminator_type(arena, &constructor_ty, return_type, constructor, this);
        add_check!(session, rule, phase, *case, case_ty, "check case type")?;
    }
    let motive = utils::assoc_apply(arena, return_type, indices);
    Ok(arena.alloc(RawNode::App {
        func: motive,
        arg: elim,
    }))
}

#[allow(clippy::too_many_arguments)]
fn infer_take_set(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    domain: RawExp,
    codomain: RawExp,
    map: RawExp,
    existence: RawExp,
    uniqueness: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
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
    let map_ty = arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    });
    add_check!(session, rule, phase, map, map_ty, "check map type")?;
    let exists = arena.alloc(RawNode::Exists { set: domain });
    add_check!(session, rule, phase, existence, exists, "check existence")?;

    let x1 = SymbolId::ANONYMOUS;
    let x2 = SymbolId::ANONYMOUS;
    let map = shift_bound_indices(arena, map, 2, 0);
    let map_x1 = arena.alloc(RawNode::App {
        func: map,
        arg: arena.bound(1),
    });
    let map_x2 = arena.alloc(RawNode::App {
        func: map,
        arg: arena.bound(0),
    });
    let equality = arena.alloc(RawNode::Equal {
        left: map_x1,
        right: map_x2,
    });
    let inner = arena.alloc(RawNode::Prod {
        var: x2,
        ty: shift_bound_indices(arena, domain, 1, 0),
        body: equality,
    });
    let uniqueness_ty = arena.alloc(RawNode::Prod {
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
    domain: RawExp,
    proposition: RawExp,
    map: RawExp,
    existence: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
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
    let map_ty = arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, proposition, 1, 0),
    });
    add_check!(session, rule, phase, map, map_ty, "check map")?;
    let exists = arena.alloc(RawNode::Exists { set: domain });
    add_check!(session, rule, phase, existence, exists, "check existence")?;
    Ok(proposition)
}

fn exp_rule(arena: &Arena, term: RawExp) -> &'static str {
    match arena.get(term) {
        RawNode::Sort(_) => "Sort",
        RawNode::ValueType => "ValueType",
        RawNode::Bound(_) => "Bound",
        RawNode::ModuleParam(_) => "ModuleParam",
        RawNode::ReflectedProgramParam(_) => "ReflectedProgramParam",
        RawNode::Meta { .. } => "Meta",
        RawNode::Prod { .. } => "Prod",
        RawNode::Lam { .. } => "Lam",
        RawNode::App { .. } => "App",
        RawNode::DefinedConstant(_) => "DefinedConstant",
        RawNode::IndType { .. } => "IndType",
        RawNode::IndCtor { .. } => "IndCtor",
        RawNode::IndElim { .. } => "IndTypeElim",
        RawNode::IndProjection { .. } => "IndProjection",
        RawNode::ReflectedProgramCase { .. } => "ReflectedProgramCase",
        RawNode::ThunkType { .. } => "ThunkType",
        RawNode::ReturnType { .. } => "ReturnType",
        RawNode::ComputationFunction { .. } => "ComputationFunction",
        RawNode::RunStep { .. } => "RunStep",
        RawNode::ProgramIndType { .. } => "ProgramIndType",
        RawNode::Thunk { .. } => "Thunk",
        RawNode::Continue { .. } => "Continue",
        RawNode::Finish { .. } => "Finish",
        RawNode::ProgramIndCtor { .. } => "ProgramIndCtor",
        RawNode::ProgramIndProjection { .. } => "ProgramIndProjection",
        RawNode::Return { .. } => "Return",
        RawNode::Force { .. } => "Force",
        RawNode::ComputationLam { .. } => "ComputationLam",
        RawNode::ComputationApp { .. } => "ComputationApp",
        RawNode::Sequence { .. } => "Sequence",
        RawNode::ValueLet { .. } => "ValueLet",
        RawNode::ProgramCase { .. } => "ProgramCase",
        RawNode::Acc { .. } => "Acc",
        RawNode::Proof { .. } => "Proof",
        RawNode::RunStepRec { .. } => "RunStepRec",
        RawNode::SetRun { .. } => "SetRun",
        RawNode::SetRunCase { .. } => "SetRunCase",
        RawNode::BoxType { .. } => "BoxType",
        RawNode::BoxProgram { .. } => "BoxProgram",
        RawNode::ForceBox { .. } => "ForceBox",
        RawNode::BoxApp { .. } => "BoxApp",
        RawNode::RfType { .. } => "RfType",
        RawNode::RfTerm { .. } => "RfTerm",
        RawNode::Run { .. } => "Run",
        RawNode::RunCase { .. } => "RunCase",
        RawNode::AccIntro { .. } => "AccIntro",
        RawNode::AccDescent { .. } => "AccDescent",
        RawNode::SubsetIntro { .. } => "SubsetIntro",
        RawNode::PowerSet { .. } => "PowerSet",
        RawNode::SubSet { .. } => "SubSet",
        RawNode::Pred { .. } => "Pred",
        RawNode::TypeLift { .. } => "TypeLift",
        RawNode::Equal { .. } => "Equal",
        RawNode::Exists { .. } => "Exists",
        RawNode::TakeSet { .. } => "TakeSet",
        RawNode::TakeProp { .. } => "TakeProp",
        RawNode::ExistsIntro { .. } => "ExistsIntro",
        RawNode::SubsetElim { .. } => "SubsetElim",
        RawNode::IdRefl { .. } => "IdRefl",
        RawNode::IdElim { .. } => "IdElim",
        RawNode::AxiomSetExt { .. } => "AxiomSetExt",
        RawNode::AxiomFunExt { .. } => "AxiomFunExt",
        RawNode::AxiomClassicalIndefiniteChoice { .. } => "AxiomClassicalIndefiniteChoice",
        RawNode::TakeEq { .. } => "TakeEq",
    }
}

fn infer_sort(
    session: &mut CheckSession<'_, '_>,
    term: RawExp,
) -> Result<Sort, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Conv";
    let phase = "infer(sort)";
    let inferred_ty = add_infer!(session, rule, phase, term, "infer type of term")?;
    if let RawNode::Sort(sort) = arena.get(inferred_ty) {
        return Ok(sort);
    }
    let normalized = type_head_normal(session.env(), inferred_ty);
    let RawNode::Sort(sort) = arena.get(normalized) else {
        return Err(failure(rule, phase, "Type is not convertible to a sort"));
    };
    Ok(sort)
}

fn transition_equality(
    arena: &Arena,
    state_ty: RawExp,
    result_ty: RawExp,
    step: RawExp,
    from: RawExp,
    to: RawExp,
) -> RawExp {
    let left = arena.alloc(RawNode::App {
        func: step,
        arg: from,
    });
    let right = arena.alloc(RawNode::Continue {
        state_ty,
        result_ty,
        next: to,
    });
    arena.alloc(RawNode::Equal { left, right })
}

fn set_ext_direction(arena: &Arena, carrier: RawExp, source: RawExp, target: RawExp) -> RawExp {
    let element = arena.bound(0);
    let source_membership = arena.alloc(RawNode::Pred {
        superset: shift_bound_indices(arena, carrier, 1, 0),
        subset: shift_bound_indices(arena, source, 1, 0),
        element,
    });
    let target_membership = arena.alloc(RawNode::Pred {
        superset: shift_bound_indices(arena, carrier, 2, 0),
        subset: shift_bound_indices(arena, target, 2, 0),
        element: arena.bound(1),
    });
    let implication = arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: source_membership,
        body: target_membership,
    });
    arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: carrier,
        body: implication,
    })
}

fn infer_axiom_set_ext(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    left: RawExp,
    right: RawExp,
    left_to_right: RawExp,
    right_to_left: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let left_ty = add_infer!(session, rule, phase, left, "infer left subset type")?;
    let RawNode::PowerSet { set: carrier } = arena.get(type_head_normal(session.env(), left_ty))
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
    Ok(arena.alloc(RawNode::Equal { left, right }))
}

fn infer_axiom_fun_ext(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    left: RawExp,
    right: RawExp,
    pointwise: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
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
    let RawNode::Prod { ty: domain, .. } = arena.get(type_head_normal(session.env(), function_ty))
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
    let left_application = arena.alloc(RawNode::App {
        func: shift_bound_indices(arena, left, 1, 0),
        arg: argument,
    });
    let right_application = arena.alloc(RawNode::App {
        func: shift_bound_indices(arena, right, 1, 0),
        arg: argument,
    });
    let pointwise_equality = arena.alloc(RawNode::Equal {
        left: left_application,
        right: right_application,
    });
    let pointwise_ty = arena.alloc(RawNode::Prod {
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
    Ok(arena.alloc(RawNode::Equal { left, right }))
}

fn infer_axiom_classical_indefinite_choice(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    domain: RawExp,
    family: RawExp,
    inhabited: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    if !matches!(
        add_sort!(session, rule, phase, domain, "check choice domain sort")?,
        Sort::Set(_)
    ) {
        return Err(failure(rule, phase, "choice domain is not Set(i)"));
    }
    let family_ty = add_infer!(session, rule, phase, family, "infer choice family type")?;
    let RawNode::Prod {
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
        RawNode::Sort(Sort::Set(_))
    ) {
        return Err(failure(rule, phase, "choice family does not return Set(i)"));
    }
    let family_at = arena.alloc(RawNode::App {
        func: shift_bound_indices(arena, family, 1, 0),
        arg: arena.bound(0),
    });
    let exists_at = arena.alloc(RawNode::Exists { set: family_at });
    let inhabited_ty = arena.alloc(RawNode::Prod {
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
    let choice_function = arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: family_at,
    });
    Ok(arena.alloc(RawNode::Exists {
        set: choice_function,
    }))
}

fn infer_proof_constructor(
    session: &mut CheckSession<'_, '_>,
    term: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = exp_rule(arena, term);
    let phase = "infer";
    match arena.get(term) {
        RawNode::ExistsIntro { element, set } => {
            add_check!(session, rule, phase, element, set, "check element")?;
            if !matches!(
                add_sort!(session, rule, phase, set, "infer set sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            Ok(arena.alloc(RawNode::Exists { set }))
        }
        RawNode::SubsetElim {
            element,
            subset,
            superset,
        } => {
            let lifted = arena.alloc(RawNode::TypeLift { superset, subset });
            add_check!(
                session,
                rule,
                phase,
                element,
                lifted,
                "check subset elimination"
            )?;
            Ok(arena.alloc(RawNode::Pred {
                superset,
                subset,
                element,
            }))
        }
        RawNode::IdRefl { element } => {
            let ty = add_infer!(session, rule, phase, element, "infer element type")?;
            if !matches!(
                add_sort!(session, rule, phase, ty, "infer type sort")?,
                Sort::Set(_)
            ) {
                return Err(failure(rule, phase, "type is not Set(i)"));
            }
            Ok(arena.alloc(RawNode::Equal {
                left: element,
                right: element,
            }))
        }
        RawNode::IdElim {
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
            let apply = arena.alloc(RawNode::Lam {
                var,
                ty,
                body: predicate,
            });
            let base_prop = arena.alloc(RawNode::App {
                func: apply,
                arg: left,
            });
            add_check!(session, rule, phase, base, base_prop, "check base")?;
            let equality_prop = arena.alloc(RawNode::Equal { left, right });
            add_check!(
                session,
                rule,
                phase,
                equality,
                equality_prop,
                "check equality"
            )?;
            Ok(arena.alloc(RawNode::App {
                func: apply,
                arg: right,
            }))
        }
        RawNode::AxiomSetExt {
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
        RawNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => infer_axiom_fun_ext(session, rule, phase, left, right, pointwise),
        RawNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            infer_axiom_classical_indefinite_choice(session, rule, phase, domain, family, inhabited)
        }
        RawNode::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            let take = arena.alloc(RawNode::TakeSet {
                domain,
                codomain,
                map: func,
                existence,
                uniqueness,
            });
            add_check!(session, rule, phase, take, codomain, "check take")?;
            add_check!(session, rule, phase, element, domain, "check element")?;
            let mapped = arena.alloc(RawNode::App { func, arg: element });
            Ok(arena.alloc(RawNode::Equal {
                left: take,
                right: mapped,
            }))
        }
        RawNode::AccIntro {
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
            let expected_predecessors = arena.alloc(RawNode::Prod {
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
        RawNode::AccDescent {
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
