//! Elaboration-time contextual metavariables and their diagnostics.

use crate::raw::{
    calculus::{
        can_weaken_to, common_ambient_carrier, erased_convertible, instantiate_telescope,
        map_children, remove_unused_ambient_binders, shift_bound_indices,
    },
    derivation::CheckSession,
    environment::{CrateEnv, DefinedConstant, ModuleParameterKind},
    exp::{Exp, ExpContext, ExpContextEntry, ExpNode, Prove},
    ids::{MetaVarId, ModuleId, SymbolId},
    program::ComputationTypeNode,
    program_derivation::ProgramCheckSession,
    sort::Sort,
};
use crate::syntax::{SourceSpan, SurfaceMeta};
use std::collections::{HashMap, HashSet};

mod diagnostics;
pub use diagnostics::{
    ConstraintRecord, ConstraintStatus, ElaborationError, GoalConstraint, MetaFlavor, MetaGoal,
    format_elaboration_error,
};

#[derive(Debug, Clone)]
struct MetaEntry {
    flavor: MetaFlavor,
    span: SourceSpan,
    context: ExpContext,
    scope_len: usize,
    assignment: Option<Exp>,
    principal: Option<GoalConstraint>,
    inferred_type: Option<Exp>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct MetaStore {
    entries: Vec<MetaEntry>,
    named: HashMap<u32, MetaVarId>,
    constraints: Vec<ConstraintRecord>,
}

impl MetaStore {
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.named.clear();
        self.constraints.clear();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn constraint_error(&self, message: String) -> ElaborationError {
        ElaborationError::ConstraintFailure {
            message,
            constraints: self.constraints.clone(),
        }
    }

    pub(crate) fn fresh(
        &mut self,
        env: &CrateEnv,
        kind: SurfaceMeta,
        span: SourceSpan,
        context: &ExpContext,
        scope_len: usize,
    ) -> Exp {
        let flavor = MetaFlavor::from(kind);
        let existing = match flavor {
            MetaFlavor::Named(number) => self.named.get(&number).cloned(),
            MetaFlavor::Implicit | MetaFlavor::Goal | MetaFlavor::Synthetic => None,
        };
        let metavariable = existing.unwrap_or_else(|| {
            let id = MetaVarId(
                u32::try_from(self.entries.len()).expect("metavariable table exceeded u32::MAX"),
            );
            self.entries.push(MetaEntry {
                flavor,
                span,
                context: context.clone(),
                scope_len,
                assignment: None,
                principal: None,
                inferred_type: None,
            });
            if let MetaFlavor::Named(number) = flavor {
                self.named.insert(number, id);
            }
            id
        });
        if existing.is_some() {
            let entry = &mut self.entries[metavariable.index()];
            let previous_start = entry.context.len().saturating_sub(entry.scope_len);
            let current_start = context.len().saturating_sub(scope_len);
            let common = entry.context[previous_start..]
                .iter()
                .zip(&context[current_start..])
                .take_while(|(left, right)| left.var == right.var)
                .count();
            if common < entry.scope_len {
                let removed = entry.scope_len - common;
                entry.scope_len = common;
                entry.context = context[..current_start + common].to_vec();
                if let Some(assignment) = entry.assignment.clone() {
                    entry.assignment =
                        remove_unused_ambient_binders(env.arena(), assignment, removed);
                }
            }
        }

        let spine = (0..scope_len)
            .rev()
            .map(|index| env.arena().exp_bound(index))
            .collect();
        env.arena().alloc(ExpNode::Meta {
            metavariable,
            spine,
        })
    }

    pub(crate) fn constrain(&mut self, constraint: GoalConstraint) {
        self.constraints.push(ConstraintRecord {
            original: constraint.clone(),
            normalized: constraint,
            status: ConstraintStatus::Residual,
        });
    }

    fn set_principal_for_meta(&mut self, env: &CrateEnv, term: Exp, constraint: &GoalConstraint) {
        if let ExpNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term))
            && self.entries[metavariable.index()].principal.is_none()
        {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
    }

    fn fresh_synthetic(&mut self, env: &CrateEnv, context: &ExpContext, span: SourceSpan) -> Exp {
        let id = MetaVarId(
            u32::try_from(self.entries.len()).expect("metavariable table exceeded u32::MAX"),
        );
        self.entries.push(MetaEntry {
            flavor: MetaFlavor::Synthetic,
            span,
            context: context.clone(),
            scope_len: context.len(),
            assignment: None,
            principal: None,
            inferred_type: None,
        });
        let spine = (0..context.len())
            .rev()
            .map(|index| env.arena().exp_bound(index))
            .collect();
        env.arena().alloc(ExpNode::Meta {
            metavariable: id,
            spine,
        })
    }

    fn set_meta_type(&mut self, env: &CrateEnv, term: Exp, expected: Exp) -> Result<(), String> {
        let ExpNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term.clone()))
        else {
            return Ok(());
        };
        let constraint = GoalConstraint::HasType {
            term,
            expected: expected.clone(),
        };
        if self.entries[metavariable.index()].principal.is_none() {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
        self.constrain(constraint);
        if let Some(previous) = self.entries[metavariable.index()].inferred_type.clone() {
            self.unify(env, previous, expected)?;
        } else {
            self.entries[metavariable.index()].inferred_type = Some(expected);
        }
        Ok(())
    }

    fn type_of_meta(
        &mut self,
        env: &CrateEnv,
        term: Exp,
        context: &ExpContext,
    ) -> Result<Exp, String> {
        let ExpNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term.clone()))
        else {
            return Err("expected metavariable".into());
        };
        if let Some(ty) = self.entries[metavariable.index()].inferred_type.clone() {
            return Ok(self.zonk(env, ty));
        }
        let span = self.entries[metavariable.index()].span;
        let ty = self.fresh_synthetic(env, context, span);
        self.entries[metavariable.index()].inferred_type = Some(ty.clone());
        let constraint = GoalConstraint::HasType {
            term,
            expected: ty.clone(),
        };
        self.entries[metavariable.index()].principal = Some(constraint.clone());
        self.constrain(constraint);
        Ok(ty)
    }

    pub(crate) fn check_pts(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
        expected: Exp,
    ) -> Result<(), String> {
        let term = self.zonk(env, term);
        let expected = self.zonk(env, expected);
        if matches!(env.arena().get(term.clone()), ExpNode::Meta { .. }) {
            return self.set_meta_type(env, term, expected);
        }
        if matches!(env.arena().get(expected.clone()), ExpNode::Meta { .. }) {
            let inferred = self.infer_pts(env, module, context, term)?;
            self.unify(env, expected, inferred)?;
            return Ok(());
        }
        if let (
            ExpNode::Lam { var, ty, body },
            ExpNode::Prod {
                ty: expected_ty,
                body: expected_body,
                ..
            },
        ) = (
            env.arena().get(term.clone()),
            env.arena().get(expected.clone()),
        ) {
            self.unify(env, ty, expected_ty.clone())?;
            context.push(ExpContextEntry {
                var,
                ty: expected_ty,
            });
            let result = self.check_pts(env, module, context, body, expected_body);
            context.pop();
            return result;
        }
        let inferred = self.infer_pts(env, module, context, term)?;
        self.check_pts_types(env, inferred, expected)
    }

    fn check_pts_types(
        &mut self,
        env: &CrateEnv,
        inferred: Exp,
        expected: Exp,
    ) -> Result<(), String> {
        let inferred = self.zonk(env, inferred);
        let expected = self.zonk(env, expected);
        if can_weaken_to(env, inferred.clone(), expected.clone()) {
            return Ok(());
        }
        if let (ExpNode::Sort(inferred), ExpNode::Sort(expected)) = (
            env.arena().get(inferred.clone()),
            env.arena().get(expected.clone()),
        ) && inferred.can_lift_to(expected)
        {
            return Ok(());
        }
        self.unify(env, expected, inferred).map(|_| ())
    }

    pub(crate) fn infer_pts(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
    ) -> Result<Exp, String> {
        let term = self.zonk(env, term);
        if !self.contains_unsolved(env, term.clone()) {
            return CheckSession::new(env, module, context)
                .infer_pts(term)
                .map_err(|error| format!("{error:?}"));
        }
        let arena = env.arena();
        match arena.get(term.clone()) {
            ExpNode::Meta { .. } => self.type_of_meta(env, term, context),
            ExpNode::Sort(sort) => sort
                .type_of_sort()
                .map(|sort| arena.sort(sort))
                .ok_or_else(|| "no sort of sort found".into()),
            ExpNode::Bound(index) => context
                .len()
                .checked_sub(index + 1)
                .and_then(|position| context.get(position))
                .map(|entry| shift_bound_indices(arena, entry.ty.clone(), index + 1, 0))
                .ok_or_else(|| "bound variable is not a PTS term".into()),
            ExpNode::ModuleParam(parameter) => env
                .module_parameter_opt(parameter)
                .and_then(|parameter| match &parameter.kind {
                    ModuleParameterKind::Pts { ty } => Some(ty.clone()),
                    _ => None,
                })
                .ok_or_else(|| "module parameter is not a PTS term".into()),
            ExpNode::DefinedConstant(definition) => {
                let definition = env.definition(definition);
                match definition {
                    DefinedConstant::Pts { ty, .. } => Ok(ty.clone()),
                    _ => Err("definition is not a PTS term".into()),
                }
            }
            ExpNode::IndType {
                indspec,
                parameters,
            } => {
                let spec = env.inductive(indspec);
                if parameters.len() != spec.parameters().len() {
                    return Err("inductive parameter count mismatch".into());
                }
                let mut preceding = Vec::new();
                for (argument, (_, expected)) in parameters.iter().cloned().zip(spec.parameters()) {
                    let expected = crate::raw::calculus::instantiate_telescope(
                        arena,
                        expected.clone(),
                        &preceding,
                    );
                    self.check_pts(env, module, context, argument.clone(), expected)?;
                    preceding.push(argument);
                }
                Ok(crate::raw::calculus::instantiate_telescope(
                    arena,
                    spec.arity(arena),
                    &parameters,
                ))
            }
            ExpNode::IndCtor {
                indspec,
                parameters,
                idx,
            } => {
                let spec = env.inductive(indspec);
                if parameters.len() != spec.parameters().len() {
                    return Err("constructor parameter count mismatch".into());
                }
                let mut preceding = Vec::new();
                for (argument, (_, expected)) in parameters.iter().cloned().zip(spec.parameters()) {
                    let expected = crate::raw::calculus::instantiate_telescope(
                        arena,
                        expected.clone(),
                        &preceding,
                    );
                    self.check_pts(env, module, context, argument.clone(), expected)?;
                    preceding.push(argument);
                }
                if idx >= spec.constructor_len() {
                    return Err("constructor index out of bounds".into());
                }
                Ok(
                    crate::raw::inductive::InductiveTypeSpecs::type_of_constructor(
                        arena, indspec, spec, idx, parameters,
                    ),
                )
            }
            ExpNode::Prod { var, ty, body } => {
                let domain_sort = self.infer_sort(env, module, context, ty.clone())?;
                context.push(ExpContextEntry { var, ty });
                let body_sort = self.infer_sort(env, module, context, body);
                context.pop();
                let body_sort = body_sort?;
                domain_sort
                    .relation_of_sort(body_sort)
                    .map(|sort| arena.sort(sort))
                    .ok_or_else(|| "no sort relation for product".into())
            }
            ExpNode::Lam { var, ty, body } => {
                self.infer_sort(env, module, context, ty.clone())?;
                context.push(ExpContextEntry {
                    var,
                    ty: ty.clone(),
                });
                let body_ty = self.infer_pts(env, module, context, body);
                context.pop();
                Ok(arena.alloc(ExpNode::Prod {
                    var,
                    ty,
                    body: body_ty?,
                }))
            }
            ExpNode::App { func, arg } => {
                let func_ty = self.infer_pts(env, module, context, func)?;
                let func_ty = self.zonk(env, func_ty);
                let (domain, codomain) =
                    match arena.get(crate::raw::calculus::whnf(env, func_ty.clone())) {
                        ExpNode::Prod { ty, body, .. } => (ty, body),
                        ExpNode::Meta { .. } => {
                            let span = meta_span(env, func_ty.clone(), &self.entries);
                            let domain = self.fresh_synthetic(env, context, span);
                            let codomain = self.fresh_synthetic(env, context, span);
                            let product = arena.alloc(ExpNode::Prod {
                                var: SymbolId::ANONYMOUS,
                                ty: domain.clone(),
                                body: shift_bound_indices(arena, codomain.clone(), 1, 0),
                            });
                            self.unify(env, func_ty, product)?;
                            (domain, shift_bound_indices(arena, codomain, 1, 0))
                        }
                        _ => return Err("application head type is not a product".into()),
                    };
                self.check_pts(env, module, context, arg.clone(), domain)?;
                Ok(crate::raw::calculus::instantiate(arena, codomain, arg))
            }
            ExpNode::PowerSet { set } => {
                let sort = self.infer_sort(env, module, context, set)?;
                match sort {
                    Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
                    _ => Err("PowerSet carrier is not Set(i)".into()),
                }
            }
            ExpNode::SubSet {
                var,
                set,
                predicate,
            } => {
                let sort = self.infer_sort(env, module, context, set.clone())?;
                if !matches!(sort, Sort::Set(_)) {
                    return Err("subset carrier is not Set(i)".into());
                }
                context.push(ExpContextEntry {
                    var,
                    ty: set.clone(),
                });
                let proposition = arena.sort(Sort::Prop);
                let result = self.check_pts(env, module, context, predicate, proposition);
                context.pop();
                result?;
                Ok(arena.alloc(ExpNode::PowerSet { set }))
            }
            ExpNode::Pred {
                superset,
                subset,
                element,
            } => {
                self.infer_sort(env, module, context, superset.clone())?;
                let power = arena.alloc(ExpNode::PowerSet {
                    set: superset.clone(),
                });
                self.check_pts(env, module, context, subset, power)?;
                self.check_pts(env, module, context, element, superset)?;
                Ok(arena.sort(Sort::Prop))
            }
            ExpNode::TypeLift { superset, subset } => {
                let sort = self.infer_sort(env, module, context, superset.clone())?;
                let power = arena.alloc(ExpNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                match sort {
                    Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
                    _ => Err("TypeLift carrier is not Set(i)".into()),
                }
            }
            ExpNode::Equal { left, right } => {
                let left_ty = self.infer_pts(env, module, context, left)?;
                let right_ty = self.infer_pts(env, module, context, right)?;
                let left_ty = self.zonk(env, left_ty);
                let right_ty = self.zonk(env, right_ty);
                if common_ambient_carrier(env, left_ty.clone(), right_ty.clone()).is_none() {
                    self.unify(env, left_ty, right_ty)?;
                }
                Ok(arena.sort(Sort::Prop))
            }
            ExpNode::Exists { set } => {
                self.infer_sort(env, module, context, set)?;
                Ok(arena.sort(Sort::Prop))
            }
            ExpNode::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => {
                self.infer_sort(env, module, context, domain.clone())?;
                self.infer_sort(env, module, context, codomain.clone())?;
                let map_ty = nondependent_product(arena, domain.clone(), codomain.clone());
                self.check_pts(env, module, context, map.clone(), map_ty)?;
                let exists = arena.alloc(ExpNode::Exists {
                    set: domain.clone(),
                });
                self.check_pts(env, module, context, existence, exists)?;
                let shifted_map = shift_bound_indices(arena, map, 2, 0);
                let mapped_left = arena.alloc(ExpNode::App {
                    func: shifted_map.clone(),
                    arg: arena.exp_bound(1),
                });
                let mapped_right = arena.alloc(ExpNode::App {
                    func: shifted_map,
                    arg: arena.exp_bound(0),
                });
                let equality = arena.alloc(ExpNode::Equal {
                    left: mapped_left,
                    right: mapped_right,
                });
                let inner = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: shift_bound_indices(arena, domain.clone(), 1, 0),
                    body: equality,
                });
                let uniqueness_ty = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: domain,
                    body: inner,
                });
                self.check_pts(env, module, context, uniqueness, uniqueness_ty)?;
                Ok(codomain)
            }
            ExpNode::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => {
                self.infer_sort(env, module, context, domain.clone())?;
                self.infer_sort(env, module, context, proposition.clone())?;
                let map_ty = nondependent_product(arena, domain.clone(), proposition.clone());
                self.check_pts(env, module, context, map, map_ty)?;
                let exists = arena.alloc(ExpNode::Exists { set: domain });
                self.check_pts(env, module, context, existence, exists)?;
                Ok(proposition)
            }
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => {
                let sort = self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                Ok(arena.sort(sort))
            }
            ExpNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                self.check_pts(env, module, context, next, state_ty.clone())?;
                Ok(arena.alloc(ExpNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
            ExpNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                self.check_pts(env, module, context, output, result_ty.clone())?;
                Ok(arena.alloc(ExpNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
            ExpNode::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                let step_ty = set_step_function_type(arena, state_ty.clone(), result_ty);
                self.check_pts(env, module, context, step, step_ty)?;
                self.check_pts(env, module, context, state, state_ty)?;
                Ok(arena.sort(Sort::Prop))
            }
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                self.check_pts(
                    env,
                    module,
                    context,
                    step.clone(),
                    set_step_function_type(arena, state_ty.clone(), result_ty.clone()),
                )?;
                self.check_pts(env, module, context, initial.clone(), state_ty.clone())?;
                self.check_pts(
                    env,
                    module,
                    context,
                    accessibility,
                    arena.alloc(ExpNode::Acc {
                        state_ty,
                        result_ty: result_ty.clone(),
                        step,
                        state: initial,
                    }),
                )?;
                Ok(result_ty)
            }
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                self.check_pts(
                    env,
                    module,
                    context,
                    step.clone(),
                    set_step_function_type(arena, state_ty.clone(), result_ty.clone()),
                )?;
                self.check_pts(
                    env,
                    module,
                    context,
                    accessibility,
                    arena.alloc(ExpNode::Acc {
                        state_ty: state_ty.clone(),
                        result_ty: result_ty.clone(),
                        step: step.clone(),
                        state: initial.clone(),
                    }),
                )?;
                self.check_pts(
                    env,
                    module,
                    context,
                    transition_equality,
                    arena.alloc(ExpNode::Equal {
                        left: arena.alloc(ExpNode::App {
                            func: step,
                            arg: initial.clone(),
                        }),
                        right: transition.clone(),
                    }),
                )?;
                self.check_pts(env, module, context, initial, state_ty.clone())?;
                self.check_pts(
                    env,
                    module,
                    context,
                    transition,
                    arena.alloc(ExpNode::RunStep {
                        state_ty,
                        result_ty: result_ty.clone(),
                    }),
                )?;
                Ok(result_ty)
            }
            ExpNode::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                self.infer_recursion_sort(
                    env,
                    module,
                    context,
                    state_ty.clone(),
                    result_ty.clone(),
                )?;
                let run_step = arena.alloc(ExpNode::RunStep {
                    state_ty: state_ty.clone(),
                    result_ty: result_ty.clone(),
                });
                let motive_ty = self.infer_pts(env, module, context, motive.clone())?;
                let ExpNode::Prod {
                    ty: motive_domain,
                    body: motive_body,
                    ..
                } = arena.get(crate::raw::calculus::whnf(env, self.zonk(env, motive_ty)))
                else {
                    return Err("RunStep recursor motive is not a family".into());
                };
                self.unify(env, motive_domain, run_step.clone())?;
                let ExpNode::Sort(motive_sort) =
                    arena.get(crate::raw::calculus::whnf(env, self.zonk(env, motive_body)))
                else {
                    return Err("RunStep recursor motive does not return a sort".into());
                };
                let branch_sort = self
                    .infer_sort(env, module, context, state_ty.clone())?
                    .relation_of_sort(motive_sort)
                    .ok_or("invalid recursor product rule")?;
                let shifted_state = shift_bound_indices(arena, state_ty.clone(), 1, 0);
                let shifted_result = shift_bound_indices(arena, result_ty.clone(), 1, 0);
                let continue_value = arena.alloc(ExpNode::Continue {
                    state_ty: shifted_state.clone(),
                    result_ty: shifted_result.clone(),
                    next: arena.exp_bound(0),
                });
                let continue_result = arena.alloc(ExpNode::App {
                    func: shift_bound_indices(arena, motive.clone(), 1, 0),
                    arg: continue_value,
                });
                let continue_ty = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: state_ty,
                    body: continue_result,
                });
                if self.infer_sort(env, module, context, continue_ty.clone())? != branch_sort {
                    return Err(
                        "RunStep continue branch type must have the branch product sort".into(),
                    );
                }
                self.check_pts(env, module, context, on_continue, continue_ty)?;
                let finish_value = arena.alloc(ExpNode::Finish {
                    state_ty: shifted_state,
                    result_ty: shifted_result,
                    output: arena.exp_bound(0),
                });
                let finish_result = arena.alloc(ExpNode::App {
                    func: shift_bound_indices(arena, motive.clone(), 1, 0),
                    arg: finish_value,
                });
                let finish_ty = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: result_ty,
                    body: finish_result,
                });
                if self.infer_sort(env, module, context, finish_ty.clone())? != branch_sort {
                    return Err(
                        "RunStep finish branch type must have the branch product sort".into(),
                    );
                }
                self.check_pts(env, module, context, on_finish, finish_ty)?;
                self.check_pts(env, module, context, scrutinee.clone(), run_step)?;
                Ok(arena.alloc(ExpNode::App {
                    func: motive,
                    arg: scrutinee,
                }))
            }
            ExpNode::BoxType { program_ty } => {
                let mut empty = Vec::new();
                let mut session = ProgramCheckSession::new(env, &mut empty);
                session
                    .check_computation_type(program_ty)
                    .map_err(|error| format!("ill-formed boxed Program type: {error:?}"))?;
                Ok(arena.sort(Sort::Set(0)))
            }
            ExpNode::BoxProgram {
                program_ty,
                program,
            } => {
                let mut empty = Vec::new();
                let mut session = ProgramCheckSession::new(env, &mut empty);
                session
                    .check_computation_term(program.clone(), program_ty.clone())
                    .map_err(|error| format!("ill-typed boxed Program: {error:?}"))?;
                let reflected_ty =
                    crate::raw::reflection::reflect_computation_type(env, program_ty.clone())
                        .map_err(|error| format!("cannot reflect boxed Program type: {error}"))?;
                let reflected = crate::raw::reflection::reflect_computation(env, program)
                    .map_err(|error| format!("cannot reflect boxed Program: {error}"))?;
                self.check_pts(env, module, context, reflected, reflected_ty)?;
                Ok(arena.alloc(ExpNode::BoxType { program_ty }))
            }
            ExpNode::ForceBox { program_ty, boxed } => {
                self.check_pts(
                    env,
                    module,
                    context,
                    boxed,
                    arena.alloc(ExpNode::BoxType {
                        program_ty: program_ty.clone(),
                    }),
                )?;
                crate::raw::reflection::reflect_computation_type(env, program_ty)
                    .map_err(|error| format!("cannot reflect boxed Program type: {error}"))
            }
            ExpNode::BoxApp { function, argument } => {
                let function_ty = self.infer_pts(env, module, context, function)?;
                let function_ty = self.zonk(env, function_ty);
                let ExpNode::BoxType { program_ty } = arena.get(function_ty) else {
                    return Err("boxed application head is not Box(P)".into());
                };
                let ComputationTypeNode::Function { domain, codomain } = arena.get(program_ty)
                else {
                    return Err("boxed application head is not a computation function".into());
                };
                self.check_pts(
                    env,
                    module,
                    context,
                    argument,
                    arena.alloc(ExpNode::BoxType {
                        program_ty: arena.alloc(ComputationTypeNode::Return { value_ty: domain }),
                    }),
                )?;
                Ok(arena.alloc(ExpNode::BoxType {
                    program_ty: codomain,
                }))
            }
            ExpNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                self.infer_sort(env, module, context, superset.clone())?;
                let power = arena.alloc(ExpNode::PowerSet {
                    set: superset.clone(),
                });
                self.check_pts(env, module, context, subset.clone(), power)?;
                self.check_pts(env, module, context, element.clone(), superset.clone())?;
                let membership = arena.alloc(ExpNode::Pred {
                    superset: superset.clone(),
                    subset: subset.clone(),
                    element,
                });
                self.check_pts(env, module, context, proof, membership)?;
                Ok(arena.alloc(ExpNode::TypeLift { superset, subset }))
            }
            ExpNode::Prove(Prove::ExistsIntro { element, set }) => {
                self.check_pts(env, module, context, element, set.clone())?;
                self.infer_sort(env, module, context, set.clone())?;
                Ok(arena.alloc(ExpNode::Exists { set }))
            }
            ExpNode::Prove(Prove::SubsetElim {
                element,
                subset,
                superset,
            }) => {
                let lifted = arena.alloc(ExpNode::TypeLift {
                    superset: superset.clone(),
                    subset: subset.clone(),
                });
                self.check_pts(env, module, context, element.clone(), lifted)?;
                Ok(arena.alloc(ExpNode::Pred {
                    superset,
                    subset,
                    element,
                }))
            }
            ExpNode::Prove(Prove::IdRefl { element }) => {
                let ty = self.infer_pts(env, module, context, element.clone())?;
                self.infer_sort(env, module, context, ty)?;
                Ok(arena.alloc(ExpNode::Equal {
                    left: element.clone(),
                    right: element,
                }))
            }
            ExpNode::Prove(Prove::IdElim {
                left,
                right,
                ty,
                var,
                predicate,
                base,
                equality,
            }) => {
                self.infer_sort(env, module, context, ty.clone())?;
                self.check_pts(env, module, context, left.clone(), ty.clone())?;
                self.check_pts(env, module, context, right.clone(), ty.clone())?;
                context.push(ExpContextEntry {
                    var,
                    ty: ty.clone(),
                });
                let proposition = arena.sort(Sort::Prop);
                let predicate_result =
                    self.check_pts(env, module, context, predicate.clone(), proposition);
                context.pop();
                predicate_result?;
                let predicate_function = arena.alloc(ExpNode::Lam {
                    var,
                    ty,
                    body: predicate,
                });
                let base_ty = arena.alloc(ExpNode::App {
                    func: predicate_function.clone(),
                    arg: left.clone(),
                });
                self.check_pts(env, module, context, base, base_ty)?;
                let equality_ty = arena.alloc(ExpNode::Equal {
                    left,
                    right: right.clone(),
                });
                self.check_pts(env, module, context, equality, equality_ty)?;
                Ok(arena.alloc(ExpNode::App {
                    func: predicate_function,
                    arg: right,
                }))
            }
            ExpNode::Prove(Prove::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            }) => {
                let take = arena.alloc(ExpNode::TakeSet {
                    domain: domain.clone(),
                    codomain: codomain.clone(),
                    map: func.clone(),
                    existence,
                    uniqueness,
                });
                self.check_pts(env, module, context, take.clone(), codomain)?;
                self.check_pts(env, module, context, element.clone(), domain)?;
                let mapped = arena.alloc(ExpNode::App { func, arg: element });
                Ok(arena.alloc(ExpNode::Equal {
                    left: take,
                    right: mapped,
                }))
            }
            _ => Err("metavariable inference for this expression is blocked".into()),
        }
    }

    fn infer_recursion_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        state_ty: Exp,
        result_ty: Exp,
    ) -> Result<Sort, String> {
        let state_sort = self.infer_sort(env, module, context, state_ty.clone())?;
        let result_sort = self.infer_sort(env, module, context, result_ty.clone())?;
        if !matches!(state_sort, Sort::Set(_)) || !matches!(result_sort, Sort::Set(_)) {
            return Err("Set recursion state and result types must inhabit Set(i)".into());
        }
        // infer_sort uses Set(0) provisionally for unresolved types. Defer
        // equality until arguments solve the holes and the strict kernel
        // checks the zonked term; a known side supplies the shared sort.
        if self.contains_unsolved(env, state_ty) {
            return Ok(result_sort);
        }
        if self.contains_unsolved(env, result_ty) {
            return Ok(state_sort);
        }
        if state_sort != result_sort {
            return Err("Set recursion state and result types must inhabit the same Set(i)".into());
        }
        Ok(state_sort)
    }

    pub(crate) fn infer_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
    ) -> Result<Sort, String> {
        let term = self.zonk(env, term);
        if !self.contains_unsolved(env, term.clone()) {
            return CheckSession::new(env, module, context)
                .infer_sort(term)
                .map_err(|error| format!("{error:?}"));
        }
        if matches!(env.arena().get(term.clone()), ExpNode::Meta { .. }) {
            let constraint = GoalConstraint::IsSort { term: term.clone() };
            self.set_principal_for_meta(env, term, &constraint);
            self.constrain(constraint);
            return Ok(Sort::Set(0));
        }
        let ty = self.infer_pts(env, module, context, term.clone())?;
        match env.arena().get(self.zonk(env, ty)) {
            ExpNode::Sort(sort) => Ok(sort),
            ExpNode::Meta { .. } => {
                self.constrain(GoalConstraint::IsSort { term });
                Ok(Sort::Set(0))
            }
            _ => Err("expression does not have a sort".into()),
        }
    }

    pub(crate) fn unify(&mut self, env: &CrateEnv, left: Exp, right: Exp) -> Result<bool, String> {
        let index = self.constraints.len();
        self.constrain(GoalConstraint::Equal {
            left: left.clone(),
            right: right.clone(),
        });
        let result = self.unify_rec(env, left.clone(), right.clone(), &mut HashSet::new());
        let normalized_left = self.zonk(env, left);
        let normalized_right = self.zonk(env, right);
        self.constraints[index].normalized = GoalConstraint::Equal {
            left: normalized_left,
            right: normalized_right,
        };
        match &result {
            Ok(true) => self.constraints[index].status = ConstraintStatus::Discharged,
            Ok(false) => self.constraints[index].status = ConstraintStatus::Residual,
            Err(_) => self.constraints[index].status = ConstraintStatus::Failed,
        }
        result
    }

    fn unify_rec(
        &mut self,
        env: &CrateEnv,
        left: Exp,
        right: Exp,
        visiting: &mut HashSet<(Exp, Exp)>,
    ) -> Result<bool, String> {
        let left = self.zonk(env, left);
        let right = self.zonk(env, right);
        if left == right || erased_convertible(env, left.clone(), right.clone()) {
            return Ok(true);
        }
        // Expand local definitions before rigid comparison. Keep named heads
        // so structural matching can still infer their implicit arguments.
        let left = beta_head(env.arena(), left);
        let right = beta_head(env.arena(), right);
        if !visiting.insert((left.clone(), right.clone())) {
            return Ok(true);
        }
        match (
            env.arena().get(left.clone()),
            env.arena().get(right.clone()),
        ) {
            (
                ExpNode::Meta {
                    metavariable,
                    spine: _,
                },
                ExpNode::Meta {
                    metavariable: other,
                    ..
                },
            ) if metavariable == other => Ok(true),
            (
                ExpNode::Meta {
                    metavariable,
                    spine,
                },
                _,
            ) => self.assign(env, metavariable, spine.len(), right),
            (
                _,
                ExpNode::Meta {
                    metavariable,
                    spine,
                },
            ) => self.assign(env, metavariable, spine.len(), left),
            (left_node, right_node) => {
                if !rigid_heads_compatible(&left_node, &right_node) {
                    return Err("incompatible rigid expressions in metavariable constraint".into());
                }
                let left_children = node_children(left_node);
                let right_children = node_children(right_node);
                if left_children.len() != right_children.len() {
                    return Err("different expression arities in metavariable constraint".into());
                }
                let mut solved = true;
                for (left, right) in left_children.into_iter().zip(right_children) {
                    solved &= self.unify_rec(env, left, right, visiting)?;
                }
                Ok(solved)
            }
        }
    }

    fn assign(
        &mut self,
        env: &CrateEnv,
        metavariable: MetaVarId,
        occurrence_scope: usize,
        value: Exp,
    ) -> Result<bool, String> {
        if self.occurs(env, metavariable, value.clone(), &mut HashSet::new()) {
            return Err(format!("occurs check failed for ?m{}", metavariable.0));
        }
        let entry = &self.entries[metavariable.index()];
        let value = if occurrence_scope >= entry.scope_len {
            remove_unused_ambient_binders(env.arena(), value, occurrence_scope - entry.scope_len)
                .ok_or_else(|| {
                    format!(
                        "solution for ?m{} captures a variable outside its shared context",
                        metavariable.0
                    )
                })?
        } else {
            shift_bound_indices(env.arena(), value, entry.scope_len - occurrence_scope, 0)
        };
        if let Some(previous) = entry.assignment.clone() {
            return self.unify_rec(env, previous, value, &mut HashSet::new());
        }
        self.entries[metavariable.index()].assignment = Some(value);
        Ok(true)
    }

    fn occurs(&self, env: &CrateEnv, needle: MetaVarId, exp: Exp, seen: &mut HashSet<Exp>) -> bool {
        if !seen.insert(exp.clone()) {
            return false;
        }
        match env.arena().get(exp) {
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                metavariable == needle
                    || self.entries[metavariable.index()]
                        .assignment
                        .clone()
                        .is_some_and(|value| self.occurs(env, needle, value, seen))
                    || spine
                        .into_iter()
                        .any(|child| self.occurs(env, needle, child, seen))
            }
            node => node_children(node)
                .into_iter()
                .any(|child| self.occurs(env, needle, child, seen)),
        }
    }

    pub(crate) fn zonk(&self, env: &CrateEnv, exp: Exp) -> Exp {
        self.zonk_rec(env, exp, &mut HashMap::new(), &mut HashSet::new())
    }

    fn zonk_rec(
        &self,
        env: &CrateEnv,
        exp: Exp,
        cache: &mut HashMap<Exp, Exp>,
        resolving: &mut HashSet<MetaVarId>,
    ) -> Exp {
        if let Some(result) = cache.get(&exp) {
            return result.clone();
        }
        let arena = env.arena();
        let result = match arena.get(exp.clone()) {
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                let entry = &self.entries[metavariable.index()];
                if let Some(assignment) = entry.assignment.clone() {
                    if !resolving.insert(metavariable) {
                        exp.clone()
                    } else {
                        let Some(arguments) = spine.get(..entry.scope_len) else {
                            resolving.remove(&metavariable);
                            return exp;
                        };
                        let rebased = instantiate_telescope(arena, assignment, arguments);
                        let result = self.zonk_rec(env, rebased, cache, resolving);
                        resolving.remove(&metavariable);
                        result
                    }
                } else {
                    exp.clone()
                }
            }
            node => {
                let original = node.clone();
                let mapped =
                    map_children(node, |child| self.zonk_rec(env, child, cache, resolving));
                if original == mapped {
                    exp.clone()
                } else {
                    arena.alloc(mapped)
                }
            }
        };
        cache.insert(exp, result.clone());
        result
    }

    pub(crate) fn contains_unsolved(&self, env: &CrateEnv, exp: Exp) -> bool {
        fn visit(env: &CrateEnv, exp: Exp, seen: &mut HashSet<Exp>) -> bool {
            if !seen.insert(exp.clone()) {
                return false;
            }
            match env.arena().get(exp) {
                ExpNode::Meta { .. } => true,
                node => node_children(node)
                    .into_iter()
                    .any(|child| visit(env, child, seen)),
            }
        }

        let exp = self.zonk(env, exp);
        visit(env, exp, &mut HashSet::new())
    }

    pub(crate) fn finish(&self, env: &CrateEnv) -> Result<(), ElaborationError> {
        let mut implicits = Vec::new();
        let mut goals = Vec::new();
        for (index, entry) in self.entries.iter().enumerate() {
            let id = MetaVarId(index as u32);
            let solved = entry
                .assignment
                .clone()
                .is_some_and(|assignment| !self.contains_unsolved(env, assignment));
            if solved {
                continue;
            }
            let goal = self.goal_for(env, id);
            match entry.flavor {
                MetaFlavor::Implicit => implicits.push(goal),
                MetaFlavor::Goal | MetaFlavor::Named(_) => goals.push(goal),
                MetaFlavor::Synthetic => {}
            }
        }
        if !implicits.is_empty() {
            Err(ElaborationError::AmbiguousImplicit(implicits))
        } else if !goals.is_empty() {
            Err(ElaborationError::UnsolvedGoals(goals))
        } else {
            Ok(())
        }
    }

    fn goal_for(&self, env: &CrateEnv, id: MetaVarId) -> MetaGoal {
        let mut related = HashSet::from([id]);
        loop {
            let before = related.len();
            for record in &self.constraints {
                let metas = metas_in_constraint(env, &record.original);
                if metas.iter().any(|meta| related.contains(meta)) {
                    related.extend(metas);
                }
            }
            if related.len() == before {
                break;
            }
        }
        let constraints = self
            .constraints
            .iter()
            .filter(|record| {
                metas_in_constraint(env, &record.original)
                    .iter()
                    .any(|meta| related.contains(meta))
            })
            .map(|record| {
                let mut record = record.clone();
                record.normalized = self.zonk_constraint(env, &record.normalized);
                record
            })
            .collect();
        let entry = &self.entries[id.index()];
        let mut dependencies = related
            .into_iter()
            .filter(|meta| *meta != id)
            .collect::<Vec<_>>();
        dependencies.sort_by_key(|meta| meta.0);
        MetaGoal {
            metavariable: id,
            flavor: entry.flavor,
            span: entry.span,
            context: entry.context.clone(),
            principal: entry
                .principal
                .as_ref()
                .map(|constraint| self.zonk_constraint(env, constraint)),
            constraints,
            dependencies,
        }
    }

    fn zonk_constraint(&self, env: &CrateEnv, constraint: &GoalConstraint) -> GoalConstraint {
        match constraint {
            GoalConstraint::HasType { term, expected } => GoalConstraint::HasType {
                term: self.zonk(env, term.clone()),
                expected: self.zonk(env, expected.clone()),
            },
            GoalConstraint::Equal { left, right } => GoalConstraint::Equal {
                left: self.zonk(env, left.clone()),
                right: self.zonk(env, right.clone()),
            },
            GoalConstraint::IsSort { term } => GoalConstraint::IsSort {
                term: self.zonk(env, term.clone()),
            },
        }
    }
}

fn constraint_expressions(constraint: &GoalConstraint) -> Vec<Exp> {
    match constraint {
        GoalConstraint::HasType { term, expected }
        | GoalConstraint::Equal {
            left: term,
            right: expected,
        } => vec![term.clone(), expected.clone()],
        GoalConstraint::IsSort { term } => vec![term.clone()],
    }
}

fn meta_span(env: &CrateEnv, exp: Exp, entries: &[MetaEntry]) -> SourceSpan {
    match env.arena().get(exp) {
        ExpNode::Meta { metavariable, .. } => entries[metavariable.index()].span,
        _ => SourceSpan { start: 0, end: 0 },
    }
}

fn metas_in_constraint(env: &CrateEnv, constraint: &GoalConstraint) -> HashSet<MetaVarId> {
    constraint_expressions(constraint)
        .into_iter()
        .flat_map(|exp| metas_in_exp(env, exp))
        .collect()
}

fn metas_in_exp(env: &CrateEnv, exp: Exp) -> HashSet<MetaVarId> {
    fn collect(env: &CrateEnv, exp: Exp, result: &mut HashSet<MetaVarId>, seen: &mut HashSet<Exp>) {
        if !seen.insert(exp.clone()) {
            return;
        }
        match env.arena().get(exp) {
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                result.insert(metavariable);
                for child in spine {
                    collect(env, child, result, seen);
                }
            }
            node => {
                for child in node_children(node) {
                    collect(env, child, result, seen);
                }
            }
        }
    }
    let mut result = HashSet::new();
    collect(env, exp, &mut result, &mut HashSet::new());
    result
}

fn beta_head(arena: &crate::raw::exp::Arena, exp: Exp) -> Exp {
    let ExpNode::App { func, arg } = arena.get(exp.clone()) else {
        return exp;
    };
    let head = beta_head(arena, func);
    if let ExpNode::Lam { body, .. } = arena.get(head.clone()) {
        let body = match arena.get(body.clone()) {
            ExpNode::Bound(0) => arg,
            _ => crate::raw::calculus::instantiate(arena, body, arg),
        };
        beta_head(arena, body)
    } else {
        arena.reuse_exp(exp, ExpNode::App { func: head, arg })
    }
}

fn node_children(node: ExpNode) -> Vec<Exp> {
    let mut children = Vec::new();
    let _ = map_children(node, |child| {
        children.push(child.clone());
        child
    });
    children
}

fn rigid_heads_compatible(left: &ExpNode, right: &ExpNode) -> bool {
    use std::mem::discriminant;
    if discriminant(left) != discriminant(right) {
        return false;
    }
    match (left, right) {
        (ExpNode::Sort(left), ExpNode::Sort(right)) => left == right,
        (ExpNode::Bound(left), ExpNode::Bound(right)) => left == right,
        (ExpNode::ModuleParam(left), ExpNode::ModuleParam(right)) => left == right,
        (ExpNode::DefinedConstant(left), ExpNode::DefinedConstant(right)) => left == right,
        (ExpNode::IndType { indspec: left, .. }, ExpNode::IndType { indspec: right, .. })
        | (ExpNode::IndElim { indspec: left, .. }, ExpNode::IndElim { indspec: right, .. })
        | (ExpNode::IndCase { indspec: left, .. }, ExpNode::IndCase { indspec: right, .. }) => {
            left == right
        }
        (
            ExpNode::IndCtor {
                indspec: left,
                idx: left_idx,
                ..
            },
            ExpNode::IndCtor {
                indspec: right,
                idx: right_idx,
                ..
            },
        ) => left == right && left_idx == right_idx,
        _ => true,
    }
}

fn nondependent_product(arena: &crate::raw::exp::Arena, domain: Exp, codomain: Exp) -> Exp {
    arena.alloc(ExpNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    })
}

fn set_step_function_type(arena: &crate::raw::exp::Arena, state_ty: Exp, result_ty: Exp) -> Exp {
    let run_step = arena.alloc(ExpNode::RunStep {
        state_ty: state_ty.clone(),
        result_ty,
    });
    nondependent_product(arena, state_ty, run_step)
}
