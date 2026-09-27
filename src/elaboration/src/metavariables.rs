//! Elaboration-time contextual metavariables and their diagnostics.

use crate::hir::{SourceSpan, SurfaceMeta};
use crate::raw::{
    calculus::{
        base_carrier, can_weaken_to, common_ambient_carrier, erased_convertible, instantiate,
        instantiate_telescope, map_children, remove_unused_ambient_binders, shift_bound_indices,
        type_head_normal,
    },
    derivation::CheckSession,
    environment::{CrateEnv, DefinedConstant, ModuleParameterKind},
    exp::{Exp, ExpContext, ExpContextEntry, ExpNode, Prove},
    ids::{InductiveId, MetaVarId, ModuleId, SymbolId},
    inductive::{InductiveTypeSpecs, case_type},
    program::ComputationTypeNode,
    program_derivation::ProgramCheckSession,
    sort::Sort,
    utils::{assoc_apply, assoc_prod, decompose_app, decompose_prod},
};
use std::collections::{HashMap, HashSet};

mod diagnostics;
#[cfg(test)]
mod tests;
pub use diagnostics::{
    ConstraintDiagnostic, ConstraintRecord, ConstraintStatus, ElaborationError, GoalConstraint,
    MetaFlavor, MetaGoal, MetaState, format_constraint, format_elaboration_error,
};

#[derive(Debug, Clone)]
struct MetaEntry {
    flavor: MetaFlavor,
    span: SourceSpan,
    occurrences: Vec<SourceSpan>,
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
    failure: Option<MetaState>,
    origins: Vec<SourceSpan>,
    sources: HashMap<Exp, Vec<SourceSpan>>,
}

impl MetaStore {
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.named.clear();
        self.constraints.clear();
        self.failure = None;
        self.origins.clear();
        self.sources.clear();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn constraint_error(&self, env: &CrateEnv, message: String) -> ElaborationError {
        let state = self.failure.unwrap_or(MetaState::Contradiction);
        let mut goals = self.goals(env);
        for goal in &mut goals {
            if goal.state != MetaState::Solved {
                goal.state = state;
            }
        }
        ElaborationError::ConstraintFailure {
            message,
            constraints: self
                .constraints
                .iter()
                .map(|record| self.constraint_diagnostic(env, record))
                .collect(),
            goals,
        }
    }

    pub(crate) fn record_source(&mut self, env: &CrateEnv, term: Exp, span: SourceSpan) {
        for id in metas_in_exp(env, term) {
            let entry = &mut self.entries[id.index()];
            if entry.span == SourceSpan::default() {
                entry.span = span;
                entry.occurrences = vec![span];
            }
        }
        self.sources.entry(term).or_default().push(span);
    }

    pub(crate) fn fresh(
        &mut self,
        env: &CrateEnv,
        kind: SurfaceMeta,
        span: SourceSpan,
        context: &ExpContext,
        scope_len: usize,
    ) -> Result<Exp, String> {
        let flavor = MetaFlavor::from(kind);
        let existing = match flavor {
            MetaFlavor::Named(number) => self.named.get(&number).copied(),
            MetaFlavor::Implicit | MetaFlavor::Goal | MetaFlavor::Synthetic => None,
        };
        let metavariable = existing.unwrap_or_else(|| {
            let id = MetaVarId(
                u32::try_from(self.entries.len()).expect("metavariable table exceeded u32::MAX"),
            );
            self.entries.push(MetaEntry {
                flavor,
                span,
                occurrences: vec![span],
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
            entry.occurrences.push(span);
            let previous_start = entry.context.len().saturating_sub(entry.scope_len);
            let current_start = context.len().saturating_sub(scope_len);
            let common = entry.context[previous_start..]
                .iter()
                .zip(&context[current_start..])
                .take_while(|(left, right)| left.var == right.var)
                .count();
            if common < entry.scope_len {
                let removed = entry.scope_len - common;
                let strengthen = |term| {
                    remove_unused_ambient_binders(env.arena(), term, removed).ok_or_else(|| {
                        format!(
                            "{} captures a variable outside its shared context",
                            entry.flavor.display_name(metavariable)
                        )
                    })
                };
                entry.assignment = entry.assignment.map(strengthen).transpose()?;
                entry.inferred_type = entry.inferred_type.map(strengthen).transpose()?;
                entry.scope_len = common;
                entry.context = context[..current_start + common].to_vec();
            }
        }

        let spine = (0..scope_len)
            .rev()
            .map(|index| env.arena().exp_bound(index))
            .collect();
        Ok(env.arena().alloc(ExpNode::Meta {
            metavariable,
            spine,
        }))
    }

    pub(crate) fn constrain(&mut self, env: &CrateEnv, constraint: GoalConstraint) {
        let mut origins = self.origins.clone();
        for meta in metas_in_constraint(env, &constraint) {
            origins.extend(self.entries[meta.index()].occurrences.iter().copied());
        }
        origins.sort_by_key(|span| (span.start, span.end));
        origins.dedup();
        self.constraints.push(ConstraintRecord {
            origins,
            original: constraint,
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
        self.fresh_synthetic_in_scope(env, context, context.len(), span)
    }

    fn fresh_synthetic_in_scope(
        &mut self,
        env: &CrateEnv,
        context: &ExpContext,
        scope_len: usize,
        span: SourceSpan,
    ) -> Exp {
        let id = MetaVarId(
            u32::try_from(self.entries.len()).expect("metavariable table exceeded u32::MAX"),
        );
        self.entries.push(MetaEntry {
            flavor: MetaFlavor::Synthetic,
            span,
            occurrences: vec![span],
            context: context.clone(),
            scope_len,
            assignment: None,
            principal: None,
            inferred_type: None,
        });
        let spine = (0..scope_len)
            .rev()
            .map(|index| env.arena().exp_bound(index))
            .collect();
        env.arena().alloc(ExpNode::Meta {
            metavariable: id,
            spine,
        })
    }

    fn set_meta_type(&mut self, env: &CrateEnv, term: Exp, expected: Exp) -> Result<(), String> {
        let ExpNode::Meta {
            metavariable,
            spine,
        } = env.arena().get(self.zonk(env, term))
        else {
            return Ok(());
        };
        let constraint = GoalConstraint::HasType { term, expected };
        if self.entries[metavariable.index()].principal.is_none() {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
        self.constrain(env, constraint);
        let entry = &self.entries[metavariable.index()];
        let expected = remove_unused_ambient_binders(
            env.arena(),
            expected,
            spine.len().saturating_sub(entry.scope_len),
        )
        .ok_or("metavariable type captures a variable outside its shared context")?;
        if let Some(previous) = self.entries[metavariable.index()].inferred_type {
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
        let ExpNode::Meta {
            metavariable,
            spine,
        } = env.arena().get(self.zonk(env, term))
        else {
            return Err("expected metavariable".into());
        };
        if let Some(ty) = self.entries[metavariable.index()].inferred_type {
            let scope = self.entries[metavariable.index()].scope_len;
            return Ok(self.zonk(env, instantiate_telescope(env.arena(), ty, &spine[..scope])));
        }
        let span = self.entries[metavariable.index()].span;
        let ty = self.fresh_synthetic(env, context, span);
        self.entries[metavariable.index()].inferred_type = Some(ty);
        let constraint = GoalConstraint::HasType { term, expected: ty };
        self.entries[metavariable.index()].principal = Some(constraint.clone());
        self.constrain(env, constraint);
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
        let previous = self.origins.clone();
        for exp in [term, expected] {
            self.origins
                .extend(self.sources.get(&exp).into_iter().flatten().copied());
            if let ExpNode::Meta { metavariable, .. } = env.arena().get(exp) {
                self.origins.extend(
                    self.entries[metavariable.index()]
                        .occurrences
                        .iter()
                        .copied(),
                );
            }
        }
        let result = self.check_pts_inner(env, module, context, term, expected);
        self.origins = previous;
        result
    }

    fn check_pts_inner(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
        expected: Exp,
    ) -> Result<(), String> {
        let term = self.zonk(env, term);
        let expected = self.zonk(env, expected);
        if matches!(env.arena().get(term), ExpNode::Meta { .. }) {
            return self.set_meta_type(env, term, expected);
        }
        if matches!(env.arena().get(expected), ExpNode::Meta { .. }) {
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
        ) = (env.arena().get(term), env.arena().get(expected))
        {
            self.unify(env, ty, expected_ty)?;
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
        if can_weaken_to(env, inferred, expected) {
            return Ok(());
        }
        if let (ExpNode::Sort(inferred), ExpNode::Sort(expected)) =
            (env.arena().get(inferred), env.arena().get(expected))
            && inferred.can_lift_to(expected)
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
        let previous = self.origins.clone();
        self.origins
            .extend(self.sources.get(&term).into_iter().flatten().copied());
        if let ExpNode::Meta { metavariable, .. } = env.arena().get(term) {
            self.origins.extend(
                self.entries[metavariable.index()]
                    .occurrences
                    .iter()
                    .copied(),
            );
        }
        let result = self.infer_pts_inner(env, module, context, term);
        self.origins = previous;
        result
    }

    fn infer_pts_inner(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
    ) -> Result<Exp, String> {
        let term = self.zonk(env, term);
        if !self.contains_unsolved(env, term) {
            return CheckSession::new(env, context)
                .infer_pts(term)
                .map_err(|error| format!("{error:?}"));
        }
        let arena = env.arena();
        match arena.get(term) {
            ExpNode::Meta { .. } => self.type_of_meta(env, term, context),
            ExpNode::Sort(sort) => sort
                .type_of_sort()
                .map(|sort| arena.sort(sort))
                .ok_or_else(|| "no sort of sort found".into()),
            ExpNode::Bound(index) => context
                .len()
                .checked_sub(index + 1)
                .and_then(|position| context.get(position))
                .map(|entry| shift_bound_indices(arena, entry.ty, index + 1, 0))
                .ok_or_else(|| "bound variable is not a PTS term".into()),
            ExpNode::ModuleParam(parameter) => env
                .module_parameter_opt(parameter)
                .and_then(|parameter| match parameter.kind {
                    ModuleParameterKind::Pts { ty } => Some(ty),
                    _ => None,
                })
                .ok_or_else(|| "module parameter is not a PTS term".into()),
            ExpNode::DefinedConstant(definition) => {
                let definition = env.definition(definition);
                match definition {
                    DefinedConstant::Pts { ty, .. } => Ok(*ty),
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
                for (argument, (_, expected)) in parameters.iter().copied().zip(spec.parameters()) {
                    let expected =
                        crate::raw::calculus::instantiate_telescope(arena, *expected, &preceding);
                    self.check_pts(env, module, context, argument, expected)?;
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
                for (argument, (_, expected)) in parameters.iter().copied().zip(spec.parameters()) {
                    let expected =
                        crate::raw::calculus::instantiate_telescope(arena, *expected, &preceding);
                    self.check_pts(env, module, context, argument, expected)?;
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
            ExpNode::IndCase {
                indspec,
                scrutinee,
                return_type,
                branches,
            } => {
                let scrutinee_ty = self.infer_pts(env, module, context, scrutinee)?;
                let (parameters, indices) = self.inductive_arguments(env, indspec, scrutinee_ty)?;
                let spec = env.inductive(indspec);
                let return_kind = self.infer_motive_kind(env, module, context, return_type)?;
                let (_, result) =
                    decompose_prod(arena, type_head_normal(env, self.zonk(env, return_kind)));
                let ExpNode::Sort(sort) = arena.get(result) else {
                    return Err("match return kind does not end in sort".into());
                };
                if spec.sort().relation_of_sort_indelim(sort).is_none()
                    && !spec.supports_singleton_elimination()
                {
                    return Err("cannot form eliminator".into());
                }
                let expected_kind =
                    InductiveTypeSpecs::return_type_kind(arena, indspec, spec, &parameters, sort);
                self.unify(env, return_kind, expected_kind)?;
                if branches.len() != spec.constructor_len() {
                    return Err("match constructor length mismatch".into());
                }
                let this = arena.alloc(ExpNode::IndType {
                    indspec,
                    parameters: parameters.clone(),
                });
                for (index, branch) in branches.into_iter().enumerate() {
                    let constructor =
                        spec.constructors()[index].instantiate_parameters(arena, &parameters);
                    let constructor_term = arena.alloc(ExpNode::IndCtor {
                        indspec,
                        parameters: parameters.clone(),
                        idx: index,
                    });
                    let expected =
                        case_type(arena, &constructor, return_type, constructor_term, this);
                    self.check_pts(env, module, context, branch, expected)?;
                }
                let motive = assoc_apply(arena, return_type, indices);
                let result = arena.alloc(ExpNode::App {
                    func: motive,
                    arg: scrutinee,
                });
                Ok(type_head_normal(env, self.zonk(env, result)))
            }
            ExpNode::Prod { var, ty, body } => {
                let domain_sort = self.infer_sort(env, module, context, ty)?;
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
                self.infer_sort(env, module, context, ty)?;
                context.push(ExpContextEntry { var, ty });
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
                let (domain, codomain) = match arena.get(crate::raw::calculus::whnf(env, func_ty)) {
                    ExpNode::Prod { ty, body, .. } => (ty, body),
                    ExpNode::Meta { .. } => {
                        let span = meta_span(env, func_ty, &self.entries);
                        let domain = self.fresh_synthetic(env, context, span);
                        let codomain = self.fresh_synthetic(env, context, span);
                        let product = arena.alloc(ExpNode::Prod {
                            var: SymbolId::ANONYMOUS,
                            ty: domain,
                            body: shift_bound_indices(arena, codomain, 1, 0),
                        });
                        self.unify(env, func_ty, product)?;
                        (domain, shift_bound_indices(arena, codomain, 1, 0))
                    }
                    _ => return Err("application head type is not a product".into()),
                };
                self.check_pts(env, module, context, arg, domain)?;
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
                let sort = self.infer_sort(env, module, context, set)?;
                if !matches!(sort, Sort::Set(_)) {
                    return Err("subset carrier is not Set(i)".into());
                }
                context.push(ExpContextEntry { var, ty: set });
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
                self.infer_sort(env, module, context, superset)?;
                let power = arena.alloc(ExpNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                self.check_pts(env, module, context, element, superset)?;
                Ok(arena.sort(Sort::Prop))
            }
            ExpNode::TypeLift { superset, subset } => {
                let sort = self.infer_sort(env, module, context, superset)?;
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
                if common_ambient_carrier(env, left_ty, right_ty).is_none() {
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
                self.infer_sort(env, module, context, domain)?;
                self.infer_sort(env, module, context, codomain)?;
                let map_ty = nondependent_product(arena, domain, codomain);
                self.check_pts(env, module, context, map, map_ty)?;
                let exists = arena.alloc(ExpNode::Exists { set: domain });
                self.check_pts(env, module, context, existence, exists)?;
                let shifted_map = shift_bound_indices(arena, map, 2, 0);
                let mapped_left = arena.alloc(ExpNode::App {
                    func: shifted_map,
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
                    ty: shift_bound_indices(arena, domain, 1, 0),
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
                self.infer_sort(env, module, context, domain)?;
                self.infer_sort(env, module, context, proposition)?;
                let map_ty = nondependent_product(arena, domain, proposition);
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                self.check_pts(env, module, context, next, state_ty)?;
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                self.check_pts(env, module, context, output, result_ty)?;
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                let step_ty = set_step_function_type(arena, state_ty, result_ty);
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                self.check_pts(
                    env,
                    module,
                    context,
                    step,
                    set_step_function_type(arena, state_ty, result_ty),
                )?;
                self.check_pts(env, module, context, initial, state_ty)?;
                self.check_pts(
                    env,
                    module,
                    context,
                    accessibility,
                    arena.alloc(ExpNode::Acc {
                        state_ty,
                        result_ty,
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                self.check_pts(
                    env,
                    module,
                    context,
                    step,
                    set_step_function_type(arena, state_ty, result_ty),
                )?;
                self.check_pts(
                    env,
                    module,
                    context,
                    accessibility,
                    arena.alloc(ExpNode::Acc {
                        state_ty,
                        result_ty,
                        step,
                        state: initial,
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
                            arg: initial,
                        }),
                        right: transition,
                    }),
                )?;
                self.check_pts(env, module, context, initial, state_ty)?;
                self.check_pts(
                    env,
                    module,
                    context,
                    transition,
                    arena.alloc(ExpNode::RunStep {
                        state_ty,
                        result_ty,
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
                self.infer_recursion_sort(env, module, context, state_ty, result_ty)?;
                let run_step = arena.alloc(ExpNode::RunStep {
                    state_ty,
                    result_ty,
                });
                let motive_ty = self.infer_pts(env, module, context, motive)?;
                let ExpNode::Prod {
                    ty: motive_domain,
                    body: motive_body,
                    ..
                } = arena.get(crate::raw::calculus::whnf(env, self.zonk(env, motive_ty)))
                else {
                    return Err("RunStep recursor motive is not a family".into());
                };
                self.unify(env, motive_domain, run_step)?;
                let ExpNode::Sort(motive_sort) =
                    arena.get(crate::raw::calculus::whnf(env, self.zonk(env, motive_body)))
                else {
                    return Err("RunStep recursor motive does not return a sort".into());
                };
                let branch_sort = self
                    .infer_sort(env, module, context, state_ty)?
                    .relation_of_sort(motive_sort)
                    .ok_or("invalid recursor product rule")?;
                let shifted_state = shift_bound_indices(arena, state_ty, 1, 0);
                let shifted_result = shift_bound_indices(arena, result_ty, 1, 0);
                let continue_value = arena.alloc(ExpNode::Continue {
                    state_ty: shifted_state,
                    result_ty: shifted_result,
                    next: arena.exp_bound(0),
                });
                let continue_result = arena.alloc(ExpNode::App {
                    func: shift_bound_indices(arena, motive, 1, 0),
                    arg: continue_value,
                });
                let continue_ty = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: state_ty,
                    body: continue_result,
                });
                if self.infer_sort(env, module, context, continue_ty)? != branch_sort {
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
                    func: shift_bound_indices(arena, motive, 1, 0),
                    arg: finish_value,
                });
                let finish_ty = arena.alloc(ExpNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: result_ty,
                    body: finish_result,
                });
                if self.infer_sort(env, module, context, finish_ty)? != branch_sort {
                    return Err(
                        "RunStep finish branch type must have the branch product sort".into(),
                    );
                }
                self.check_pts(env, module, context, on_finish, finish_ty)?;
                self.check_pts(env, module, context, scrutinee, run_step)?;
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
                    .check_computation_term(program, program_ty)
                    .map_err(|error| format!("ill-typed boxed Program: {error:?}"))?;
                let reflected_ty =
                    crate::raw::reflection::reflect_computation_type(env, program_ty)
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
                    arena.alloc(ExpNode::BoxType { program_ty }),
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
                self.infer_sort(env, module, context, superset)?;
                let power = arena.alloc(ExpNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                self.check_pts(env, module, context, element, superset)?;
                let membership = arena.alloc(ExpNode::Pred {
                    superset,
                    subset,
                    element,
                });
                self.check_pts(env, module, context, proof, membership)?;
                Ok(arena.alloc(ExpNode::TypeLift { superset, subset }))
            }
            ExpNode::Prove(Prove::ExistsIntro { element, set }) => {
                self.check_pts(env, module, context, element, set)?;
                self.infer_sort(env, module, context, set)?;
                Ok(arena.alloc(ExpNode::Exists { set }))
            }
            ExpNode::Prove(Prove::SubsetElim {
                element,
                subset,
                superset,
            }) => {
                let lifted = arena.alloc(ExpNode::TypeLift { superset, subset });
                self.check_pts(env, module, context, element, lifted)?;
                Ok(arena.alloc(ExpNode::Pred {
                    superset,
                    subset,
                    element,
                }))
            }
            ExpNode::Prove(Prove::IdRefl { element }) => {
                let ty = self.infer_pts(env, module, context, element)?;
                self.infer_sort(env, module, context, ty)?;
                Ok(arena.alloc(ExpNode::Equal {
                    left: element,
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
                self.infer_sort(env, module, context, ty)?;
                self.check_pts(env, module, context, left, ty)?;
                self.check_pts(env, module, context, right, ty)?;
                let ty = self.zonk(env, ty);
                context.push(ExpContextEntry { var, ty });
                let proposition = arena.sort(Sort::Prop);
                let predicate_result = self.check_pts(env, module, context, predicate, proposition);
                context.pop();
                predicate_result?;
                let predicate_function = arena.alloc(ExpNode::Lam {
                    var,
                    ty,
                    body: predicate,
                });
                let base_ty = arena.alloc(ExpNode::App {
                    func: predicate_function,
                    arg: left,
                });
                self.check_pts(env, module, context, base, base_ty)?;
                let equality_ty = arena.alloc(ExpNode::Equal { left, right });
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
                    domain,
                    codomain,
                    map: func,
                    existence,
                    uniqueness,
                });
                self.check_pts(env, module, context, take, codomain)?;
                self.check_pts(env, module, context, element, domain)?;
                let mapped = arena.alloc(ExpNode::App { func, arg: element });
                Ok(arena.alloc(ExpNode::Equal {
                    left: take,
                    right: mapped,
                }))
            }
            _ => {
                self.failure = Some(MetaState::Unsupported);
                Err(
                    "metavariable inference for this expression is not supported by the solver"
                        .into(),
                )
            }
        }
    }

    /// Refine an unknown scrutinee type using the inductive named by `\in`.
    /// Build its arguments in the original hole's scope, before pattern binders
    /// are introduced, so the inferred type cannot capture those binders.
    pub(crate) fn inductive_arguments(
        &mut self,
        env: &CrateEnv,
        inductive: InductiveId,
        ty: Exp,
    ) -> Result<(Vec<Exp>, Vec<Exp>), String> {
        let arena = env.arena();
        let ty = base_carrier(env, self.zonk(env, ty));
        if let ExpNode::Meta { metavariable, .. } = arena.get(ty) {
            let entry = &self.entries[metavariable.index()];
            let (context, scope_len, span) = (entry.context.clone(), entry.scope_len, entry.span);
            let spec = env.inductive(inductive);
            let mut parameters = Vec::new();
            for (_, expected) in spec.parameters() {
                let expected = instantiate_telescope(arena, *expected, &parameters);
                let argument = self.fresh_synthetic_in_scope(env, &context, scope_len, span);
                self.set_meta_type(env, argument, expected)?;
                parameters.push(argument);
            }
            let mut arity = instantiate_telescope(arena, spec.arity(arena), &parameters);
            let mut indices = Vec::new();
            while let ExpNode::Prod { ty, body, .. } = arena.get(arity) {
                let index = self.fresh_synthetic_in_scope(env, &context, scope_len, span);
                self.set_meta_type(env, index, ty)?;
                indices.push(index);
                arity = instantiate(arena, body, index);
            }
            let head = arena.alloc(ExpNode::IndType {
                indspec: inductive,
                parameters,
            });
            let instance = assoc_apply(arena, head, indices);
            let original = arena.alloc(ExpNode::Meta {
                metavariable,
                spine: (0..scope_len)
                    .rev()
                    .map(|index| arena.exp_bound(index))
                    .collect(),
            });
            self.unify(env, original, instance)?;
        }
        let (head, indices) = decompose_app(arena, self.zonk(env, ty));
        let ExpNode::IndType {
            indspec,
            parameters,
        } = arena.get(head)
        else {
            return Err("Match scrutinee must have an inductive type".into());
        };
        if indspec != inductive {
            return Err("Match scrutinee type does not match its path".into());
        }
        Ok((parameters, indices))
    }

    fn infer_motive_kind(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        motive: Exp,
    ) -> Result<Exp, String> {
        // Like the strict checker's motive inference, do not demand a sort
        // above a product whose codomain is already SetKind or PropKind.
        let mark = context.len();
        let result = (|| {
            let mut binders = Vec::new();
            let mut body = self.zonk(env, motive);
            while let ExpNode::Lam {
                var,
                ty,
                body: next,
            } = env.arena().get(body)
            {
                self.infer_sort(env, module, context, ty)?;
                context.push(ExpContextEntry { var, ty });
                binders.push((var, ty));
                body = next;
            }
            let body_ty = self.infer_pts(env, module, context, body)?;
            Ok(assoc_prod(env.arena(), binders, body_ty))
        })();
        context.truncate(mark);
        result
    }

    fn infer_recursion_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        state_ty: Exp,
        result_ty: Exp,
    ) -> Result<Sort, String> {
        let state_sort = self.infer_sort(env, module, context, state_ty)?;
        let result_sort = self.infer_sort(env, module, context, result_ty)?;
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
        if !self.contains_unsolved(env, term) {
            return CheckSession::new(env, context)
                .infer_sort(term)
                .map_err(|error| format!("{error:?}"));
        }
        if matches!(env.arena().get(term), ExpNode::Meta { .. }) {
            let constraint = GoalConstraint::IsSort { term };
            self.set_principal_for_meta(env, term, &constraint);
            self.constrain(env, constraint);
            return Ok(Sort::Set(0));
        }
        let ty = self.infer_pts(env, module, context, term)?;
        match env.arena().get(self.zonk(env, ty)) {
            ExpNode::Sort(sort) => Ok(sort),
            ExpNode::Meta { .. } => {
                self.constrain(env, GoalConstraint::IsSort { term });
                Ok(Sort::Set(0))
            }
            _ => Err("expression does not have a sort".into()),
        }
    }

    pub(crate) fn unify(&mut self, env: &CrateEnv, left: Exp, right: Exp) -> Result<bool, String> {
        let index = self.constraints.len();
        self.constrain(env, GoalConstraint::Equal { left, right });
        let result = self.unify_rec(env, left, right, &mut HashSet::new());
        match &result {
            Ok(true) => self.constraints[index].status = ConstraintStatus::Discharged,
            Ok(false) => self.constraints[index].status = ConstraintStatus::Blocked,
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
        if left == right || erased_convertible(env, left, right) {
            return Ok(true);
        }
        // Expand local definitions before rigid comparison. Keep named heads
        // so structural matching can still infer their implicit arguments.
        let left = beta_head(env.arena(), left);
        let right = beta_head(env.arena(), right);
        if !visiting.insert((left, right)) {
            return Ok(true);
        }
        match (env.arena().get(left), env.arena().get(right)) {
            (
                ExpNode::Meta {
                    metavariable,
                    spine: left_spine,
                },
                ExpNode::Meta {
                    metavariable: other,
                    spine: right_spine,
                },
            ) if metavariable == other => {
                let scope = self.entries[metavariable.index()].scope_len;
                Ok(left_spine[..scope]
                    .iter()
                    .zip(&right_spine[..scope])
                    .all(|(a, b)| erased_convertible(env, *a, *b)))
            }
            (
                ExpNode::Meta {
                    metavariable,
                    spine,
                },
                _,
            ) => self.assign(env, metavariable, &spine, right),
            (
                _,
                ExpNode::Meta {
                    metavariable,
                    spine,
                },
            ) => self.assign(env, metavariable, &spine, left),
            (left_node, right_node) => {
                if !rigid_heads_compatible(&left_node, &right_node) {
                    if flexible_head(env, left) || flexible_head(env, right) {
                        return Ok(false);
                    }
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
        spine: &[Exp],
        value: Exp,
    ) -> Result<bool, String> {
        if self.occurs(env, metavariable, value, &mut HashSet::new()) {
            return Err(format!(
                "occurs check failed for {}",
                self.entries[metavariable.index()]
                    .flavor
                    .display_name(metavariable)
            ));
        }
        let entry = &self.entries[metavariable.index()];
        // Only identity contextual spines are solved here. Non-pattern
        // equations stay blocked until later substitutions simplify them.
        if !spine.iter().rev().enumerate().all(
            |(index, exp)| matches!(env.arena().get(*exp), ExpNode::Bound(bound) if bound == index),
        ) {
            return Ok(false);
        }
        let occurrence_scope = spine.len();
        let value = if occurrence_scope >= entry.scope_len {
            remove_unused_ambient_binders(env.arena(), value, occurrence_scope - entry.scope_len)
                .ok_or_else(|| {
                    format!(
                        "solution for {} captures a variable outside its shared context",
                        entry.flavor.display_name(metavariable)
                    )
                })?
        } else {
            shift_bound_indices(env.arena(), value, entry.scope_len - occurrence_scope, 0)
        };
        if let Some(previous) = entry.assignment {
            return self.unify_rec(env, previous, value, &mut HashSet::new());
        }
        self.entries[metavariable.index()].assignment = Some(value);
        Ok(true)
    }

    fn occurs(&self, env: &CrateEnv, needle: MetaVarId, exp: Exp, seen: &mut HashSet<Exp>) -> bool {
        if !seen.insert(exp) {
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
            return *result;
        }
        let arena = env.arena();
        let result = match arena.get(exp) {
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                let entry = &self.entries[metavariable.index()];
                if let Some(assignment) = entry.assignment {
                    if !resolving.insert(metavariable) {
                        exp
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
                    exp
                }
            }
            node => {
                let original = node.clone();
                let mapped =
                    map_children(node, |child| self.zonk_rec(env, child, cache, resolving));
                if original == mapped {
                    exp
                } else {
                    arena.alloc(mapped)
                }
            }
        };
        cache.insert(exp, result);
        result
    }

    pub(crate) fn contains_unsolved(&self, env: &CrateEnv, exp: Exp) -> bool {
        fn visit(env: &CrateEnv, exp: Exp, seen: &mut HashSet<Exp>) -> bool {
            if !seen.insert(exp) {
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

    pub(crate) fn finish(&mut self, env: &CrateEnv) -> Result<(), ElaborationError> {
        loop {
            let before = self
                .entries
                .iter()
                .filter(|entry| entry.assignment.is_some())
                .count();
            for index in 0..self.constraints.len() {
                if self.constraints[index].status != ConstraintStatus::Blocked {
                    continue;
                }
                let GoalConstraint::Equal { left, right } = self.constraints[index].original else {
                    continue;
                };
                match self.unify_rec(env, left, right, &mut HashSet::new()) {
                    Ok(true) => self.constraints[index].status = ConstraintStatus::Discharged,
                    Ok(false) => {}
                    Err(message) => {
                        self.constraints[index].status = ConstraintStatus::Failed;
                        return Err(self.constraint_error(env, message));
                    }
                }
            }
            for index in 0..self.entries.len() {
                let entry = &self.entries[index];
                let (Some(value), Some(expected)) = (entry.assignment, entry.inferred_type) else {
                    continue;
                };
                if self.contains_unsolved(env, value) || !self.contains_unsolved(env, expected) {
                    continue;
                }
                let value = self.zonk(env, value);
                let mut context = entry.context.clone();
                for binding in &mut context {
                    binding.ty = self.zonk(env, binding.ty);
                }
                if let Ok(inferred) = CheckSession::new(env, &mut context).infer_pts(value) {
                    self.unify(env, expected, inferred)
                        .map_err(|message| self.constraint_error(env, message))?;
                }
            }
            if before
                == self
                    .entries
                    .iter()
                    .filter(|entry| entry.assignment.is_some())
                    .count()
            {
                break;
            }
        }
        let goals = self.goals(env);
        if goals.is_empty() {
            Ok(())
        } else {
            Err(ElaborationError::Metavariables(goals))
        }
    }

    fn solved(&self, env: &CrateEnv, id: MetaVarId) -> bool {
        self.entries[id.index()]
            .assignment
            .is_some_and(|value| !self.contains_unsolved(env, value))
    }

    fn goals(&self, env: &CrateEnv) -> Vec<MetaGoal> {
        self.entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                let id = MetaVarId(index as u32);
                (entry.flavor != MetaFlavor::Synthetic
                    && (entry.flavor == MetaFlavor::Goal || !self.solved(env, id)))
                .then(|| self.goal_for(env, id))
            })
            .collect()
    }

    fn constraint_diagnostic(
        &self,
        env: &CrateEnv,
        record: &ConstraintRecord,
    ) -> ConstraintDiagnostic {
        let names = |id: MetaVarId| self.entries[id.index()].flavor.display_name(id);
        let printer = crate::raw::printing::Printer::new(env, &names);
        let normalized = self.zonk_constraint(env, &record.original);
        let mut context = match &record.original {
            GoalConstraint::HasType { term, .. } | GoalConstraint::IsSort { term } => {
                match env.arena().get(*term) {
                    ExpNode::Meta { metavariable, .. } => {
                        self.entries[metavariable.index()].context.clone()
                    }
                    _ => Vec::new(),
                }
            }
            _ => Vec::new(),
        };
        for binding in &mut context {
            binding.ty = self.zonk(env, binding.ty);
        }
        let status = match &normalized {
            GoalConstraint::Equal { left, right } if erased_convertible(env, *left, *right) => {
                ConstraintStatus::Discharged
            }
            GoalConstraint::HasType { term, expected }
                if !self.contains_unsolved(env, *term)
                    && !self.contains_unsolved(env, *expected)
                    && CheckSession::new(env, &mut context)
                        .check_pts(*term, *expected)
                        .is_ok() =>
            {
                ConstraintStatus::Discharged
            }
            GoalConstraint::IsSort { term }
                if !self.contains_unsolved(env, *term)
                    && CheckSession::new(env, &mut context)
                        .infer_sort(*term)
                        .is_ok() =>
            {
                ConstraintStatus::Discharged
            }
            _ => record.status,
        };
        ConstraintDiagnostic {
            original: format_constraint(&printer, &record.original),
            normalized: format_constraint(&printer, &normalized),
            status,
            origins: record.origins.clone(),
        }
    }

    fn goal_for(&self, env: &CrateEnv, id: MetaVarId) -> MetaGoal {
        let entry = &self.entries[id.index()];
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
                    || record
                        .origins
                        .iter()
                        .any(|span| entry.occurrences.contains(span))
            })
            .map(|record| self.constraint_diagnostic(env, record))
            .collect();
        // Dependencies are unresolved metas in this goal's type or assignment,
        // rather than every meta which ever shared a constraint.
        let mut dependencies = HashSet::new();
        for exp in [entry.inferred_type, entry.assignment]
            .into_iter()
            .flatten()
        {
            dependencies.extend(metas_in_exp(env, self.zonk(env, exp)));
        }
        dependencies.remove(&id);
        let mut dependencies: Vec<_> = dependencies.into_iter().collect();
        dependencies.sort_by_key(|meta| meta.0);
        let blocked = self.constraints.iter().any(|record| {
            record.status == ConstraintStatus::Blocked
                && metas_in_constraint(env, &record.original).contains(&id)
        });
        let state = if self.solved(env, id) {
            MetaState::Solved
        } else if blocked {
            MetaState::Unsupported
        } else if !dependencies.is_empty() {
            MetaState::Waiting
        } else {
            MetaState::InsufficientInformation
        };
        let names = |id: MetaVarId| self.entries[id.index()].flavor.display_name(id);
        let printer = crate::raw::printing::Printer::new(env, &names);
        let context = entry
            .context
            .iter()
            .map(|binding| crate::raw::exp::ExpContextEntry {
                var: binding.var,
                ty: self.zonk(env, binding.ty),
            })
            .collect();
        let principal = entry.principal.as_ref().map(|constraint| {
            // Keep the inspected occurrence visible even when it has a solution.
            let normalized = match constraint {
                GoalConstraint::HasType { term, expected } => GoalConstraint::HasType {
                    term: *term,
                    expected: self.zonk(env, *expected),
                },
                GoalConstraint::IsSort { term } => GoalConstraint::IsSort { term: *term },
                other => self.zonk_constraint(env, other),
            };
            format_constraint(&printer, &normalized)
        });
        MetaGoal {
            metavariable: id,
            flavor: entry.flavor,
            span: entry.span,
            occurrences: entry.occurrences.clone(),
            context: printer.format_ctx(&context),
            principal,
            solution: entry
                .assignment
                .map(|value| printer.format_exp(self.zonk(env, value))),
            state,
            constraints,
            dependencies,
        }
    }

    fn zonk_constraint(&self, env: &CrateEnv, constraint: &GoalConstraint) -> GoalConstraint {
        match constraint {
            GoalConstraint::HasType { term, expected } => GoalConstraint::HasType {
                term: self.zonk(env, *term),
                expected: self.zonk(env, *expected),
            },
            GoalConstraint::Equal { left, right } => GoalConstraint::Equal {
                left: self.zonk(env, *left),
                right: self.zonk(env, *right),
            },
            GoalConstraint::IsSort { term } => GoalConstraint::IsSort {
                term: self.zonk(env, *term),
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
        } => vec![*term, *expected],
        GoalConstraint::IsSort { term } => vec![*term],
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
        if !seen.insert(exp) {
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
    let ExpNode::App { func, arg } = arena.get(exp) else {
        return exp;
    };
    let head = beta_head(arena, func);
    if let ExpNode::Lam { body, .. } = arena.get(head) {
        let body = match arena.get(body) {
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
        children.push(child);
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
        state_ty,
        result_ty,
    });
    nondependent_product(arena, state_ty, run_step)
}

fn flexible_head(env: &CrateEnv, mut term: Exp) -> bool {
    loop {
        match env.arena().get(term) {
            ExpNode::App { func, .. } => term = func,
            ExpNode::Meta { .. } => return true,
            _ => return false,
        }
    }
}
