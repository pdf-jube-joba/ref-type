//! Source holes and diagnostics backed by the kernel's contextual solver.
use crate::{
    hir::{SourceSpan, SurfaceMeta},
    kernel_bridge::{base_carrier, instantiate, instantiate_telescope},
    raw::{
        environment::CrateEnv,
        exp::{Exp, ExpContext, ExpContextEntry, ExpNode},
        ids::{InductiveId, MetaVarId, ModuleId},
        sort::Sort,
        utils::{assoc_apply, decompose_app},
    },
};
use kernel::{
    metavariables::{Constraint, MetaContext, Outcome},
    syntax::{MetaId, Node},
};
use std::collections::{HashMap, HashSet};
pub(crate) mod diagnostics;
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
#[derive(Debug, Default)]
pub(crate) struct MetaStore {
    core: MetaContext,
    ids: HashMap<MetaId, MetaVarId>,
    core_ids: Vec<MetaId>,
    reported: usize,
    current_context: ExpContext,
    entries: Vec<MetaEntry>,
    named: HashMap<u32, MetaVarId>,
    constraints: Vec<ConstraintRecord>,
    failure: Option<MetaState>,
    origins: Vec<SourceSpan>,
    sources: HashMap<Exp, Vec<SourceSpan>>,
}
impl MetaStore {
    fn diagnostic_snapshot(&self) -> Self {
        Self {
            core: self.core.diagnostic_snapshot(),
            ids: self.ids.clone(),
            core_ids: self.core_ids.clone(),
            entries: self.entries.clone(),
            constraints: self.constraints.clone(),
            failure: self.failure,
            ..Self::default()
        }
    }

    pub(crate) fn clear(&mut self) {
        *self = Self::default();
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    fn sync(&mut self, env: &CrateEnv) {
        for (id, core) in self.core.entries() {
            let source = if let Some(&source) = self.ids.get(&id) {
                source
            } else {
                let source = MetaVarId(self.entries.len() as u32);
                self.ids.insert(id, source);
                self.core_ids.push(id);
                self.entries.push(MetaEntry {
                    flavor: MetaFlavor::Synthetic,
                    span: self.origins.first().copied().unwrap_or_default(),
                    occurrences: self.origins.clone(),
                    context: core
                        .context
                        .iter()
                        .map(|b| ExpContextEntry {
                            var: b.var,
                            ty: Exp(b.ty),
                        })
                        .collect(),
                    scope_len: core.context.len(),
                    assignment: None,
                    principal: None,
                    inferred_type: None,
                });
                source
            };
            if self.core_ids[source.index()] != id {
                continue;
            }
            env.arena().bind_meta(source, id);
            self.entries[source.index()].assignment = core.assignment.map(Exp);
            self.entries[source.index()].inferred_type = core.expected.map(Exp);
            if self.entries[source.index()].principal.is_none()
                && let Some(expected) = core.expected
            {
                let term = Exp(env.arena().core.alloc(Node::Meta {
                    id,
                    arguments: (0..core.context.len())
                        .rev()
                        .map(|i| env.arena().core.bound(i))
                        .collect(),
                }));
                let constraint = GoalConstraint::HasType {
                    term,
                    expected: Exp(expected),
                };
                self.entries[source.index()].principal = Some(constraint.clone());
                self.constraints.push(ConstraintRecord {
                    core: None,
                    original: constraint,
                    status: ConstraintStatus::Residual,
                    origins: self.entries[source.index()].occurrences.clone(),
                });
            }
        }
        let history = self.core.history()[self.reported..].to_vec();
        self.reported = self.core.history().len();
        for constraint in history {
            let retained = constraint.clone();
            let goal = match constraint {
                Constraint::Equal { left, right, .. } => GoalConstraint::Equal {
                    left: Exp(left),
                    right: Exp(right),
                },
                Constraint::HasType { term, expected, .. }
                | Constraint::Validate {
                    term,
                    expected: Some(expected),
                    ..
                } => GoalConstraint::HasType {
                    term: Exp(term),
                    expected: Exp(expected),
                },
                Constraint::IsSort { term, .. } => GoalConstraint::IsSort { term: Exp(term) },
                _ => continue,
            };
            self.constrain(env, goal);
            self.constraints.last_mut().unwrap().core = Some(retained);
        }
    }
    pub(crate) fn fresh(
        &mut self,
        env: &CrateEnv,
        kind: SurfaceMeta,
        span: SourceSpan,
        context: &ExpContext,
        scope_len: usize,
    ) -> Result<Exp, crate::error::Error> {
        self.current_context = context.clone();
        let flavor = MetaFlavor::from(kind);
        let existing = match flavor {
            MetaFlavor::Named(n) => self.named.get(&n).copied(),
            _ => None,
        };
        let base = context.len().saturating_sub(scope_len);
        let source = if let Some(source) = existing {
            let entry = &mut self.entries[source.index()];
            entry.occurrences.push(span);
            let start = entry.context.len().saturating_sub(entry.scope_len);
            let common = entry.context[start..]
                .iter()
                .zip(&context[base..])
                .take_while(|(a, b)| a.var == b.var)
                .count();
            if common < entry.scope_len {
                let fresh = self
                    .core
                    .restrict(&env.kernel.borrow(), self.core_ids[source.index()], common)
                    .map_err(crate::error::Error::from)?;
                let Node::Meta { id, .. } = env.arena().core.get(fresh) else {
                    unreachable!()
                };
                self.core_ids[source.index()] = id;
                self.ids.insert(id, source);
                env.arena().bind_meta(source, id);
                entry.context = context[..base + common].to_vec();
                entry.scope_len = common;
            }
            source
        } else {
            let term = crate::kernel_bridge::logical_in_scope(
                env,
                context,
                base,
                &[],
                |env, context, _| Ok(self.core.fresh(env.arena(), context, None)),
            )?;
            let Node::Meta { id, .. } = env.arena().core.get(term) else {
                unreachable!()
            };
            let source = MetaVarId(self.entries.len() as u32);
            self.core
                .set_origin(id, kernel::metavariables::OriginId(source.index() as u64))
                .map_err(crate::error::Error::from)?;
            self.ids.insert(id, source);
            self.core_ids.push(id);
            env.arena().bind_meta(source, id);
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
            if let MetaFlavor::Named(n) = flavor {
                self.named.insert(n, source);
            }
            source
        };
        let keep = self.entries[source.index()].scope_len;
        let arguments = (scope_len - keep..scope_len)
            .rev()
            .map(|i| env.arena().core.bound(i))
            .collect();
        Ok(Exp(env.arena().core.alloc(Node::Meta {
            id: self.core_ids[source.index()],
            arguments,
        })))
    }
    fn fresh_synthetic_in_scope(
        &mut self,
        env: &CrateEnv,
        context: &ExpContext,
        scope_len: usize,
        span: SourceSpan,
    ) -> Exp {
        let e = self
            .fresh(env, SurfaceMeta::Implicit, span, context, scope_len)
            .expect("valid contextual synthetic hole");
        let Node::Meta { id, .. } = env.arena().core.get(e.0) else {
            unreachable!()
        };
        self.entries[self.ids[&id].index()].flavor = MetaFlavor::Synthetic;
        e
    }
    fn set_meta_type(
        &mut self,
        env: &CrateEnv,
        term: Exp,
        expected: Exp,
    ) -> Result<(), crate::error::Error> {
        let context = self.current_context.clone();
        self.check_pts(env, env.root_module(), &mut context.clone(), term, expected)
    }
    pub(crate) fn check_pts(
        &mut self,
        env: &CrateEnv,
        _module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
        expected: Exp,
    ) -> Result<(), crate::error::Error> {
        self.current_context = context.clone();
        let constraint = GoalConstraint::HasType { term, expected };
        self.set_principal_for_meta(env, term, &constraint);
        let index = self.constraints.len();
        self.constrain(env, constraint);
        let result = crate::kernel_bridge::logical(
            env,
            context,
            &[term, expected],
            |env, context, terms| {
                self.constraints[index].core = Some(Constraint::HasType {
                    context: context.clone(),
                    term: terms[0],
                    expected: terms[1],
                });
                self.core.check(env, context, terms[0], terms[1])
            },
        );
        self.sync(env);
        self.constraints[index].status = match result {
            Ok(Outcome::Solved) => ConstraintStatus::Discharged,
            Ok(Outcome::Blocked) => ConstraintStatus::Blocked,
            Err(_) => ConstraintStatus::Failed,
        };
        result.map(|_| ())
    }
    pub(crate) fn infer_pts(
        &mut self,
        env: &CrateEnv,
        _module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
    ) -> Result<Exp, crate::error::Error> {
        self.current_context = context.clone();
        let result = crate::kernel_bridge::logical(env, context, &[term], |env, context, terms| {
            self.core.infer(env, context, terms[0])
        })
        .map(Exp);
        self.sync(env);
        if let Ok(expected) = result {
            let constraint = GoalConstraint::HasType { term, expected };
            self.set_principal_for_meta(env, term, &constraint);
            self.constrain(env, constraint);
        }
        result
    }
    pub(crate) fn infer_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut ExpContext,
        term: Exp,
    ) -> Result<Sort, crate::error::Error> {
        let constraint = GoalConstraint::IsSort { term };
        self.set_principal_for_meta(env, term, &constraint);
        self.constrain(env, constraint);
        crate::kernel_bridge::logical(env, context, &[term], |_env, context, terms| {
            self.core.constrain(Constraint::IsSort {
                context,
                term: terms[0],
            });
            Ok(())
        })?;
        let ty = self.infer_pts(env, module, context, term)?;
        match env.arena().get(self.zonk(env, ty)) {
            ExpNode::Sort(sort) => Ok(sort),
            ExpNode::Meta { .. } => Ok(Sort::Set(0)),
            _ => Err(crate::error::Error::Invalid(
                crate::error::Invalid::ExpressionDoesNotHaveASort,
            )),
        }
    }
    pub(crate) fn unify_in_context(
        &mut self,
        env: &CrateEnv,
        context: &ExpContext,
        left: Exp,
        right: Exp,
    ) -> Result<bool, crate::error::Error> {
        self.current_context = context.clone();
        self.unify(env, left, right)
    }

    pub(crate) fn unify(
        &mut self,
        env: &CrateEnv,
        left: Exp,
        right: Exp,
    ) -> Result<bool, crate::error::Error> {
        let index = self.constraints.len();
        self.constrain(env, GoalConstraint::Equal { left, right });
        let result = crate::kernel_bridge::logical(
            env,
            &self.current_context,
            &[left, right],
            |env, context, terms| {
                self.constraints[index].core = Some(Constraint::Equal {
                    context: context.clone(),
                    left: terms[0],
                    right: terms[1],
                });
                self.core.unify(env, &context, terms[0], terms[1])
            },
        )
        .map(|o| o == Outcome::Solved);
        if result.is_err() && std::env::var_os("REF_TYPE_DEBUG_CONSTRAINTS").is_some() {
            if let Some(Constraint::Equal { left, right, .. }) = &self.constraints[index].core {
                if let Ok(Some((path, left, right))) =
                    kernel::reduction::first_difference(&env.kernel.borrow(), *left, *right)
                {
                    eprintln!(
                        "failed equality {path:?}: {} != {}",
                        crate::raw::printing::format_exp(env, Exp(left)),
                        crate::raw::printing::format_exp(env, Exp(right))
                    );
                }
            }
        }
        self.constraints[index].status = match result {
            Ok(true) => ConstraintStatus::Discharged,
            Ok(false) => ConstraintStatus::Blocked,
            Err(_) => ConstraintStatus::Failed,
        };
        self.sync(env);
        result
    }
    pub(crate) fn zonk(&self, env: &CrateEnv, term: Exp) -> Exp {
        fn visit(
            store: &MetaStore,
            env: &CrateEnv,
            e: kernel::syntax::Expression,
            cache: &mut HashMap<kernel::syntax::Expression, kernel::syntax::Expression>,
        ) -> kernel::syntax::Expression {
            if let Some(&e) = cache.get(&e) {
                return e;
            }
            let arena = &env.arena().core;
            let result = if let Node::Meta { id, .. } = arena.get(e)
                && store.core.entry(id).is_ok()
            {
                store
                    .core
                    .zonk(arena, e)
                    .expect("consistent kernel meta context")
            } else {
                arena
                    .map_children(e, |child, _| {
                        Ok::<_, std::convert::Infallible>(visit(store, env, child, cache))
                    })
                    .unwrap()
            };
            cache.insert(e, result);
            result
        }
        Exp(visit(self, env, term.0, &mut HashMap::new()))
    }
    pub(crate) fn contains_unsolved(&self, env: &CrateEnv, term: Exp) -> bool {
        !metas_in_exp(env, self.zonk(env, term)).is_empty()
    }
    /// Solve the terms needed by an inner check without finalizing unrelated
    /// holes in the surrounding, still incomplete logical expression.
    pub(crate) fn solve_for(
        &mut self,
        env: &CrateEnv,
        terms: &[Exp],
    ) -> Result<(), ElaborationError> {
        let result = self.core.solve_pending(&env.kernel.borrow());
        self.sync(env);
        result.map_err(|error| self.constraint_error(env, crate::error::Error::Kernel(error)))?;
        if terms.iter().any(|&term| self.contains_unsolved(env, term)) {
            return Err(self.goal_error(env));
        }
        Ok(())
    }

    pub(crate) fn finish(&mut self, env: &CrateEnv) -> Result<(), ElaborationError> {
        let result = self.core.finish(&env.kernel.borrow());
        self.sync(env);
        for record in &mut self.constraints {
            if result.is_ok()
                || record
                    .core
                    .as_ref()
                    .is_some_and(|constraint| self.core.is_discharged(constraint))
            {
                record.status = ConstraintStatus::Discharged;
            }
        }
        match result {
            Err(error)
                if matches!(
                    error.root(),
                    kernel::metavariables::Error::Unresolved { .. }
                ) =>
            {
                Err(self.goal_error(env))
            }
            Err(error) => Err(self.constraint_error(env, crate::error::Error::Kernel(error))),
            Ok(()) => {
                let goals = crate::diagnostics::with_diagnostic_mode(
                    crate::DiagnosticMode::Compact,
                    || self.goals(env),
                );
                if goals.is_empty() {
                    Ok(())
                } else {
                    Err(self.defer_goals(goals))
                }
            }
        }
    }
    fn goal_error(&self, env: &CrateEnv) -> ElaborationError {
        let goals =
            crate::diagnostics::with_diagnostic_mode(crate::DiagnosticMode::Compact, || {
                self.goals(env)
            });
        self.defer_goals(goals)
    }
    fn defer_goals(&self, goals: Vec<MetaGoal>) -> ElaborationError {
        let summary = ElaborationError::Metavariables(goals);
        if crate::diagnostics::compact() {
            return summary;
        }
        let _profile = crate::diagnostics::DiagnosticProfile::start("capture");
        ElaborationError::Deferred {
            summary: Box::new(summary),
            details: std::rc::Rc::new(diagnostics::DeferredDetails::logical(
                self.diagnostic_snapshot(),
                None,
            )),
        }
    }
    pub(crate) fn constraint_error(
        &self,
        env: &CrateEnv,
        message: crate::error::Error,
    ) -> ElaborationError {
        if crate::diagnostics::compact() {
            return ElaborationError::Failure(message);
        }
        let _profile = crate::diagnostics::DiagnosticProfile::start("capture");
        let mut goals =
            crate::diagnostics::with_diagnostic_mode(crate::DiagnosticMode::Compact, || {
                self.goals(env)
            });
        for goal in &mut goals {
            if goal.state != MetaState::Solved {
                goal.state = self.failure.unwrap_or(MetaState::Contradiction);
            }
        }
        ElaborationError::Deferred {
            summary: Box::new(ElaborationError::ConstraintFailure {
                cause: Box::new(message.clone()),
                constraints: vec![],
                goals,
                omitted_constraints: 0,
            }),
            details: std::rc::Rc::new(diagnostics::DeferredDetails::logical(
                self.diagnostic_snapshot(),
                Some(message),
            )),
        }
    }
    pub(crate) fn detailed_error(
        &self,
        env: &CrateEnv,
        message: crate::error::Error,
    ) -> ElaborationError {
        if crate::diagnostics::compact() {
            return ElaborationError::Failure(message);
        }
        let state = self.failure.unwrap_or(MetaState::Contradiction);
        let mut goals = self.goals(env);
        for goal in &mut goals {
            if goal.state != MetaState::Solved {
                goal.state = state;
            }
        }
        ElaborationError::ConstraintFailure {
            cause: Box::new(message),
            constraints: self
                .constraints
                .iter()
                .take(crate::diagnostics::CONSTRAINTS)
                .map(|record| self.constraint_diagnostic(env, record))
                .collect(),
            goals,
            omitted_constraints: self
                .constraints
                .len()
                .saturating_sub(crate::diagnostics::CONSTRAINTS),
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
    pub(crate) fn constrain(&mut self, env: &CrateEnv, constraint: GoalConstraint) {
        let mut origins = self.origins.clone();
        for meta in metas_in_constraint(env, &constraint) {
            origins.extend(self.entries[meta.index()].occurrences.iter().copied());
        }
        origins.sort_by_key(|span| (span.start, span.end));
        origins.dedup();
        self.constraints.push(ConstraintRecord {
            core: None,
            origins,
            original: constraint,
            status: ConstraintStatus::Residual,
        });
    }
    fn set_principal_for_meta(&mut self, env: &CrateEnv, term: Exp, constraint: &GoalConstraint) {
        let term = self.zonk(env, term);
        if matches!(env.arena().core.get(term.0), Node::Meta { .. })
            && let ExpNode::Meta { metavariable, .. } = env.arena().get(term)
            && self.entries[metavariable.index()].principal.is_none()
        {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
    }
    pub(crate) fn inductive_arguments(
        &mut self,
        env: &CrateEnv,
        inductive: InductiveId,
        ty: Exp,
    ) -> Result<(Vec<Exp>, Vec<Exp>), crate::error::Error> {
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
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::MatchScrutineeMustHaveAnInductiveType,
            ));
        };
        if indspec != inductive {
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::MatchScrutineeTypeDoesNotMatchItsPath,
            ));
        }
        Ok((parameters, indices))
    }
    fn solved(&self, env: &CrateEnv, id: MetaVarId) -> bool {
        self.entries[id.index()]
            .assignment
            .is_some_and(|value| !self.contains_unsolved(env, value))
    }
    pub(crate) fn goals(&self, env: &CrateEnv) -> Vec<MetaGoal> {
        let _profile = crate::diagnostics::DiagnosticProfile::start("logical-goals");
        let mut attached = HashSet::new();
        let mut seen = HashSet::new();
        for entry in &self.entries {
            if entry.flavor != MetaFlavor::Synthetic {
                let roots = entry
                    .assignment
                    .into_iter()
                    .chain(entry.inferred_type)
                    .chain(entry.context.iter().map(|b| b.ty))
                    .map(|e| e.0);
                let mut pending = roots.collect::<Vec<_>>();
                while let Some(e) = pending.pop() {
                    if !seen.insert(e) {
                        continue;
                    }
                    if let Node::Meta { id, .. } = env.arena().core.get(e)
                        && let Ok(meta) = self.core.entry(id)
                    {
                        if let Some(source) = self.ids.get(&id) {
                            attached.insert(*source);
                        }
                        pending.extend(meta.assignment);
                        pending.extend(meta.expected);
                    }
                    pending.extend(env.arena().core.children(e).into_iter().map(|(e, _)| e));
                }
            }
        }
        let candidates: Vec<_> = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                let id = MetaVarId(index as u32);
                (entry.flavor == MetaFlavor::Goal
                    || (!self.solved(env, id)
                        && (entry.flavor != MetaFlavor::Synthetic || !attached.contains(&id))))
                .then_some(id)
            })
            .collect();
        let omitted = candidates.len().saturating_sub(crate::diagnostics::GOALS);
        let mut goals: Vec<_> = candidates
            .into_iter()
            .take(crate::diagnostics::GOALS)
            .map(|id| self.goal_for(env, id))
            .collect();
        if let Some(goal) = goals.last_mut() {
            goal.omitted_goals = omitted;
        }
        goals
    }
    fn constraint_diagnostic(
        &self,
        env: &CrateEnv,
        record: &ConstraintRecord,
    ) -> ConstraintDiagnostic {
        let names = |id: MetaVarId| self.entries[id.index()].flavor.display_name(id);
        let printer = crate::raw::printing::Printer::new(env, &names);
        let normalized = self.zonk_constraint(env, &record.original);
        ConstraintDiagnostic {
            original: format_constraint(&printer, &record.original),
            normalized: format_constraint(&printer, &normalized),
            status: record.status,
            origins: record.origins.iter().take(32).copied().collect(),
            omitted_origins: record.origins.len().saturating_sub(32),
        }
    }
    fn goal_for(&self, env: &CrateEnv, id: MetaVarId) -> MetaGoal {
        let entry = &self.entries[id.index()];
        let compact = crate::diagnostics::compact();
        let mut related = HashSet::from([id]);
        let mut selected = std::collections::BTreeSet::new();
        let mut examined = 0;
        let mut remaining_nodes = crate::diagnostics::SEARCH * 16;
        if !compact {
            loop {
                let before = selected.len();
                for (index, record) in self.constraints.iter().enumerate() {
                    if examined >= crate::diagnostics::SEARCH || remaining_nodes == 0 {
                        break;
                    }
                    examined += 1;
                    let mut metas = HashSet::new();
                    let mut pending = constraint_expressions(&record.original);
                    let mut seen = HashSet::new();
                    while let Some(exp) = pending.pop() {
                        if !seen.insert(exp) {
                            continue;
                        }
                        if remaining_nodes == 0 {
                            break;
                        }
                        remaining_nodes -= 1;
                        match env.arena().get(exp) {
                            ExpNode::Meta {
                                metavariable,
                                spine,
                            } => {
                                metas.insert(metavariable);
                                pending.extend(spine);
                            }
                            _ => pending.extend(logical_children(env, exp)),
                        }
                    }
                    if metas.iter().any(|meta| related.contains(meta))
                        || record
                            .origins
                            .iter()
                            .any(|span| entry.occurrences.contains(span))
                    {
                        related.extend(metas);
                        selected.insert(index);
                    }
                }
                if selected.len() == before
                    || examined >= crate::diagnostics::SEARCH
                    || remaining_nodes == 0
                {
                    break;
                }
            }
        }
        let omitted_constraints = if compact {
            0
        } else if examined >= crate::diagnostics::SEARCH || remaining_nodes == 0 {
            self.constraints
                .len()
                .saturating_sub(selected.len().min(crate::diagnostics::CONSTRAINTS))
        } else {
            selected
                .len()
                .saturating_sub(crate::diagnostics::CONSTRAINTS)
        };
        let constraints = selected
            .into_iter()
            .take(crate::diagnostics::CONSTRAINTS)
            .map(|index| self.constraint_diagnostic(env, &self.constraints[index]))
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
            .take(128)
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
            context: {
                let mut text = printer.format_ctx(&context);
                if entry.context.len() > 128 {
                    text.push_str(&format!(
                        "; … {} context entries omitted",
                        entry.context.len() - 128
                    ));
                }
                crate::diagnostics::bounded(text, 8192)
            },
            principal,
            solution: entry
                .assignment
                .map(|value| printer.format_exp(self.zonk(env, value))),
            state,
            constraints,
            omitted_constraints,
            omitted_goals: 0,
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

fn metas_in_constraint(env: &CrateEnv, constraint: &GoalConstraint) -> HashSet<MetaVarId> {
    constraint_expressions(constraint)
        .into_iter()
        .flat_map(|exp| metas_in_exp(env, exp))
        .collect()
}

fn metas_in_exp(env: &CrateEnv, exp: Exp) -> HashSet<MetaVarId> {
    let mut result = HashSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![exp];
    while let Some(exp) = pending.pop() {
        if !seen.insert(exp) {
            continue;
        }
        // Checked definitions are closed over their explicit arguments.
        // A frontend view of a specialized reference unfolds its body, which
        // would expand unrelated proofs merely to attach a source location.
        // Holes can only occur in the reference's actual arguments.
        if matches!(env.arena().core.get(exp.0), Node::Meta { .. })
            && let ExpNode::Meta { metavariable, .. } = env.arena().get(exp)
        {
            result.insert(metavariable);
        }
        pending.extend(
            env.arena()
                .core
                .children(exp.0)
                .into_iter()
                .map(|(child, _)| Exp(child)),
        );
    }
    result
}

fn logical_children(env: &CrateEnv, exp: Exp) -> Vec<Exp> {
    use crate::raw::traversal::Term;
    let mut children = Vec::new();
    Term::Logical(exp).visit_children(env.arena(), |child, _| {
        if let Term::Logical(child) = child {
            children.push(child);
        }
    });
    children
}
