//! Elaboration-time contextual metavariables and their diagnostics.

use crate::syntax::{SourceSpan, SurfaceMeta};
use kernel::{
    calculus::{
        can_weaken_to, common_ambient_carrier, erased_convertible, instantiate_telescope,
        map_children, remove_unused_ambient_binders, shift_bound_indices,
    },
    derivation::CheckSession,
    environment::{CrateEnv, DefinitionKind, ModuleParameterKind},
    exp::{Context, ContextEntry, RawExp, RawNode},
    ids::{MetaVarId, ModuleId, SymbolId},
    inductive::CtorBinder,
    sort::Sort,
};
use serde::Serialize;
use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MetaFlavor {
    Implicit,
    Goal,
    Named(u32),
    Synthetic,
}

impl From<SurfaceMeta> for MetaFlavor {
    fn from(value: SurfaceMeta) -> Self {
        match value {
            SurfaceMeta::Implicit => Self::Implicit,
            SurfaceMeta::Goal => Self::Goal,
            SurfaceMeta::Named(number) => Self::Named(number),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum GoalConstraint {
    HasType { term: RawExp, expected: RawExp },
    Equal { left: RawExp, right: RawExp },
    IsSort { term: RawExp },
    IsValueType { term: RawExp },
    IsComputationType { term: RawExp },
    HasValueType { term: RawExp, expected: RawExp },
    HasComputationType { term: RawExp, expected: RawExp },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ConstraintStatus {
    Discharged,
    Residual,
    Failed,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConstraintRecord {
    pub original: GoalConstraint,
    pub normalized: GoalConstraint,
    pub status: ConstraintStatus,
}

#[derive(Debug, Clone, Serialize)]
pub struct MetaGoal {
    pub metavariable: MetaVarId,
    pub flavor: MetaFlavor,
    pub span: SourceSpan,
    pub context: Context,
    pub principal: Option<GoalConstraint>,
    pub constraints: Vec<ConstraintRecord>,
    pub dependencies: Vec<MetaVarId>,
}

impl MetaGoal {
    pub fn display_name(&self) -> String {
        match self.flavor {
            MetaFlavor::Implicit => "_".into(),
            MetaFlavor::Goal => format!("?#{}", self.metavariable.0),
            MetaFlavor::Named(number) => format!("?{number}"),
            MetaFlavor::Synthetic => format!("?m{}", self.metavariable.0),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum ElaborationError {
    Message(String),
    ConstraintFailure {
        message: String,
        constraints: Vec<ConstraintRecord>,
    },
    AmbiguousImplicit(Vec<MetaGoal>),
    UnsolvedGoals(Vec<MetaGoal>),
}

impl fmt::Display for ElaborationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Message(message) => formatter.write_str(message),
            Self::ConstraintFailure { message, .. } => write!(formatter, "{message}"),
            Self::AmbiguousImplicit(goals) => write!(
                formatter,
                "{} implicit metavariable(s) are not uniquely determined",
                goals.len()
            ),
            Self::UnsolvedGoals(goals) => {
                write!(
                    formatter,
                    "{} metavariable goal(s) remain unsolved",
                    goals.len()
                )
            }
        }
    }
}

impl Error for ElaborationError {}

pub fn format_elaboration_error(env: &CrateEnv, error: &ElaborationError) -> String {
    match error {
        ElaborationError::Message(message) => message.clone(),
        ElaborationError::ConstraintFailure {
            message,
            constraints,
        } => {
            let details = constraints
                .iter()
                .map(|constraint| format_constraint_record(env, constraint))
                .collect::<Vec<_>>()
                .join("\n");
            format!("{message}\n{details}")
        }
        ElaborationError::AmbiguousImplicit(goals) => format_goals(
            env,
            "implicit metavariable is not uniquely determined",
            goals,
        ),
        ElaborationError::UnsolvedGoals(goals) => {
            format_goals(env, "unsolved metavariable goal", goals)
        }
    }
}

fn format_goals(env: &CrateEnv, heading: &str, goals: &[MetaGoal]) -> String {
    goals
        .iter()
        .map(|goal| {
            let context = kernel::printing::format_ctx(env, &goal.context);
            let principal = goal
                .principal
                .as_ref()
                .map(|constraint| format_constraint(env, constraint))
                .unwrap_or_else(|| "<no principal judgement>".into());
            let constraints = goal
                .constraints
                .iter()
                .map(|constraint| format!("  {}", format_constraint_record(env, constraint)))
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                "{heading} {} at {}..{}\ncontext: [{}]\ngoal: {}\nconstraints:\n{}",
                goal.display_name(),
                goal.span.start,
                goal.span.end,
                context,
                principal,
                constraints
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn format_constraint_record(env: &CrateEnv, record: &ConstraintRecord) -> String {
    format!(
        "[{:?}] {}",
        record.status,
        format_constraint(env, &record.normalized)
    )
}

fn format_constraint(env: &CrateEnv, constraint: &GoalConstraint) -> String {
    let exp = |term| kernel::printing::format_exp(env, term);
    match constraint {
        GoalConstraint::HasType { term, expected } => {
            format!("{} : {}", exp(*term), exp(*expected))
        }
        GoalConstraint::Equal { left, right } => format!("{} ≡ {}", exp(*left), exp(*right)),
        GoalConstraint::IsSort { term } => format!("{} has a sort", exp(*term)),
        GoalConstraint::IsValueType { term } => format!("{} : \\VType", exp(*term)),
        GoalConstraint::IsComputationType { term } => {
            format!("{} is a computation type", exp(*term))
        }
        GoalConstraint::HasValueType { term, expected } => {
            format!("{} :value {}", exp(*term), exp(*expected))
        }
        GoalConstraint::HasComputationType { term, expected } => {
            format!("{} :computation {}", exp(*term), exp(*expected))
        }
    }
}

impl From<String> for ElaborationError {
    fn from(value: String) -> Self {
        Self::Message(value)
    }
}

impl From<&str> for ElaborationError {
    fn from(value: &str) -> Self {
        Self::Message(value.into())
    }
}

#[derive(Debug, Clone)]
struct MetaEntry {
    flavor: MetaFlavor,
    span: SourceSpan,
    context: Context,
    scope_len: usize,
    assignment: Option<RawExp>,
    principal: Option<GoalConstraint>,
    inferred_type: Option<RawExp>,
}

#[derive(Debug, Clone, Default)]
pub struct MetaStore {
    entries: Vec<MetaEntry>,
    named: HashMap<u32, MetaVarId>,
    constraints: Vec<ConstraintRecord>,
}

impl MetaStore {
    pub fn clear(&mut self) {
        self.entries.clear();
        self.named.clear();
        self.constraints.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn constraint_error(&self, message: String) -> ElaborationError {
        ElaborationError::ConstraintFailure {
            message,
            constraints: self.constraints.clone(),
        }
    }

    pub fn fresh(
        &mut self,
        env: &CrateEnv,
        kind: SurfaceMeta,
        span: SourceSpan,
        context: &Context,
        scope_len: usize,
    ) -> RawExp {
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
                .take_while(|(left, right)| left.var() == right.var())
                .count();
            if common < entry.scope_len {
                let removed = entry.scope_len - common;
                entry.scope_len = common;
                entry.context = context[..current_start + common].to_vec();
                if let Some(assignment) = entry.assignment {
                    entry.assignment =
                        remove_unused_ambient_binders(env.arena(), assignment, removed);
                }
            }
        }

        let spine = (0..scope_len)
            .rev()
            .map(|index| env.arena().bound(index))
            .collect();
        env.arena().alloc(RawNode::Meta {
            metavariable,
            spine,
        })
    }

    pub fn constrain(&mut self, constraint: GoalConstraint) {
        self.constraints.push(ConstraintRecord {
            original: constraint.clone(),
            normalized: constraint,
            status: ConstraintStatus::Residual,
        });
    }

    fn set_principal_for_meta(
        &mut self,
        env: &CrateEnv,
        term: RawExp,
        constraint: &GoalConstraint,
    ) {
        if let RawNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term))
            && self.entries[metavariable.index()].principal.is_none()
        {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
    }

    fn fresh_synthetic(&mut self, env: &CrateEnv, context: &Context, span: SourceSpan) -> RawExp {
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
            .map(|index| env.arena().bound(index))
            .collect();
        env.arena().alloc(RawNode::Meta {
            metavariable: id,
            spine,
        })
    }

    fn set_meta_type(
        &mut self,
        env: &CrateEnv,
        term: RawExp,
        expected: RawExp,
    ) -> Result<(), String> {
        let RawNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term)) else {
            return Ok(());
        };
        let constraint = GoalConstraint::HasType { term, expected };
        if self.entries[metavariable.index()].principal.is_none() {
            self.entries[metavariable.index()].principal = Some(constraint.clone());
        }
        self.constrain(constraint);
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
        term: RawExp,
        context: &Context,
    ) -> Result<RawExp, String> {
        let RawNode::Meta { metavariable, .. } = env.arena().get(self.zonk(env, term)) else {
            return Err("expected metavariable".into());
        };
        if let Some(ty) = self.entries[metavariable.index()].inferred_type {
            return Ok(self.zonk(env, ty));
        }
        let span = self.entries[metavariable.index()].span;
        let ty = self.fresh_synthetic(env, context, span);
        self.entries[metavariable.index()].inferred_type = Some(ty);
        let constraint = GoalConstraint::HasType { term, expected: ty };
        self.entries[metavariable.index()].principal = Some(constraint.clone());
        self.constrain(constraint);
        Ok(ty)
    }

    pub fn check_pts(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        term: RawExp,
        expected: RawExp,
    ) -> Result<(), String> {
        let term = self.zonk(env, term);
        let expected = self.zonk(env, expected);
        if matches!(env.arena().get(term), RawNode::Meta { .. }) {
            return self.set_meta_type(env, term, expected);
        }
        if matches!(env.arena().get(expected), RawNode::Meta { .. }) {
            let inferred = self.infer_pts(env, module, context, term)?;
            self.unify(env, expected, inferred)?;
            return Ok(());
        }
        if let (
            RawNode::Lam { var, ty, body },
            RawNode::Prod {
                ty: expected_ty,
                body: expected_body,
                ..
            },
        ) = (env.arena().get(term), env.arena().get(expected))
        {
            self.unify(env, ty, expected_ty)?;
            context.push(ContextEntry::Pts {
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
        inferred: RawExp,
        expected: RawExp,
    ) -> Result<(), String> {
        let inferred = self.zonk(env, inferred);
        let expected = self.zonk(env, expected);
        if can_weaken_to(env, inferred, expected) {
            return Ok(());
        }
        if let (RawNode::Sort(inferred), RawNode::Sort(expected)) =
            (env.arena().get(inferred), env.arena().get(expected))
            && inferred.can_lift_to(expected)
        {
            return Ok(());
        }
        self.unify(env, expected, inferred).map(|_| ())
    }

    pub fn infer_pts(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        term: RawExp,
    ) -> Result<RawExp, String> {
        let term = self.zonk(env, term);
        if !self.contains_unsolved(env, term) {
            return CheckSession::new(env, module, context)
                .infer_pts(term)
                .map_err(|error| format!("{error:?}"));
        }
        let arena = env.arena();
        match arena.get(term) {
            RawNode::Meta { .. } => self.type_of_meta(env, term, context),
            RawNode::Sort(sort) => sort
                .type_of_sort()
                .map(|sort| arena.sort(sort))
                .ok_or_else(|| "no sort of sort found".into()),
            RawNode::Bound(index) => context
                .len()
                .checked_sub(index + 1)
                .and_then(|position| context.get(position))
                .and_then(|entry| match entry {
                    ContextEntry::Pts { ty, .. } => {
                        Some(shift_bound_indices(arena, *ty, index + 1, 0))
                    }
                    _ => None,
                })
                .ok_or_else(|| "bound variable is not a PTS term".into()),
            RawNode::ModuleParam(parameter) => env
                .module_parameter_opt(parameter)
                .and_then(|parameter| match parameter.kind {
                    ModuleParameterKind::Pts { ty } => Some(ty),
                    _ => None,
                })
                .ok_or_else(|| "module parameter is not a PTS term".into()),
            RawNode::DefinedConstant(definition) => {
                let definition = env.definition(definition);
                (definition.kind == DefinitionKind::Pts)
                    .then_some(definition.ty)
                    .ok_or_else(|| "definition is not a PTS term".into())
            }
            RawNode::IndType {
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
                        kernel::calculus::instantiate_telescope(arena, *expected, &preceding);
                    self.check_pts(env, module, context, argument, expected)?;
                    preceding.push(argument);
                }
                Ok(kernel::calculus::instantiate_telescope(
                    arena,
                    spec.arity(arena),
                    &parameters,
                ))
            }
            RawNode::IndCtor {
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
                        kernel::calculus::instantiate_telescope(arena, *expected, &preceding);
                    self.check_pts(env, module, context, argument, expected)?;
                    preceding.push(argument);
                }
                if idx >= spec.constructor_len() {
                    return Err("constructor index out of bounds".into());
                }
                Ok(kernel::inductive::InductiveTypeSpecs::type_of_constructor(
                    arena, indspec, spec, idx, parameters,
                ))
            }
            RawNode::IndProjection {
                indspec,
                parameters,
                value,
                field,
            } => {
                let spec = env.inductive(indspec);
                if spec.constructor_len() != 1 {
                    return Err("projection target is not a structure".into());
                }
                if parameters.len() != spec.parameters().len() {
                    return Err("structure projection parameter count mismatch".into());
                }
                let mut preceding_parameters = Vec::new();
                for (argument, (_, expected)) in parameters.iter().copied().zip(spec.parameters()) {
                    let expected = instantiate_telescope(arena, *expected, &preceding_parameters);
                    self.check_pts(env, module, context, argument, expected)?;
                    preceding_parameters.push(argument);
                }
                let structure_ty = arena.alloc(RawNode::IndType {
                    indspec,
                    parameters: parameters.clone(),
                });
                self.check_pts(env, module, context, value, structure_ty)?;
                let constructor = spec.constructors()[0].instantiate_parameters(arena, &parameters);
                let Some(CtorBinder::Simple((_, field_ty))) = constructor.telescope.get(field)
                else {
                    return Err("structure projection field out of bounds".into());
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
            RawNode::Prod { var, ty, body } => {
                let domain_sort = self.infer_sort(env, module, context, ty)?;
                context.push(ContextEntry::Pts { var, ty });
                let body_sort = self.infer_sort(env, module, context, body);
                context.pop();
                let body_sort = body_sort?;
                domain_sort
                    .relation_of_sort(body_sort)
                    .map(|sort| arena.sort(sort))
                    .ok_or_else(|| "no sort relation for product".into())
            }
            RawNode::Lam { var, ty, body } => {
                self.infer_sort(env, module, context, ty)?;
                context.push(ContextEntry::Pts { var, ty });
                let body_ty = self.infer_pts(env, module, context, body);
                context.pop();
                Ok(arena.alloc(RawNode::Prod {
                    var,
                    ty,
                    body: body_ty?,
                }))
            }
            RawNode::App { func, arg } => {
                let func_ty = self.infer_pts(env, module, context, func)?;
                let func_ty = self.zonk(env, func_ty);
                let (domain, codomain) = match arena.get(kernel::calculus::whnf(env, func_ty)) {
                    RawNode::Prod { ty, body, .. } => (ty, body),
                    RawNode::Meta { .. } => {
                        let span = meta_span(env, func_ty, &self.entries);
                        let domain = self.fresh_synthetic(env, context, span);
                        let codomain = self.fresh_synthetic(env, context, span);
                        let product = arena.alloc(RawNode::Prod {
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
                Ok(kernel::calculus::instantiate(arena, codomain, arg))
            }
            RawNode::PowerSet { set } => {
                let sort = self.infer_sort(env, module, context, set)?;
                match sort {
                    Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
                    _ => Err("PowerSet carrier is not Set(i)".into()),
                }
            }
            RawNode::SubSet {
                var,
                set,
                predicate,
            } => {
                let sort = self.infer_sort(env, module, context, set)?;
                if !matches!(sort, Sort::Set(_)) {
                    return Err("subset carrier is not Set(i)".into());
                }
                context.push(ContextEntry::Pts { var, ty: set });
                let proposition = arena.sort(Sort::Prop);
                let result = self.check_pts(env, module, context, predicate, proposition);
                context.pop();
                result?;
                Ok(arena.alloc(RawNode::PowerSet { set }))
            }
            RawNode::Pred {
                superset,
                subset,
                element,
            } => {
                self.infer_sort(env, module, context, superset)?;
                let power = arena.alloc(RawNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                self.check_pts(env, module, context, element, superset)?;
                Ok(arena.sort(Sort::Prop))
            }
            RawNode::TypeLift { superset, subset } => {
                let sort = self.infer_sort(env, module, context, superset)?;
                let power = arena.alloc(RawNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                match sort {
                    Sort::Set(level) => Ok(arena.sort(Sort::Set(level))),
                    _ => Err("TypeLift carrier is not Set(i)".into()),
                }
            }
            RawNode::Equal { left, right } => {
                let left_ty = self.infer_pts(env, module, context, left)?;
                let right_ty = self.infer_pts(env, module, context, right)?;
                let left_ty = self.zonk(env, left_ty);
                let right_ty = self.zonk(env, right_ty);
                if common_ambient_carrier(env, left_ty, right_ty).is_none() {
                    self.unify(env, left_ty, right_ty)?;
                }
                Ok(arena.sort(Sort::Prop))
            }
            RawNode::Exists { set } => {
                self.infer_sort(env, module, context, set)?;
                Ok(arena.sort(Sort::Prop))
            }
            RawNode::TakeSet {
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
                let exists = arena.alloc(RawNode::Exists { set: domain });
                self.check_pts(env, module, context, existence, exists)?;
                let shifted_map = shift_bound_indices(arena, map, 2, 0);
                let mapped_left = arena.alloc(RawNode::App {
                    func: shifted_map,
                    arg: arena.bound(1),
                });
                let mapped_right = arena.alloc(RawNode::App {
                    func: shifted_map,
                    arg: arena.bound(0),
                });
                let equality = arena.alloc(RawNode::Equal {
                    left: mapped_left,
                    right: mapped_right,
                });
                let inner = arena.alloc(RawNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: shift_bound_indices(arena, domain, 1, 0),
                    body: equality,
                });
                let uniqueness_ty = arena.alloc(RawNode::Prod {
                    var: SymbolId::ANONYMOUS,
                    ty: domain,
                    body: inner,
                });
                self.check_pts(env, module, context, uniqueness, uniqueness_ty)?;
                Ok(codomain)
            }
            RawNode::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => {
                self.infer_sort(env, module, context, domain)?;
                self.infer_sort(env, module, context, proposition)?;
                let map_ty = nondependent_product(arena, domain, proposition);
                self.check_pts(env, module, context, map, map_ty)?;
                let exists = arena.alloc(RawNode::Exists { set: domain });
                self.check_pts(env, module, context, existence, exists)?;
                Ok(proposition)
            }
            RawNode::RunStep {
                state_ty,
                result_ty,
            } => {
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                Ok(arena.sort(Sort::Set(0)))
            }
            RawNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                self.check_pts(env, module, context, next, state_ty)?;
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
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                self.check_pts(env, module, context, output, result_ty)?;
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
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                let step_ty = set_step_function_type(arena, state_ty, result_ty);
                self.check_pts(env, module, context, step, step_ty)?;
                self.check_pts(env, module, context, state, state_ty)?;
                Ok(arena.sort(Sort::Prop))
            }
            RawNode::Proof { proposition } => {
                if self.infer_sort(env, module, context, proposition)? != Sort::Prop {
                    return Err("Proof argument is not a proposition".into());
                }
                // Provability is a judgement-level obligation collected by
                // the strict kernel after metavariables have been solved.
                Ok(proposition)
            }
            RawNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
            } => {
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                self.check_pts(
                    env,
                    module,
                    context,
                    step,
                    set_step_function_type(arena, state_ty, result_ty),
                )?;
                self.check_pts(env, module, context, initial, state_ty)?;
                Ok(result_ty)
            }
            RawNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => {
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
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
                    transition,
                    arena.alloc(RawNode::RunStep {
                        state_ty,
                        result_ty,
                    }),
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
            } => {
                ensure_set_sort(self.infer_sort(env, module, context, state_ty)?)?;
                ensure_set_sort(self.infer_sort(env, module, context, result_ty)?)?;
                let run_step = arena.alloc(RawNode::RunStep {
                    state_ty,
                    result_ty,
                });
                let motive_ty = self.infer_pts(env, module, context, motive)?;
                let RawNode::Prod {
                    ty: motive_domain, ..
                } = arena.get(self.zonk(env, motive_ty))
                else {
                    return Err("RunStep recursor motive is not a family".into());
                };
                self.unify(env, motive_domain, run_step)?;
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
                self.check_pts(
                    env,
                    module,
                    context,
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
                self.check_pts(
                    env,
                    module,
                    context,
                    on_finish,
                    arena.alloc(RawNode::Prod {
                        var: SymbolId::ANONYMOUS,
                        ty: result_ty,
                        body: finish_result,
                    }),
                )?;
                self.check_pts(env, module, context, scrutinee, run_step)?;
                Ok(arena.alloc(RawNode::App {
                    func: motive,
                    arg: scrutinee,
                }))
            }
            RawNode::BoxType { program_ty } => {
                let mut empty = Vec::new();
                if self
                    .check_value_type(env, module, &mut empty, program_ty)
                    .is_err()
                {
                    self.check_computation_type(env, module, &mut empty, program_ty)?;
                }
                Ok(arena.sort(Sort::Set(0)))
            }
            RawNode::BoxProgram {
                program_ty,
                program,
            } => {
                let mut empty = Vec::new();
                if self
                    .check_value_type(env, module, &mut empty, program_ty)
                    .is_ok()
                {
                    self.check_value(env, module, &mut empty, program, program_ty)?;
                } else {
                    self.check_computation_type(env, module, &mut empty, program_ty)?;
                    self.check_computation(env, module, &mut empty, program, program_ty)?;
                }
                Ok(arena.alloc(RawNode::BoxType { program_ty }))
            }
            RawNode::ForceBox { program_ty, boxed } => {
                self.check_pts(
                    env,
                    module,
                    context,
                    boxed,
                    arena.alloc(RawNode::BoxType { program_ty }),
                )?;
                kernel::reflection::reflect_type(env, self.zonk(env, program_ty))
                    .map_err(|error| format!("cannot reflect boxed Program type: {error}"))
            }
            RawNode::BoxApp { function, argument } => {
                let function_ty = self.infer_pts(env, module, context, function)?;
                let function_ty = self.zonk(env, function_ty);
                let RawNode::BoxType { program_ty } = arena.get(function_ty) else {
                    return Err("boxed application head is not Box(P)".into());
                };
                let RawNode::ComputationFunction { domain, codomain } = arena.get(program_ty)
                else {
                    return Err("boxed application head is not a computation function".into());
                };
                self.check_pts(
                    env,
                    module,
                    context,
                    argument,
                    arena.alloc(RawNode::BoxType { program_ty: domain }),
                )?;
                Ok(arena.alloc(RawNode::BoxType {
                    program_ty: codomain,
                }))
            }
            RawNode::RfType { .. } | RawNode::RfTerm { .. } => {
                Err("RfType and RfTerm were removed; reflection is meta-level".into())
            }
            RawNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                self.infer_sort(env, module, context, superset)?;
                let power = arena.alloc(RawNode::PowerSet { set: superset });
                self.check_pts(env, module, context, subset, power)?;
                self.check_pts(env, module, context, element, superset)?;
                let membership = arena.alloc(RawNode::Pred {
                    superset,
                    subset,
                    element,
                });
                self.check_pts(env, module, context, proof, membership)?;
                Ok(arena.alloc(RawNode::TypeLift { superset, subset }))
            }
            RawNode::ExistsIntro { element, set } => {
                self.check_pts(env, module, context, element, set)?;
                self.infer_sort(env, module, context, set)?;
                Ok(arena.alloc(RawNode::Exists { set }))
            }
            RawNode::SubsetElim {
                element,
                subset,
                superset,
            } => {
                let lifted = arena.alloc(RawNode::TypeLift { superset, subset });
                self.check_pts(env, module, context, element, lifted)?;
                Ok(arena.alloc(RawNode::Pred {
                    superset,
                    subset,
                    element,
                }))
            }
            RawNode::IdRefl { element } => {
                let ty = self.infer_pts(env, module, context, element)?;
                self.infer_sort(env, module, context, ty)?;
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
                self.infer_sort(env, module, context, ty)?;
                self.check_pts(env, module, context, left, ty)?;
                self.check_pts(env, module, context, right, ty)?;
                context.push(ContextEntry::Pts { var, ty });
                let proposition = arena.sort(Sort::Prop);
                let predicate_result = self.check_pts(env, module, context, predicate, proposition);
                context.pop();
                predicate_result?;
                let predicate_function = arena.alloc(RawNode::Lam {
                    var,
                    ty,
                    body: predicate,
                });
                let base_ty = arena.alloc(RawNode::App {
                    func: predicate_function,
                    arg: left,
                });
                self.check_pts(env, module, context, base, base_ty)?;
                let equality_ty = arena.alloc(RawNode::Equal { left, right });
                self.check_pts(env, module, context, equality, equality_ty)?;
                Ok(arena.alloc(RawNode::App {
                    func: predicate_function,
                    arg: right,
                }))
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
                self.check_pts(env, module, context, take, codomain)?;
                self.check_pts(env, module, context, element, domain)?;
                let mapped = arena.alloc(RawNode::App { func, arg: element });
                Ok(arena.alloc(RawNode::Equal {
                    left: take,
                    right: mapped,
                }))
            }
            _ => Err("metavariable inference for this expression is blocked".into()),
        }
    }

    pub fn infer_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        term: RawExp,
    ) -> Result<Sort, String> {
        let term = self.zonk(env, term);
        if !self.contains_unsolved(env, term) {
            return CheckSession::new(env, module, context)
                .infer_sort(term)
                .map_err(|error| format!("{error:?}"));
        }
        if matches!(env.arena().get(term), RawNode::Meta { .. }) {
            let constraint = GoalConstraint::IsSort { term };
            self.set_principal_for_meta(env, term, &constraint);
            self.constrain(constraint);
            return Ok(Sort::Set(0));
        }
        let ty = self.infer_pts(env, module, context, term)?;
        match env.arena().get(self.zonk(env, ty)) {
            RawNode::Sort(sort) => Ok(sort),
            RawNode::Meta { .. } => {
                self.constrain(GoalConstraint::IsSort { term });
                Ok(Sort::Set(0))
            }
            _ => Err("expression does not have a sort".into()),
        }
    }

    pub fn check_value_type(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        ty: RawExp,
    ) -> Result<(), String> {
        let ty = self.zonk(env, ty);
        let arena = env.arena();
        if !self.contains_unsolved(env, ty) {
            return CheckSession::new(env, module, context)
                .check_value_type(ty)
                .map_err(|error| format!("{error:?}"));
        }
        match env.arena().get(ty) {
            RawNode::Meta { .. } => {
                let constraint = GoalConstraint::IsValueType { term: ty };
                self.set_principal_for_meta(env, ty, &constraint);
                self.constrain(constraint);
                Ok(())
            }
            RawNode::Bound(index) => match context.get(context.len().saturating_sub(index + 1)) {
                Some(ContextEntry::ProgramType { .. }) => Ok(()),
                _ => Err("bound variable is not a Program type".into()),
            },
            RawNode::ModuleParam(parameter) => match env.module_parameter_opt(parameter) {
                Some(parameter) if matches!(parameter.kind, ModuleParameterKind::ProgramType) => {
                    Ok(())
                }
                _ => Err("module parameter is not a Program type".into()),
            },
            RawNode::ThunkType { computation_ty } => {
                self.check_computation_type(env, module, context, computation_ty)
            }
            RawNode::RunStep {
                state_ty,
                result_ty,
            } => {
                self.check_value_type(env, module, context, state_ty)?;
                self.check_value_type(env, module, context, result_ty)
            }
            RawNode::ProgramIndType {
                indspec,
                parameters,
            } => {
                if parameters.len() != env.program_inductive(indspec).parameters().len() {
                    return Err("Program datatype parameter count mismatch".into());
                }
                for parameter in parameters {
                    self.check_value_type(env, module, context, parameter)?;
                }
                Ok(())
            }
            RawNode::Prod { var, ty, body } => {
                if matches!(arena.get(ty), RawNode::ValueType) {
                    context.push(ContextEntry::ProgramType { var });
                } else {
                    self.check_value_type(env, module, context, ty)?;
                    context.push(ContextEntry::ProgramValue { var, ty });
                }
                let result = self.check_value_type(env, module, context, body);
                context.pop();
                result
            }
            _ => Err("expression is not a Program value type".into()),
        }
    }

    pub fn check_computation_type(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        ty: RawExp,
    ) -> Result<(), String> {
        let ty = self.zonk(env, ty);
        if !self.contains_unsolved(env, ty) {
            return CheckSession::new(env, module, context)
                .check_computation_type(ty)
                .map_err(|error| format!("{error:?}"));
        }
        match env.arena().get(ty) {
            RawNode::Meta { .. } => {
                let constraint = GoalConstraint::IsComputationType { term: ty };
                self.set_principal_for_meta(env, ty, &constraint);
                self.constrain(constraint);
                Ok(())
            }
            RawNode::ReturnType { value_ty } => {
                self.check_value_type(env, module, context, value_ty)
            }
            RawNode::ComputationFunction { domain, codomain } => {
                self.check_value_type(env, module, context, domain)?;
                self.check_computation_type(env, module, context, codomain)
            }
            _ => Err("expression is not a Program computation type".into()),
        }
    }

    pub fn check_value(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        value: RawExp,
        expected: RawExp,
    ) -> Result<(), String> {
        let value = self.zonk(env, value);
        let expected = self.zonk(env, expected);
        self.check_value_type(env, module, context, expected)?;
        if matches!(env.arena().get(value), RawNode::Meta { .. }) {
            self.set_meta_type(env, value, expected)?;
            self.constrain(GoalConstraint::HasValueType {
                term: value,
                expected,
            });
            return Ok(());
        }
        let inferred = self.infer_value(env, module, context, value)?;
        self.unify(env, inferred, expected)?;
        Ok(())
    }

    pub fn infer_value(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        value: RawExp,
    ) -> Result<RawExp, String> {
        let value = self.zonk(env, value);
        if !self.contains_unsolved(env, value) {
            return CheckSession::new(env, module, context)
                .infer_value(value)
                .map_err(|error| format!("{error:?}"));
        }
        let arena = env.arena();
        match arena.get(value) {
            RawNode::Meta { .. } => self.type_of_meta(env, value, context),
            RawNode::Bound(index) => context
                .len()
                .checked_sub(index + 1)
                .and_then(|position| context.get(position))
                .and_then(|entry| match entry {
                    ContextEntry::ProgramValue { ty, .. } => {
                        Some(shift_bound_indices(arena, *ty, index + 1, 0))
                    }
                    _ => None,
                })
                .ok_or_else(|| "bound variable is not a Program value".into()),
            RawNode::ModuleParam(parameter) => env
                .module_parameter_opt(parameter)
                .and_then(|parameter| match parameter.kind {
                    ModuleParameterKind::ProgramValue { ty } => Some(ty),
                    _ => None,
                })
                .ok_or_else(|| "module parameter is not a Program value".into()),
            RawNode::DefinedConstant(definition) => {
                let definition = env.definition(definition);
                (definition.kind == DefinitionKind::ProgramValue)
                    .then_some(definition.ty)
                    .ok_or_else(|| "definition is not a Program value".into())
            }
            RawNode::Lam { var, ty, body } => {
                if matches!(arena.get(ty), RawNode::ValueType) {
                    context.push(ContextEntry::ProgramType { var });
                } else {
                    self.check_value_type(env, module, context, ty)?;
                    context.push(ContextEntry::ProgramValue { var, ty });
                }
                let body_ty = self.infer_value(env, module, context, body);
                context.pop();
                Ok(arena.alloc(RawNode::Prod {
                    var,
                    ty,
                    body: body_ty?,
                }))
            }
            RawNode::App { func, arg } => {
                let func_ty = self.infer_value(env, module, context, func)?;
                let func_ty = self.zonk(env, func_ty);
                let RawNode::Prod {
                    ty: domain, body, ..
                } = arena.get(kernel::calculus::whnf(env, func_ty))
                else {
                    return Err("Program value application head is not a function".into());
                };
                if matches!(arena.get(domain), RawNode::ValueType) {
                    self.check_value_type(env, module, context, arg)?;
                } else {
                    self.check_value(env, module, context, arg, domain)?;
                }
                Ok(kernel::calculus::instantiate(arena, body, arg))
            }
            RawNode::Thunk { computation } => {
                let computation_ty = self.infer_computation(env, module, context, computation)?;
                Ok(arena.alloc(RawNode::ThunkType { computation_ty }))
            }
            RawNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                self.check_value_type(env, module, context, state_ty)?;
                self.check_value_type(env, module, context, result_ty)?;
                self.check_value(env, module, context, next, state_ty)?;
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
                self.check_value_type(env, module, context, state_ty)?;
                self.check_value_type(env, module, context, result_ty)?;
                self.check_value(env, module, context, output, result_ty)?;
                Ok(arena.alloc(RawNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
            RawNode::ProgramIndCtor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let spec = env.program_inductive(indspec);
                if parameters.len() != spec.parameters().len() {
                    return Err("Program constructor parameter count mismatch".into());
                }
                for parameter in &parameters {
                    self.check_value_type(env, module, context, *parameter)?;
                }
                let constructor = spec
                    .constructors()
                    .get(idx)
                    .ok_or_else(|| "Program constructor index out of bounds".to_string())?;
                let expected_fields = constructor.instantiated_fields(arena, &parameters);
                if fields.len() != expected_fields.len() {
                    return Err("Program constructor field count mismatch".into());
                }
                let mut preceding = Vec::new();
                for (field, (_, expected)) in fields.into_iter().zip(expected_fields) {
                    let expected =
                        kernel::calculus::instantiate_telescope(arena, expected, &preceding);
                    self.check_value(env, module, context, field, expected)?;
                    preceding.push(field);
                }
                Ok(arena.alloc(RawNode::ProgramIndType {
                    indspec,
                    parameters,
                }))
            }
            RawNode::ProgramIndProjection {
                indspec,
                parameters,
                value,
                field,
            } => {
                let spec = env.program_inductive(indspec);
                if spec.constructors().len() != 1 {
                    return Err("Program projection target is not a structure".into());
                }
                if parameters.len() != spec.parameters().len() {
                    return Err("Program projection parameter count mismatch".into());
                }
                for parameter in &parameters {
                    self.check_value_type(env, module, context, *parameter)?;
                }
                let structure_ty = arena.alloc(RawNode::ProgramIndType {
                    indspec,
                    parameters: parameters.clone(),
                });
                self.check_value(env, module, context, value, structure_ty)?;
                let fields = spec.constructors()[0].instantiated_fields(arena, &parameters);
                let (_, field_ty) = fields
                    .get(field)
                    .copied()
                    .ok_or_else(|| "Program projection field out of bounds".to_string())?;
                let preceding = (0..field)
                    .map(|field| {
                        arena.alloc(RawNode::ProgramIndProjection {
                            indspec,
                            parameters: parameters.clone(),
                            value,
                            field,
                        })
                    })
                    .collect::<Vec<_>>();
                Ok(instantiate_telescope(arena, field_ty, &preceding))
            }
            _ => Err("metavariable inference for this Program value is blocked".into()),
        }
    }

    pub fn check_computation(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        computation: RawExp,
        expected: RawExp,
    ) -> Result<(), String> {
        let computation = self.zonk(env, computation);
        let expected = self.zonk(env, expected);
        self.check_computation_type(env, module, context, expected)?;
        if matches!(env.arena().get(computation), RawNode::Meta { .. }) {
            self.set_meta_type(env, computation, expected)?;
            self.constrain(GoalConstraint::HasComputationType {
                term: computation,
                expected,
            });
            return Ok(());
        }
        let inferred = self.infer_computation(env, module, context, computation)?;
        self.unify(env, inferred, expected)?;
        Ok(())
    }

    pub fn infer_computation(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        context: &mut Context,
        computation: RawExp,
    ) -> Result<RawExp, String> {
        let computation = self.zonk(env, computation);
        if !self.contains_unsolved(env, computation) {
            return CheckSession::new(env, module, context)
                .infer_computation(computation)
                .map_err(|error| format!("{error:?}"));
        }
        let arena = env.arena();
        match arena.get(computation) {
            RawNode::Meta { .. } => self.type_of_meta(env, computation, context),
            RawNode::DefinedConstant(definition) => {
                let definition = env.definition(definition);
                (definition.kind == DefinitionKind::ProgramComputation)
                    .then_some(definition.ty)
                    .ok_or_else(|| "definition is not a Program computation".into())
            }
            RawNode::Return { value } => {
                let value_ty = self.infer_value(env, module, context, value)?;
                Ok(arena.alloc(RawNode::ReturnType { value_ty }))
            }
            RawNode::Force { value } => {
                let inferred = self.infer_value(env, module, context, value)?;
                let value_ty = self.zonk(env, inferred);
                match arena.get(value_ty) {
                    RawNode::ThunkType { computation_ty } => Ok(computation_ty),
                    RawNode::Meta { .. } => {
                        let span = meta_span(env, value_ty, &self.entries);
                        let result = self.fresh_synthetic(env, context, span);
                        let thunk = arena.alloc(RawNode::ThunkType {
                            computation_ty: result,
                        });
                        self.unify(env, value_ty, thunk)?;
                        Ok(result)
                    }
                    _ => Err("forced value does not have a thunk type".into()),
                }
            }
            RawNode::ComputationLam {
                var,
                value_ty,
                body,
            } => {
                self.check_value_type(env, module, context, value_ty)?;
                context.push(ContextEntry::ProgramValue { var, ty: value_ty });
                let body_ty = self.infer_computation(env, module, context, body);
                context.pop();
                Ok(arena.alloc(RawNode::ComputationFunction {
                    domain: value_ty,
                    codomain: body_ty?,
                }))
            }
            RawNode::ComputationApp { computation, value } => {
                let inferred = self.infer_computation(env, module, context, computation)?;
                let computation_ty = self.zonk(env, inferred);
                let (domain, codomain) = match arena.get(computation_ty) {
                    RawNode::ComputationFunction { domain, codomain } => (domain, codomain),
                    RawNode::Meta { .. } => {
                        let span = meta_span(env, computation_ty, &self.entries);
                        let domain = self.fresh_synthetic(env, context, span);
                        let codomain = self.fresh_synthetic(env, context, span);
                        let function =
                            arena.alloc(RawNode::ComputationFunction { domain, codomain });
                        self.unify(env, computation_ty, function)?;
                        (domain, codomain)
                    }
                    _ => return Err("computation application head is not a function".into()),
                };
                self.check_value(env, module, context, value, domain)?;
                Ok(codomain)
            }
            RawNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                self.check_value_type(env, module, context, value_ty)?;
                let source = arena.alloc(RawNode::ReturnType { value_ty });
                self.check_computation(env, module, context, computation, source)?;
                context.push(ContextEntry::ProgramValue { var, ty: value_ty });
                let body_ty = self.infer_computation(env, module, context, body);
                context.pop();
                body_ty
            }
            RawNode::ValueLet { var, value, body } => {
                let value_ty = self.infer_value(env, module, context, value)?;
                context.push(ContextEntry::ProgramValue { var, ty: value_ty });
                let body_ty = self.infer_computation(env, module, context, body);
                context.pop();
                body_ty
            }
            RawNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => {
                self.check_value_type(env, module, context, state_ty)?;
                self.check_value_type(env, module, context, result_ty)?;
                let step_ty = step_function_type(arena, state_ty, result_ty);
                self.check_value(env, module, context, step, step_ty)?;
                self.check_value(env, module, context, initial, state_ty)?;
                Ok(arena.alloc(RawNode::ReturnType {
                    value_ty: result_ty,
                }))
            }
            _ => Err("metavariable inference for this Program computation is blocked".into()),
        }
    }

    pub fn constrain_type(&mut self, term: RawExp, expected: RawExp) {
        self.constrain(GoalConstraint::HasType { term, expected });
    }

    pub fn unify(&mut self, env: &CrateEnv, left: RawExp, right: RawExp) -> Result<bool, String> {
        let index = self.constraints.len();
        self.constrain(GoalConstraint::Equal { left, right });
        let result = self.unify_rec(env, left, right, &mut HashSet::new());
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
        left: RawExp,
        right: RawExp,
        visiting: &mut HashSet<(RawExp, RawExp)>,
    ) -> Result<bool, String> {
        let left = self.zonk(env, left);
        let right = self.zonk(env, right);
        if left == right || erased_convertible(env, left, right) {
            return Ok(true);
        }
        if !visiting.insert((left, right)) {
            return Ok(true);
        }
        match (env.arena().get(left), env.arena().get(right)) {
            (
                RawNode::Meta {
                    metavariable,
                    spine: _,
                },
                RawNode::Meta {
                    metavariable: other,
                    ..
                },
            ) if metavariable == other => Ok(true),
            (
                RawNode::Meta {
                    metavariable,
                    spine,
                },
                _,
            ) => self.assign(env, metavariable, spine.len(), right),
            (
                _,
                RawNode::Meta {
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
        value: RawExp,
    ) -> Result<bool, String> {
        if self.occurs(env, metavariable, value, &mut HashSet::new()) {
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
        if let Some(previous) = entry.assignment {
            return self.unify_rec(env, previous, value, &mut HashSet::new());
        }
        self.entries[metavariable.index()].assignment = Some(value);
        Ok(true)
    }

    fn occurs(
        &self,
        env: &CrateEnv,
        needle: MetaVarId,
        exp: RawExp,
        seen: &mut HashSet<RawExp>,
    ) -> bool {
        if !seen.insert(exp) {
            return false;
        }
        match env.arena().get(exp) {
            RawNode::Meta {
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

    pub fn zonk(&self, env: &CrateEnv, exp: RawExp) -> RawExp {
        self.zonk_rec(env, exp, &mut HashMap::new(), &mut HashSet::new())
    }

    fn zonk_rec(
        &self,
        env: &CrateEnv,
        exp: RawExp,
        cache: &mut HashMap<RawExp, RawExp>,
        resolving: &mut HashSet<MetaVarId>,
    ) -> RawExp {
        if let Some(result) = cache.get(&exp) {
            return *result;
        }
        let arena = env.arena();
        let result = match arena.get(exp) {
            RawNode::Meta {
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

    pub fn contains_unsolved(&self, env: &CrateEnv, exp: RawExp) -> bool {
        match env.arena().get(self.zonk(env, exp)) {
            RawNode::Meta { .. } => true,
            node => node_children(node)
                .into_iter()
                .any(|child| self.contains_unsolved(env, child)),
        }
    }

    pub fn finish(&self, env: &CrateEnv) -> Result<(), ElaborationError> {
        let mut implicits = Vec::new();
        let mut goals = Vec::new();
        for (index, entry) in self.entries.iter().enumerate() {
            let id = MetaVarId(index as u32);
            let solved = entry
                .assignment
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
            GoalConstraint::IsValueType { term } => GoalConstraint::IsValueType {
                term: self.zonk(env, *term),
            },
            GoalConstraint::IsComputationType { term } => GoalConstraint::IsComputationType {
                term: self.zonk(env, *term),
            },
            GoalConstraint::HasValueType { term, expected } => GoalConstraint::HasValueType {
                term: self.zonk(env, *term),
                expected: self.zonk(env, *expected),
            },
            GoalConstraint::HasComputationType { term, expected } => {
                GoalConstraint::HasComputationType {
                    term: self.zonk(env, *term),
                    expected: self.zonk(env, *expected),
                }
            }
        }
    }
}

fn constraint_expressions(constraint: &GoalConstraint) -> Vec<RawExp> {
    match constraint {
        GoalConstraint::HasType { term, expected }
        | GoalConstraint::Equal {
            left: term,
            right: expected,
        }
        | GoalConstraint::HasValueType { term, expected }
        | GoalConstraint::HasComputationType { term, expected } => vec![*term, *expected],
        GoalConstraint::IsSort { term }
        | GoalConstraint::IsValueType { term }
        | GoalConstraint::IsComputationType { term } => vec![*term],
    }
}

fn meta_span(env: &CrateEnv, exp: RawExp, entries: &[MetaEntry]) -> SourceSpan {
    match env.arena().get(exp) {
        RawNode::Meta { metavariable, .. } => entries[metavariable.index()].span,
        _ => SourceSpan { start: 0, end: 0 },
    }
}

fn metas_in_constraint(env: &CrateEnv, constraint: &GoalConstraint) -> HashSet<MetaVarId> {
    constraint_expressions(constraint)
        .into_iter()
        .flat_map(|exp| metas_in_exp(env, exp))
        .collect()
}

fn metas_in_exp(env: &CrateEnv, exp: RawExp) -> HashSet<MetaVarId> {
    fn collect(
        env: &CrateEnv,
        exp: RawExp,
        result: &mut HashSet<MetaVarId>,
        seen: &mut HashSet<RawExp>,
    ) {
        if !seen.insert(exp) {
            return;
        }
        match env.arena().get(exp) {
            RawNode::Meta {
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

fn node_children(node: RawNode) -> Vec<RawExp> {
    let mut children = Vec::new();
    let _ = map_children(node, |child| {
        children.push(child);
        child
    });
    children
}

fn rigid_heads_compatible(left: &RawNode, right: &RawNode) -> bool {
    use std::mem::discriminant;
    if discriminant(left) != discriminant(right) {
        return false;
    }
    match (left, right) {
        (RawNode::Sort(left), RawNode::Sort(right)) => left == right,
        (RawNode::Bound(left), RawNode::Bound(right)) => left == right,
        (RawNode::ModuleParam(left), RawNode::ModuleParam(right)) => left == right,
        (RawNode::DefinedConstant(left), RawNode::DefinedConstant(right)) => left == right,
        (RawNode::IndType { indspec: left, .. }, RawNode::IndType { indspec: right, .. }) => {
            left == right
        }
        (
            RawNode::IndCtor {
                indspec: left,
                idx: left_idx,
                ..
            },
            RawNode::IndCtor {
                indspec: right,
                idx: right_idx,
                ..
            },
        ) => left == right && left_idx == right_idx,
        (RawNode::IndElim { indspec: left, .. }, RawNode::IndElim { indspec: right, .. }) => {
            left == right
        }
        (
            RawNode::IndProjection {
                indspec: left,
                field: left_field,
                ..
            },
            RawNode::IndProjection {
                indspec: right,
                field: right_field,
                ..
            },
        ) => left == right && left_field == right_field,
        (
            RawNode::ProgramIndType { indspec: left, .. },
            RawNode::ProgramIndType { indspec: right, .. },
        ) => left == right,
        (
            RawNode::ProgramIndCtor {
                indspec: left,
                idx: left_idx,
                ..
            },
            RawNode::ProgramIndCtor {
                indspec: right,
                idx: right_idx,
                ..
            },
        ) => left == right && left_idx == right_idx,
        (
            RawNode::ProgramIndProjection {
                indspec: left,
                field: left_field,
                ..
            },
            RawNode::ProgramIndProjection {
                indspec: right,
                field: right_field,
                ..
            },
        ) => left == right && left_field == right_field,
        (
            RawNode::ProgramCase { indspec: left, .. },
            RawNode::ProgramCase { indspec: right, .. },
        ) => left == right,
        _ => true,
    }
}

fn nondependent_product(arena: &kernel::exp::Arena, domain: RawExp, codomain: RawExp) -> RawExp {
    arena.alloc(RawNode::Prod {
        var: SymbolId::ANONYMOUS,
        ty: domain,
        body: shift_bound_indices(arena, codomain, 1, 0),
    })
}

fn ensure_set_sort(sort: Sort) -> Result<(), String> {
    if matches!(sort, Sort::Set(_)) {
        Ok(())
    } else {
        Err("Set recursion type must inhabit Set(i)".into())
    }
}

fn set_step_function_type(
    arena: &kernel::exp::Arena,
    state_ty: RawExp,
    result_ty: RawExp,
) -> RawExp {
    let run_step = arena.alloc(RawNode::RunStep {
        state_ty,
        result_ty,
    });
    nondependent_product(arena, state_ty, run_step)
}

fn step_function_type(arena: &kernel::exp::Arena, state_ty: RawExp, result_ty: RawExp) -> RawExp {
    let run_step = arena.alloc(RawNode::RunStep {
        state_ty,
        result_ty,
    });
    let result = arena.alloc(RawNode::ReturnType { value_ty: run_step });
    let function = arena.alloc(RawNode::ComputationFunction {
        domain: state_ty,
        codomain: result,
    });
    arena.alloc(RawNode::ThunkType {
        computation_ty: function,
    })
}
