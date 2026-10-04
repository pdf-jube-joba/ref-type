//! Program surface holes use the kernel's shared contextual solver.
use super::*;
use kernel::metavariables::Outcome;
use kernel::{
    sort::{BaseSort, Sort},
    syntax::{Expression, Node},
};
fn expression(term: Term) -> Expression {
    match term {
        Term::Logical(e) => e.0,
        Term::ValueType(e) => e.0,
        Term::ComputationType(e) => e.0,
        Term::Value(e) => e.0,
        Term::Computation(e) => e.0,
    }
}
fn view(category: MetaCategory, e: Expression) -> Term {
    match category {
        MetaCategory::ValueType => Term::ValueType(ValueType(e)),
        MetaCategory::ComputationType => Term::ComputationType(ComputationType(e)),
        MetaCategory::ValueTerm => Term::Value(ValueTerm(e)),
        MetaCategory::ComputationTerm => Term::Computation(ComputationTerm(e)),
    }
}
fn category(term: Term) -> MetaCategory {
    match term {
        Term::ValueType(_) => MetaCategory::ValueType,
        Term::ComputationType(_) => MetaCategory::ComputationType,
        Term::Value(_) => MetaCategory::ValueTerm,
        Term::Computation(_) => MetaCategory::ComputationTerm,
        _ => unreachable!(),
    }
}
fn category_code(c: MetaCategory) -> u8 {
    match c {
        MetaCategory::ValueType => 1,
        MetaCategory::ComputationType => 2,
        MetaCategory::ValueTerm => 3,
        MetaCategory::ComputationTerm => 4,
    }
}
fn context_symbol(entry: &ProgramContextEntry) -> SymbolId {
    match entry {
        ProgramContextEntry::ValueType { var } | ProgramContextEntry::ValueTerm { var, .. } => *var,
    }
}
fn spine(arena: &Arena, context: &ProgramContext) -> Vec<ProgramArgument> {
    context
        .iter()
        .enumerate()
        .map(|(position, entry)| {
            let index = context.len() - position - 1;
            match entry {
                ProgramContextEntry::ValueType { .. } => {
                    ProgramArgument::ValueType(arena.value_type_bound(index))
                }
                ProgramContextEntry::ValueTerm { .. } => {
                    ProgramArgument::ValueTerm(arena.value_bound(index))
                }
            }
        })
        .collect()
}
#[cfg(test)]
fn argument_term(argument: ProgramArgument) -> Term {
    match argument {
        ProgramArgument::ValueType(ty) => Term::ValueType(ty),
        ProgramArgument::ValueTerm(value) => Term::Value(value),
    }
}
fn occurrence(arena: &Arena, term: Term) -> Option<(MetaVarId, Vec<ProgramArgument>)> {
    match term {
        Term::ValueType(ty) => match arena.get(ty) {
            ValueTypeNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::ComputationType(ty) => match arena.get(ty) {
            ComputationTypeNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Value(value) => match arena.get(value) {
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Computation(value) => match arena.get(value) {
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Logical(_) => None,
    }
}
fn print_term(printer: &Printer<'_>, term: Term) -> String {
    match term {
        Term::Logical(term) => printer.format_exp(term),
        Term::ValueType(ty) => printer.format_value_type(ty),
        Term::ComputationType(ty) => printer.format_computation_type(ty),
        Term::Value(value) => printer.format_value(value),
        Term::Computation(value) => printer.format_computation(value),
    }
}

impl ProgramScope {
    fn sync(&mut self, environment: &GlobalEnvironment) {
        let arena = environment.crate_env.arena();
        let mut inferred = HashMap::new();
        for (id, entry) in self.core.entries() {
            if let Some(&source) = self.ids.get(&id)
                && let Some(ty) = entry.expected
                && let Node::Meta { id: ty_id, .. } = arena.core.get(ty)
            {
                let cat = match self.metas[source.index()].category {
                    MetaCategory::ValueTerm => MetaCategory::ValueType,
                    MetaCategory::ComputationTerm => MetaCategory::ComputationType,
                    _ => continue,
                };
                inferred.insert(ty_id, cat);
            }
        }
        for (id, entry) in self.core.entries() {
            let source = if let Some(&source) = self.ids.get(&id) {
                source
            } else {
                let source = MetaVarId(self.metas.len() as u32);
                self.ids.insert(id, source);
                self.core_ids.push(id);
                let cat = inferred
                    .get(&id)
                    .copied()
                    .unwrap_or(MetaCategory::ValueType);
                let context = entry
                    .context
                    .iter()
                    .map(|b| {
                        if matches!(
                            arena.core.get(b.ty),
                            Node::Sort(Sort::Base(BaseSort::Value(_)))
                        ) {
                            ProgramContextEntry::ValueType { var: b.var }
                        } else {
                            ProgramContextEntry::ValueTerm {
                                var: b.var,
                                ty: ValueType(b.ty),
                            }
                        }
                    })
                    .collect();
                self.metas.push(ProgramMeta {
                    flavor: MetaFlavor::Synthetic,
                    span: SourceSpan::default(),
                    occurrences: vec![],
                    category: cat,
                    context,
                    solution: None,
                    expected: None,
                });
                source
            };
            if self.core_ids[source.index()] != id {
                continue;
            }
            let meta = &mut self.metas[source.index()];
            arena.bind_program_meta(
                source,
                id,
                category_code(meta.category),
                meta.context
                    .iter()
                    .map(|b| matches!(b, ProgramContextEntry::ValueType { .. }))
                    .collect(),
            );
            meta.solution = entry.assignment.map(|e| view(meta.category, e));
            meta.expected = match meta.category {
                MetaCategory::ValueTerm => entry.expected.map(|e| Term::ValueType(ValueType(e))),
                MetaCategory::ComputationTerm => entry
                    .expected
                    .map(|e| Term::ComputationType(ComputationType(e))),
                _ => None,
            };
        }
    }
    pub(super) fn fresh_meta(
        &mut self,
        environment: &GlobalEnvironment,
        flavor: SurfaceMeta,
        span: SourceSpan,
        category: MetaCategory,
    ) -> Result<(MetaVarId, Vec<ProgramArgument>), String> {
        let env = &environment.crate_env;
        let arena = env.arena();
        let arguments = spine(arena, &self.context);
        if let SurfaceMeta::Named(number) = flavor
            && let Some(source) = self.named_metas.get(&number).copied()
        {
            let existing = &mut self.metas[source.index()];
            if existing.category != category {
                return Err(format!("metavariable _{number} has incompatible uses"));
            }
            let common = existing
                .context
                .iter()
                .zip(&self.context)
                .take_while(|(a, b)| context_symbol(a) == context_symbol(b))
                .count();
            if common < existing.context.len() {
                let term = self
                    .core
                    .restrict(&env.kernel.borrow(), self.core_ids[source.index()], common)
                    .map_err(|e| e.to_string())?;
                let Node::Meta { id, .. } = arena.core.get(term) else {
                    unreachable!()
                };
                self.core_ids[source.index()] = id;
                self.ids.insert(id, source);
                existing.context.truncate(common);
            }
            existing.occurrences.push(span);
            self.sync(environment);
            return Ok((source, arguments.into_iter().take(common).collect()));
        }
        let term = crate::kernel_bridge::program(env, &self.context, &[], |env, context, _| {
            let expected = match category {
                MetaCategory::ValueType => Some(env.arena().sort(Sort::Base(BaseSort::Value(0)))),
                MetaCategory::ComputationType => {
                    Some(env.arena().sort(Sort::Base(BaseSort::Computation(0))))
                }
                _ => None,
            };
            Ok(self.core.fresh(env.arena(), context, expected))
        })?;
        let Node::Meta { id, .. } = arena.core.get(term) else {
            unreachable!()
        };
        let source = MetaVarId(self.metas.len() as u32);
        self.core
            .set_origin(id, kernel::metavariables::OriginId(source.index() as u64))
            .map_err(|e| e.to_string())?;
        self.core_ids.push(id);
        self.ids.insert(id, source);
        self.metas.push(ProgramMeta {
            flavor: flavor.into(),
            span,
            occurrences: vec![span],
            category,
            context: self.context.clone(),
            solution: None,
            expected: None,
        });
        if let SurfaceMeta::Named(n) = flavor {
            self.named_metas.insert(n, source);
        }
        self.sync(environment);
        Ok((source, arguments))
    }
    fn zonk_term(&self, environment: &GlobalEnvironment, term: Term) -> Term {
        let env = &environment.crate_env;
        fn walk(scope: &ProgramScope, arena: &kernel::syntax::Arena, e: Expression) -> Expression {
            if let Node::Meta { id, .. } = arena.get(e)
                && scope.core.entry(id).is_ok()
            {
                scope
                    .core
                    .zonk(arena, e)
                    .expect("consistent Program meta context")
            } else {
                arena
                    .map_children(e, |e, _| {
                        Ok::<_, std::convert::Infallible>(walk(scope, arena, e))
                    })
                    .unwrap()
            }
        }
        view(
            category(term),
            walk(self, &env.arena().core, expression(term)),
        )
    }
    pub(super) fn unify_terms(
        &mut self,
        environment: &GlobalEnvironment,
        left: Term,
        right: Term,
    ) -> Result<(), String> {
        let index = self.record_constraint(environment, ProgramConstraint::Equal(left, right));
        let result = crate::kernel_bridge::program(
            &environment.crate_env,
            &self.context,
            &[left, right],
            |env, context, terms| self.core.unify(env, &context, terms[0], terms[1]),
        );
        self.constraints[index].status = match result {
            Ok(Outcome::Solved) => ConstraintStatus::Discharged,
            Ok(Outcome::Blocked) => ConstraintStatus::Blocked,
            Err(_) => ConstraintStatus::Failed,
        };
        self.sync(environment);
        result.map(|_| ())
    }
    #[cfg(test)]
    fn assign(
        &mut self,
        environment: &GlobalEnvironment,
        id: MetaVarId,
        arguments: &[ProgramArgument],
        value: Term,
    ) -> Result<(), String> {
        let e = environment.crate_env.arena().core.alloc(Node::Meta {
            id: self.core_ids[id.index()],
            arguments: arguments
                .iter()
                .map(|&a| expression(argument_term(a)))
                .collect(),
        });
        self.unify_terms(environment, view(self.metas[id.index()].category, e), value)
    }
    fn solve(
        &mut self,
        environment: &GlobalEnvironment,
        context: &ProgramContext,
        term: Term,
        expected: Term,
    ) -> Result<(), String> {
        self.record_constraint(environment, ProgramConstraint::HasType(term, expected));
        let result = crate::kernel_bridge::program(
            &environment.crate_env,
            context,
            &[term, expected],
            |env, context, terms| {
                self.core
                    .check(env, context, terms[0], terms[1])
                    .map(|_| ())
            },
        );
        self.sync(environment);
        result
    }
    fn solve_value(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        term: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        self.solve(
            environment,
            context,
            Term::Value(term),
            Term::ValueType(expected),
        )
    }
    fn solve_computation(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        term: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        self.solve(
            environment,
            context,
            Term::Computation(term),
            Term::ComputationType(expected),
        )
    }
    fn infer(
        &mut self,
        environment: &GlobalEnvironment,
        context: &ProgramContext,
        term: Term,
    ) -> Result<Expression, String> {
        let result = crate::kernel_bridge::program(
            &environment.crate_env,
            context,
            &[term],
            |env, context, terms| self.core.infer(env, context, terms[0]),
        );
        self.sync(environment);
        result
    }
    pub(super) fn check_value_type_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        ty: ValueType,
    ) -> Result<(), ElaborationError> {
        self.infer(environment, &self.context.clone(), Term::ValueType(ty))
            .map(|_| ())
            .map_err(|error| self.solver_error(environment, error))
    }

    pub(super) fn infer_value_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        term: ValueTerm,
    ) -> Result<ValueType, String> {
        self.infer(environment, context, Term::Value(term))
            .map(ValueType)
    }
    pub(super) fn infer_computation_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        term: ComputationTerm,
    ) -> Result<ComputationType, String> {
        self.infer(environment, context, Term::Computation(term))
            .map(ComputationType)
    }
    pub(super) fn finish_program_metas(
        &mut self,
        environment: &GlobalEnvironment,
    ) -> Result<(), ElaborationError> {
        let result = self.core.finish(&environment.crate_env.kernel.borrow());
        self.sync(environment);
        let goals = self.goals(environment);
        match result {
            Ok(()) if goals.is_empty() => Ok(()),
            Ok(()) => Err(ElaborationError::Metavariables(goals)),
            Err(kernel::metavariables::Error::Unresolved { .. }) if !goals.is_empty() => {
                Err(ElaborationError::Metavariables(goals))
            }
            Err(e) => Err(self.solver_error(
                environment,
                crate::lowering::format_kernel_error(&environment.crate_env, &e),
            )),
        }
    }
    pub(super) fn infer_kernel_value(
        &self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        ProgramCheckSession::new(&environment.crate_env, context)
            .infer_value_term(value)
            .map_err(|error| format!("cannot infer Program value: {error}"))
    }
    pub(crate) fn check_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(ValueTerm, ValueType), ElaborationError> {
        let mut context = self.context.clone();
        self.solve_value(environment, &mut context, value, expected)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, expected),
        ))
    }
    pub(crate) fn check_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(ComputationTerm, ComputationType), ElaborationError> {
        let mut context = self.context.clone();
        self.solve_computation(environment, &mut context, computation, expected)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, expected),
        ))
    }
    pub(crate) fn infer_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> Result<(ValueTerm, ValueType), ElaborationError> {
        let mut context = self.context.clone();
        let ty = self
            .infer_value_term(environment, &mut context, value)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, ty),
        ))
    }
    pub(crate) fn infer_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
    ) -> Result<(ComputationTerm, ComputationType), ElaborationError> {
        let mut context = self.context.clone();
        let ty = self
            .infer_computation_term(environment, &mut context, computation)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, ty),
        ))
    }
    fn record_constraint(
        &mut self,
        environment: &GlobalEnvironment,
        constraint: ProgramConstraint,
    ) -> usize {
        let mut origins = self.origins.clone();
        let (left, right) = match constraint {
            ProgramConstraint::Equal(a, b) | ProgramConstraint::HasType(a, b) => (a, b),
        };
        for id in metas(environment.crate_env.arena(), left)
            .into_iter()
            .chain(metas(environment.crate_env.arena(), right))
        {
            origins.extend(self.metas[id.index()].occurrences.iter().copied());
        }
        origins.sort_by_key(|span| (span.start, span.end));
        origins.dedup();
        let index = self.constraints.len();
        self.constraints.push(ProgramConstraintRecord {
            constraint,
            status: ConstraintStatus::Residual,
            origins,
        });
        index
    }
    fn constraint_diagnostic(
        &self,
        environment: &GlobalEnvironment,
        record: &ProgramConstraintRecord,
    ) -> ConstraintDiagnostic {
        let names = |id: MetaVarId| {
            self.metas.get(id.index()).map_or_else(
                || format!("_pts{}", id.index()),
                |meta| meta.flavor.display_name(id),
            )
        };
        let printer = Printer::new(&environment.crate_env, &names);
        let (left, relation, right) = match record.constraint {
            ProgramConstraint::Equal(left, right) => (left, "≡", right),
            ProgramConstraint::HasType(left, right) => (left, ":", right),
        };
        let render = |a, b| {
            format!(
                "{} {relation} {}",
                print_term(&printer, a),
                print_term(&printer, b)
            )
        };
        ConstraintDiagnostic {
            original: render(left, right),
            normalized: render(
                self.zonk_term(environment, left),
                self.zonk_term(environment, right),
            ),
            status: record.status,
            origins: record.origins.clone(),
        }
    }
    fn goals(&self, environment: &GlobalEnvironment) -> Vec<MetaGoal> {
        let compact = std::env::var("REF_TYPE_COMPACT_DIAGNOSTICS").as_deref() == Ok("1");
        let arena = environment.crate_env.arena();
        let names = |id: MetaVarId| {
            self.metas.get(id.index()).map_or_else(
                || format!("_pts{}", id.index()),
                |meta| meta.flavor.display_name(id),
            )
        };
        let printer = Printer::new(&environment.crate_env, &names);
        self.metas
            .iter()
            .enumerate()
            .filter_map(|(index, meta)| {
                if meta.flavor == MetaFlavor::Synthetic {
                    let entry = self.core.entry(self.core_ids[index]).ok()?;
                    if entry.assignment.is_some() {
                        return None;
                    }
                    let id = MetaVarId(index as u32);
                    let format = |e| {
                        crate::lowering::diagnostics::format_expression(
                            &environment.crate_env,
                            &entry.context,
                            e,
                        )
                    };
                    return Some(MetaGoal {
                        metavariable: id,
                        flavor: meta.flavor,
                        span: meta.span,
                        occurrences: meta.occurrences.clone(),
                        context: entry
                            .context
                            .iter()
                            .map(|b| {
                                format!("{}: {}", environment.crate_env.symbol(b.var), format(b.ty))
                            })
                            .collect::<Vec<_>>()
                            .join(", "),
                        principal: entry
                            .expected
                            .map(|ty| format!("{} : {}", names(id), format(ty))),
                        solution: None,
                        state: MetaState::InsufficientInformation,
                        dependencies: vec![],
                        constraints: vec![],
                    });
                }
                let id = MetaVarId(index as u32);
                let solution = meta.solution.map(|term| self.zonk_term(environment, term));
                let solved = solution.is_some_and(|term| metas(arena, term).is_empty());
                if meta.flavor == MetaFlavor::Synthetic
                    || (solved && meta.flavor != MetaFlavor::Goal)
                {
                    return None;
                }
                let expected = meta.expected.map(|term| self.zonk_term(environment, term));
                let mut dependencies: Vec<_> = expected
                    .into_iter()
                    .chain(solution)
                    .flat_map(|term| metas(arena, term))
                    .filter(|other| *other != id)
                    .collect();
                dependencies.sort_by_key(|id| id.0);
                dependencies.dedup();
                let state = if solved {
                    MetaState::Solved
                } else if dependencies.is_empty() {
                    MetaState::InsufficientInformation
                } else {
                    MetaState::Waiting
                };
                let local_context = meta
                    .context
                    .iter()
                    .map(|entry| match entry {
                        ProgramContextEntry::ValueType { var } => {
                            format!("{}: \\VType", environment.crate_env.symbol(*var))
                        }
                        ProgramContextEntry::ValueTerm { var, ty } => format!(
                            "{}: {}",
                            environment.crate_env.symbol(*var),
                            printer.format_value_type(self.zonk_value_type(environment, *ty))
                        ),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut module_context = Vec::new();
                let mut module = Some(environment.module_manager.current());
                while let Some(id) = module {
                    let current = environment.crate_env.module(id);
                    for parameter in current.parameters() {
                        let name = environment.crate_env.symbol(parameter.name);
                        let ty = match parameter.kind {
                            crate::raw::environment::ModuleParameterKind::ProgramType => {
                                "\\VType".to_string()
                            }
                            crate::raw::environment::ModuleParameterKind::ProgramValue { ty } => {
                                printer.format_value_type(ty)
                            }
                            crate::raw::environment::ModuleParameterKind::Pts { ty } => {
                                printer.format_exp(ty)
                            }
                        };
                        module_context.push(format!("{name}: {ty}"));
                    }
                    module = current.parent();
                }
                if !local_context.is_empty() {
                    module_context.push(local_context);
                }
                let context = module_context.join(", ");
                let expected =
                    expected.map(|term| print_term(&printer, term)).or_else(|| {
                        match meta.category {
                            MetaCategory::ValueType => Some("\\VType".into()),
                            MetaCategory::ComputationType => Some("\\CType".into()),
                            _ => None,
                        }
                    });
                Some(MetaGoal {
                    metavariable: id,
                    flavor: meta.flavor,
                    span: meta.span,
                    occurrences: meta.occurrences.clone(),
                    context,
                    principal: expected.map(|expected| format!("{} : {expected}", names(id))),
                    solution: solution.map(|term| print_term(&printer, term)),
                    state,
                    dependencies,
                    constraints: self
                        .constraints
                        .iter()
                        .filter(|_| !compact)
                        .filter(|record| {
                            record
                                .origins
                                .iter()
                                .any(|span| meta.occurrences.contains(span))
                        })
                        .map(|record| self.constraint_diagnostic(environment, record))
                        .collect(),
                })
            })
            .collect()
    }
    fn solver_error(&self, environment: &GlobalEnvironment, message: String) -> ElaborationError {
        if std::env::var("REF_TYPE_COMPACT_DIAGNOSTICS").as_deref() == Ok("1") {
            return ElaborationError::Message(message);
        }
        let mut goals = self.goals(environment);
        let state = if self
            .constraints
            .iter()
            .any(|record| record.status == ConstraintStatus::Failed)
        {
            MetaState::Contradiction
        } else {
            MetaState::Unsupported
        };
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
                .map(|record| self.constraint_diagnostic(environment, record))
                .collect(),
            goals,
        }
    }
    pub(super) fn zonk_value_type(
        &self,
        environment: &GlobalEnvironment,
        value: ValueType,
    ) -> ValueType {
        let Term::ValueType(value) = self.zonk_term(environment, Term::ValueType(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_computation_type(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationType,
    ) -> ComputationType {
        let Term::ComputationType(value) =
            self.zonk_term(environment, Term::ComputationType(value))
        else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_value(
        &self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> ValueTerm {
        let Term::Value(value) = self.zonk_term(environment, Term::Value(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_computation(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationTerm,
    ) -> ComputationTerm {
        let Term::Computation(value) = self.zonk_term(environment, Term::Computation(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn resolve_value_type_head(
        &self,
        environment: &GlobalEnvironment,
        value: ValueType,
    ) -> ValueType {
        self.zonk_value_type(environment, value)
    }
    pub(super) fn resolve_computation_type_head(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationType,
    ) -> ComputationType {
        self.zonk_computation_type(environment, value)
    }
}
pub(super) fn metas(arena: &Arena, term: Term) -> HashSet<MetaVarId> {
    let mut result = HashSet::new();
    term.walk(arena, 0, &mut |term, _| {
        if let Some((id, _)) = occurrence(arena, term) {
            result.insert(id);
        }
        None
    });
    result
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_solution_is_rebased_between_sibling_contexts() {
        let mut environment = GlobalEnvironment::default();
        let a = environment.crate_env.intern("A");
        let x = environment.crate_env.intern("x");
        let y = environment.crate_env.intern("y");
        let mut scope = ProgramScope::new();
        scope.push_type(a);
        scope.push_value(x, environment.crate_env.arena().value_type_bound(0));
        let (id, first_spine) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan { start: 1, end: 3 },
                MetaCategory::ValueType,
            )
            .unwrap();
        scope
            .assign(
                &environment,
                id,
                &first_spine,
                Term::ValueType(environment.crate_env.arena().value_type_bound(1)),
            )
            .unwrap();
        scope.truncate(1);
        scope.push_value(y, environment.crate_env.arena().value_type_bound(0));
        let (same, second_spine) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan { start: 8, end: 10 },
                MetaCategory::ValueType,
            )
            .unwrap();
        assert_eq!(id, same);
        assert_eq!(scope.metas[id.index()].context.len(), 1);
        let occurrence = environment.crate_env.arena().alloc(ValueTypeNode::Meta {
            metavariable: id,
            spine: second_spine,
        });
        assert!(matches!(
            environment
                .crate_env
                .arena()
                .get(scope.zonk_value_type(&environment, occurrence)),
            ValueTypeNode::Bound(1)
        ));
    }

    #[test]
    fn a_solution_cannot_capture_a_sibling_type_binder() {
        let mut environment = GlobalEnvironment::default();
        let a = environment.crate_env.intern("A");
        let b = environment.crate_env.intern("B");
        let mut scope = ProgramScope::new();
        scope.push_type(a);
        let (id, arguments) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan::default(),
                MetaCategory::ValueType,
            )
            .unwrap();
        scope
            .assign(
                &environment,
                id,
                &arguments,
                Term::ValueType(environment.crate_env.arena().value_type_bound(0)),
            )
            .unwrap();
        scope.truncate(0);
        scope.push_type(b);
        let error = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan::default(),
                MetaCategory::ValueType,
            )
            .unwrap_err();
        assert!(error.contains("outside its shared context"), "{error}");
    }
}
