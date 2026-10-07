//! Register declarations in dependency order, including datatype reflections.
use super::*;

impl Lowerer<'_> {
    pub(super) fn definition(&mut self, id: DefId) -> Result<(), String> {
        let mut pending = vec![(id, false)];
        let mut active = FxHashSet::default();
        while let Some((id, ready)) = pending.pop() {
            if self
                .raw
                .kernel_definitions
                .borrow()
                .get(&id)
                .is_some_and(|&id| self.kernel.definition(id).is_ok())
            {
                continue;
            }
            if ready {
                self.definition_ready(id)?;
                active.remove(&id);
                continue;
            }
            if !active.insert(id) {
                return Err("cyclic definition dependency".into());
            }
            pending.push((id, true));
            for dependency in self.definition_dependencies(id).into_iter().rev() {
                if self
                    .raw
                    .kernel_definitions
                    .borrow()
                    .get(&dependency)
                    .is_none_or(|&id| self.kernel.definition(id).is_err())
                {
                    pending.push((dependency, false))
                }
            }
        }
        Ok(())
    }

    pub(super) fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
        if self
            .raw
            .kernel_definitions
            .borrow()
            .get(&id)
            .is_some_and(|&id| self.kernel.definition(id).is_ok())
        {
            return Ok(());
        }
        tracing::debug!(target:"ref_type::lowering",?id,"lower definition");
        let _phase = std::env::var_os("REF_TYPE_PROFILE_PHASES").map(|_| {
            crate::profiling::Phase::start(format!(
                "lowering.definition:{}",
                raw::printing::definition_name(self.raw, id)
            ))
        });
        let captures = self.captures(Declaration::Definition(id));
        let base = self.raw.definition_context(id.module).len();
        let depth = self.raw.definition_parameters(id).len();
        let open = self.definition_ambient(id)?;
        self.in_scope(captures, if open > 0 { 0 } else { base }, depth, |this| {
            this.lower_definition(id)
        })
    }

    fn lower_definition(&mut self, id: DefId) -> Result<(), String> {
        let mut timer =
            crate::elaborator::profiling::ProfileTimer::start("REF_TYPE_PROFILE_LOWERING", || {
                raw::printing::definition_name(self.raw, id)
            });
        let raw = self.raw.definition(id).clone();
        let parameters = self.raw.definition_parameters(id).to_vec();
        let mut program_context = self.raw.program_definition_context(id.module);
        program_context.extend(
            parameters
                .iter()
                .map(|var| raw::program::ProgramContextEntry::ValueType { var: *var }),
        );
        self.scope.program_depth = program_context.len();
        let (body, classifier, context) = match raw {
            raw::environment::DefinedConstant::Contextual {
                parameters,
                ty,
                body,
            } => {
                let mut ctx = self.raw.definition_context(id.module);
                ctx.extend(
                    parameters
                        .into_iter()
                        .map(|(var, ty)| ExpContextEntry { var, ty }),
                );
                let classifier = self.classifier(ty, &mut ctx, id.module)?;
                let body = self.set(body, &mut ctx, id.module)?;
                let context = self.context(&ctx, id.module)?;
                (body, classifier, context)
            }
            raw::environment::DefinedConstant::Pts { ty, body } => {
                let mut ctx = self.raw.definition_context(id.module);
                ctx.extend(parameters.iter().map(|var| ExpContextEntry {
                    var: *var,
                    ty: self.raw.arena().sort(raw::sort::Sort::Set(0)),
                }));
                let classifier = self.classifier(ty, &mut ctx, id.module)?;
                let body = self.set(body, &mut ctx, id.module)?;
                let context = self.context(&ctx, id.module)?;
                (body, classifier, context)
            }
            raw::environment::DefinedConstant::ProgramValue { ty, body, .. } => {
                let ty = self.value_type(ty)?;
                let body = self.value_term(body, &mut program_context)?;
                (body, ty, self.program_context(&program_context)?)
            }
            raw::environment::DefinedConstant::ProgramComputation { ty, body, .. } => {
                let ty = self.computation_type(ty)?;
                let body = self.computation_term(body, &mut program_context)?;
                (body, ty, self.program_context(&program_context)?)
            }
        };
        if let Some(timer) = &mut timer {
            timer.checkpoint("lower terms");
        }
        let kernel_id = self
            .kernel
            .register_definition(
                &mut self.metas,
                ke::Definition {
                    body,
                    ty: classifier,
                    context,
                },
            )
            .map_err(|e| {
                format!(
                    "definition {}: {}",
                    raw::printing::definition_name(self.raw, id),
                    super::diagnostics::format_error(self.raw, &e)
                )
            })?;
        if let Some(timer) = &mut timer {
            timer.checkpoint("kernel registration");
        }
        // An open specialization captures local binders. Reify its body rather
        // than a bare frontend name so later substitutions can see those binders.
        let source = (self.definition_ambient(id)? == 0).then_some(id);
        self.raw.arena().bind_definition(
            kernel_id,
            source,
            matches!(
                self.raw.definition(id),
                raw::environment::DefinedConstant::Contextual { .. }
            ),
            self.scope.captures.clone(),
            self.kernel
                .definition(kernel_id)
                .map_err(|e| e.to_string())?
                .body,
        );
        if let Some(reflected) = self.kernel.reflected_definition(kernel_id) {
            self.raw.arena().bind_definition(
                reflected,
                None,
                false,
                self.scope.captures.clone(),
                self.kernel
                    .definition(reflected)
                    .map_err(|e| e.to_string())?
                    .body,
            );
        }
        self.raw
            .kernel_definitions
            .borrow_mut()
            .insert(id, kernel_id);
        Ok(())
    }

    pub(super) fn inductive(&mut self, id: InductiveId) -> Result<(), String> {
        if let Some(origin) = self.raw.inductive_specialization(id)
            && !self.raw.is_program_mirror(id)
        {
            return self.inductive(origin.source);
        }

        if self.kernel.inductive(id.into()).is_some() || !self.active.insert(id) {
            return Ok(());
        }
        let captures = self.captures(Declaration::Inductive(id));
        let ambient = self.raw.definition_context(id.module);
        let result = self.in_scope(captures, ambient.len(), 0, |this| {
            this.lower_inductive(id, ambient)
        });
        self.active.remove(&id);
        result
    }

    fn lower_inductive(&mut self, id: InductiveId, mut ctx: ExpContext) -> Result<(), String> {
        let m = id.module;
        let raw = self.raw.inductive(id).clone();
        let parameters = raw
            .parameters()
            .iter()
            .map(|(var, ty)| ExpContextEntry { var: *var, ty: *ty })
            .collect::<ExpContext>();
        let mut native_params = self.capture_context(false)?;
        for b in &parameters {
            let classifier = self.set(b.ty, &mut ctx, m)?;
            native_params.push(ke::Binding {
                var: b.var,
                ty: classifier,
            });
            ctx.push(b.clone())
        }
        let arity = raw.arity(self.raw.arena());
        let sort = Self::sort(raw.sort());
        let arity = if sort.is_upper() {
            self.logical_base_kind(sort.base())?
        } else {
            self.set(arity, &mut ctx, m)?
        };
        let args = (0..parameters.len())
            .rev()
            .map(|i| self.raw.arena().exp_bound(i))
            .collect();
        let this = self.raw.arena().alloc(ExpNode::IndType {
            indspec: id,
            parameters: args,
        });
        let mut constructors = vec![];
        for ctor in raw.constructors() {
            constructors.push(self.set(
                ctor.as_exp_with_type(self.raw.arena(), this),
                &mut ctx,
                m,
            )?)
        }
        self.kernel
            .register_inductive(
                id.into(),
                ke::InductiveSpec {
                    parameters: native_params,
                    arity,
                    constructors,
                    sort,
                },
            )
            .map_err(|e| {
                format!(
                    "inductive {}: {}",
                    raw::printing::inductive_name(self.raw, id, None),
                    super::diagnostics::format_error(self.raw, &e)
                )
            })?;
        self.raw
            .arena()
            .inductive_captures
            .borrow_mut()
            .insert(id.into(), (self.scope.captures.clone(), parameters.len()));
        Ok(())
    }

    pub(super) fn datatype(&mut self, id: ProgramInductiveId) -> Result<(), String> {
        if self.structural && !self.raw.has_program_inductive(id) {
            return Ok(());
        }
        if self.kernel.datatype(id.into()).is_some() {
            return Ok(());
        }
        // Recursive fields are lowered while the datatype's identity is reserved.
        if !self.active_program.insert(id) {
            return Ok(());
        }
        let captures = self.captures(Declaration::Datatype(id));
        let depth = self.raw.program_inductive(id).parameters().len();
        let result = self.in_scope(captures, 0, depth, |this| this.lower_datatype(id));
        self.active_program.remove(&id);
        result
    }

    fn lower_datatype(&mut self, id: ProgramInductiveId) -> Result<(), String> {
        let raw = self.raw.program_inductive(id).clone();
        let mut parameters = self.capture_context(true)?;
        for &var in raw.parameters() {
            let classifier = self
                .kernel
                .arena()
                .sort(k::Sort::Base(k::BaseSort::Value(0)));
            parameters.push(ke::Binding {
                var,
                ty: classifier,
            })
        }
        let mut constructors = vec![];
        for ctor in raw.constructors() {
            let mut fields = vec![];
            for &(var, ty) in ctor.fields() {
                fields.push(ke::Binding {
                    var,
                    ty: self.value_type(ty)?,
                })
            }
            constructors.push(fields)
        }
        self.inductive(raw.reflected())?;
        self.kernel
            .register_datatype(
                id.into(),
                ke::Datatype {
                    parameters,
                    constructors,
                    level: 0,
                    reflected: raw.reflected().into(),
                },
            )
            .map_err(|error| super::diagnostics::format_error(self.raw, &error))?;
        self.raw
            .arena()
            .datatype_reflections
            .borrow_mut()
            .insert(id.into(), raw.reflected().into());
        Ok(())
    }

    pub(crate) fn lower_all(&mut self) -> Result<(), String> {
        let _phase = crate::profiling::Phase::start("lowering.all");
        let parameters = crate::profiling::Phase::start("lowering.parameters");
        for id in self.raw.parameter_ids() {
            let captures = self.captures(Declaration::Parameter(id));
            self.in_scope(captures, 0, 0, |this| {
                let context = this.capture_context(true)?;
                kernel::check::Checker::new(this.kernel, &mut this.metas, context)
                    .check_context()
                    .map_err(|error| super::diagnostics::format_error(this.raw, &error))
            })?;
        }
        drop(parameters);
        let inductives = crate::profiling::Phase::start("lowering.inductives");
        for id in self.raw.inductive_ids() {
            self.inductive(id)?
        }
        drop(inductives);
        let datatypes = crate::profiling::Phase::start("lowering.datatypes");
        for id in self.raw.datatype_ids() {
            self.datatype(id)?
        }
        drop(datatypes);
        let _definitions = crate::profiling::Phase::start("lowering.definitions");
        for id in self.raw.definition_ids() {
            self.definition(id)?
        }
        Ok(())
    }
}
