//! Register declarations in dependency order, including datatype reflections.
use super::*;

impl Lowerer<'_> {
    pub(super) fn definition(&mut self, id: DefId) -> Result<(), String> {
        let mut pending = vec![(id, false)];
        let mut active = HashSet::new();
        while let Some((id, ready)) = pending.pop() {
            if self.checked_definition(id).is_some() {
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
            for dependency in
                crate::dependencies::definition_dependencies(self.raw, self.raw.definition(id))
                    .definitions
                    .into_iter()
                    .rev()
            {
                if self.checked_definition(dependency).is_none() {
                    pending.push((dependency, false))
                }
            }
        }
        Ok(())
    }

    pub(super) fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
        if self.checked_definition(id).is_some() {
            return Ok(());
        }
        tracing::debug!(target:"ref_type::lowering",?id,"lower definition");
        let raw = self.raw.definition(id).clone();
        let parameters = self.raw.definition_parameters(id).to_vec();
        let mut program_context = parameters
            .iter()
            .map(|var| crate::program::ProgramContextEntry::ValueType { var: *var })
            .collect::<Vec<_>>();
        let (body, classifier, context) = match raw {
            crate::environment::DefinedConstant::Pts { ty, body } => {
                let mut ctx = self.raw.definition_context(id.module);
                ctx.extend(parameters.iter().map(|var| ExpContextEntry {
                    var: *var,
                    ty: self.raw.arena().sort(crate::sort::Sort::Set(0)),
                }));
                let classifier = self.classifier(ty, &mut ctx, id.module)?;
                let body = self.set(body, &mut ctx, id.module)?;
                let context = self.context(&ctx, id.module)?;
                (body, classifier, context)
            }
            crate::environment::DefinedConstant::ProgramValue { ty, body, .. } => {
                let ty = self.value_type(ty)?;
                let body = self.value_term(body, &mut program_context)?;
                (
                    body.into(),
                    ty.into(),
                    self.program_context(&program_context)?,
                )
            }
            crate::environment::DefinedConstant::ProgramComputation { ty, body, .. } => {
                let ty = self.computation_type(ty)?;
                let body = self.computation_term(body, &mut program_context)?;
                (
                    body.into(),
                    ty.into(),
                    self.program_context(&program_context)?,
                )
            }
        };
        let kernel_id = self.definition_id(id);
        let closed = kernel::calculus::is_closed(self.kernel.arena(), body)
            && match classifier {
                ke::Classifier::Expression(ty) => {
                    kernel::calculus::is_closed(self.kernel.arena(), ty)
                }
                ke::Classifier::Upper(_) => true,
            };
        if !parameters.is_empty() || !closed {
            return self.kernel.register_definition_template(
                kernel_id,
                ke::Definition {
                    body,
                    classifier,
                    context,
                },
            );
        }
        self.kernel
            .register_definition(
                kernel_id,
                ke::Definition {
                    body,
                    classifier,
                    context,
                },
            )
            .map_err(|e| format!("indexed definition {id:?}: {e}"))
    }

    pub(super) fn parameter(&mut self, id: ModuleParamId) -> Result<(), String> {
        if self.ids.parameters.contains_key(&id) {
            return Ok(());
        }
        let p = self
            .raw
            .module_parameter_opt(id)
            .ok_or("unknown parameter")?
            .clone();
        let mut ctx = self.raw.definition_context(id.module);
        let classifier = match p.kind {
            crate::environment::ModuleParameterKind::Pts { ty } => {
                self.set(ty, &mut ctx, id.module)?
            }
            crate::environment::ModuleParameterKind::ProgramType => self
                .kernel
                .arena()
                .alloc(s::ValueKindNode {
                    level: 0,
                    form: s::ValueKindForm::Base,
                })
                .into(),
            crate::environment::ModuleParameterKind::ProgramValue { ty } => {
                self.value_type(ty)?.into()
            }
        };
        let level = self.kernel.push_binding(ke::Binding {
            var: p.name,
            classifier,
        })?;
        self.ids.parameters.insert(id, level);
        Ok(())
    }

    pub(super) fn inductive(
        &mut self,
        id: InductiveId,
        m: ModuleId,
        ambient: &ExpContext,
    ) -> Result<(), String> {
        let kernel_id = self.inductive_id(id);
        if self.kernel.inductive(kernel_id).is_some() || !self.active.insert(id) {
            return Ok(());
        }
        let raw = self.raw.inductive(id).clone();
        let mut ctx = ambient.clone();
        let parameters = raw
            .parameters()
            .iter()
            .map(|(var, ty)| ExpContextEntry { var: *var, ty: *ty })
            .collect::<ExpContext>();
        let mut native_params = vec![];
        for b in &parameters {
            let classifier = self.set(b.ty, &mut ctx, m)?;
            native_params.push(ke::Binding {
                var: b.var,
                classifier,
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
                kernel_id,
                ke::InductiveSpec {
                    parameters: native_params,
                    arity,
                    constructors,
                    sort,
                },
            )
            .map_err(|e| format!("indexed inductive {id:?}: {e}"))?;
        self.active.remove(&id);
        Ok(())
    }

    pub(super) fn datatype(&mut self, id: ProgramInductiveId) -> Result<(), String> {
        let kernel_id = self.datatype_id(id);
        if self.kernel.datatype(kernel_id).is_some() {
            return Ok(());
        }
        // Recursive fields are lowered while the datatype's identity is reserved.
        if !self.active_program.insert(id) {
            return Ok(());
        }
        let raw = self.raw.program_inductive(id).clone();
        let mut parameters = vec![];
        for &var in raw.parameters() {
            let classifier = self
                .kernel
                .arena()
                .alloc(s::ValueKindNode {
                    level: 0,
                    form: s::ValueKindForm::Base,
                })
                .into();
            parameters.push(ke::Binding { var, classifier })
        }
        let mut constructors = vec![];
        for ctor in raw.constructors() {
            let mut fields = vec![];
            for &(var, ty) in ctor.fields() {
                fields.push((var, self.value_type(ty)?))
            }
            constructors.push(fields)
        }
        self.inductive(
            raw.reflected(),
            id.module,
            &self.raw.definition_context(id.module),
        )?;
        let reflected = self.inductive_id(raw.reflected());
        self.kernel.register_datatype(
            kernel_id,
            ke::ProgramDatatype {
                parameters,
                constructors,
                level: 0,
                reflected,
            },
        )?;
        self.active_program.remove(&id);
        Ok(())
    }

    pub fn lower_all(&mut self) -> Result<(), String> {
        for id in self.raw.parameter_ids() {
            self.parameter(id)?
        }
        for id in self.raw.inductive_ids() {
            self.inductive(id, id.module, &self.raw.definition_context(id.module))?
        }
        for id in self.raw.datatype_ids() {
            self.datatype(id)?
        }
        for id in self.raw.definition_ids() {
            self.definition(id)?
        }
        Ok(())
    }
}
