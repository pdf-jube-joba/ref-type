//! Register declarations in dependency order, including datatype reflections.
use super::*;

impl Lowerer<'_> {
    pub(super) fn definition(&mut self, id: DefId) -> Result<(), String> {
        let mut pending = vec![(id, false)];
        let mut active = HashSet::new();
        while let Some((id, ready)) = pending.pop() {
            if self.kernel.definition(id).is_some() || self.kernel.definition_template(id).is_some()
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
            for dependency in
                raw::dependencies::definition_dependencies(self.raw, self.raw.definition(id))
                    .definitions
                    .into_iter()
                    .rev()
            {
                if self.kernel.definition(dependency).is_none() {
                    pending.push((dependency, false))
                }
            }
        }
        Ok(())
    }

    pub(super) fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
        if self.kernel.definition(id).is_some() || self.kernel.definition_template(id).is_some() {
            return Ok(());
        }
        tracing::debug!(target:"ref_type::lowering",?id,"lower definition");
        let raw = self.raw.definition(id).clone();
        let mut ctx = if matches!(raw, raw::environment::DefinedConstant::Pts { .. }) {
            self.raw.definition_context(id.module)
        } else {
            self.raw.program_reflection_context(id.module)
        };
        let parameters = self.raw.definition_parameters(id).to_vec();
        ctx.extend(parameters.iter().map(|var| ExpContextEntry {
            var: *var,
            ty: self.raw.arena().sort(RawSort::Set(0)),
        }));
        let mut program_context = parameters
            .iter()
            .map(|var| raw::program::ProgramContextEntry::ValueType { var: *var })
            .collect::<Vec<_>>();
        let certificate = match &raw {
            raw::environment::DefinedConstant::ProgramValue {
                certified_reflection,
                ..
            }
            | raw::environment::DefinedConstant::ProgramComputation {
                certified_reflection,
                ..
            } => *certified_reflection,
            _ => None,
        };
        let certified_reflection = certificate
            .map(|e| self.set(e, &mut ctx, id.module)?.try_into())
            .transpose()?;

        let (body, classifier, context) = match raw {
            raw::environment::DefinedConstant::Pts { ty, body } => {
                let classifier = self.classifier(ty, &mut ctx, id.module)?;
                let body = self.set(body, &mut ctx, id.module)?;
                let context = self.context(&ctx, id.module)?;
                (body, classifier, context)
            }
            raw::environment::DefinedConstant::ProgramValue { ty, body, .. } => {
                let ty = self.value_type(ty)?;
                let body = self.value_term(body, &mut program_context)?;
                (
                    body.into(),
                    ty.into(),
                    self.program_context(&program_context)?,
                )
            }
            raw::environment::DefinedConstant::ProgramComputation { ty, body, .. } => {
                let ty = self.computation_type(ty)?;
                let body = self.computation_term(body, &mut program_context)?;
                (
                    body.into(),
                    ty.into(),
                    self.program_context(&program_context)?,
                )
            }
        };
        if !parameters.is_empty() {
            return self.kernel.register_definition_template(
                id,
                ke::Definition {
                    body,
                    classifier,
                    context,
                    certified_reflection,
                },
            );
        }
        self.kernel
            .register_definition(
                id,
                ke::Definition {
                    body,
                    classifier,
                    context,
                    certified_reflection,
                },
            )
            .map_err(|e| format!("indexed definition {id:?}: {e}"))
    }

    pub(super) fn parameter(&mut self, id: ModuleParamId) -> Result<(), String> {
        if self.kernel.parameter(id).is_some() {
            return Ok(());
        }
        let p = self
            .raw
            .module_parameter_opt(id)
            .ok_or("unknown parameter")?
            .clone();
        let mut ctx = self.raw.definition_context(id.module);
        let classifier = match p.kind {
            raw::environment::ModuleParameterKind::Pts { ty } => {
                self.set(ty, &mut ctx, id.module)?
            }
            raw::environment::ModuleParameterKind::ProgramType => self
                .kernel
                .arena()
                .alloc(s::ValueKindNode {
                    level: 0,
                    form: s::ValueKindForm::Base,
                })
                .into(),
            raw::environment::ModuleParameterKind::ProgramValue { ty } => {
                self.value_type(ty)?.into()
            }
        };
        self.kernel.register_parameter(
            id,
            ke::Binding {
                var: p.name,
                classifier,
            },
            vec![],
        )
    }

    pub(super) fn inductive(
        &mut self,
        id: InductiveId,
        m: ModuleId,
        ambient: &ExpContext,
    ) -> Result<(), String> {
        if self.kernel.inductive(id).is_some() || !self.active.insert(id) {
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
                id,
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
        if self.kernel.datatype(id).is_some() {
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
        self.kernel.register_datatype(
            id,
            ke::ProgramDatatype {
                parameters,
                constructors,
                level: 0,
                reflected: raw.reflected(),
            },
        )?;
        self.active_program.remove(&id);
        Ok(())
    }

    pub(crate) fn lower_all(&mut self) -> Result<(), String> {
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
