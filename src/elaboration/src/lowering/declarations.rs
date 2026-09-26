//! Register declarations in dependency order, including datatype reflections.
use super::*;

impl Lowerer<'_> {
    pub(super) fn definition(&mut self, id: DefId) -> Result<(), String> {
        let mut pending = vec![(id, false)];
        let mut active = HashSet::new();
        while let Some((id, ready)) = pending.pop() {
            if self.kernel.definition(id.into()).is_some() {
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
                if self.kernel.definition(dependency.into()).is_none() {
                    pending.push((dependency, false))
                }
            }
        }
        Ok(())
    }

    pub(super) fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
        if self.kernel.definition(id.into()).is_some() {
            return Ok(());
        }
        tracing::debug!(target:"ref_type::lowering",?id,"lower definition");
        let captures = self.captures(Declaration::Definition(id));
        let base = self.raw.definition_context(id.module).len();
        let depth = self.raw.definition_parameters(id).len();
        self.in_scope(captures, base, depth, |this| this.lower_definition(id))
    }

    fn lower_definition(&mut self, id: DefId) -> Result<(), String> {
        let raw = self.raw.definition(id).clone();
        let parameters = self.raw.definition_parameters(id).to_vec();
        let mut program_context = parameters
            .iter()
            .map(|var| raw::program::ProgramContextEntry::ValueType { var: *var })
            .collect::<Vec<_>>();
        let (body, classifier, context) = match raw {
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
        self.kernel
            .register_definition(
                id.into(),
                ke::Definition {
                    body,
                    classifier,
                    context,
                },
            )
            .map_err(|e| format!("indexed definition {id:?}: {e}"))
    }

    pub(super) fn inductive(&mut self, id: InductiveId) -> Result<(), String> {
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
                id.into(),
                ke::InductiveSpec {
                    parameters: native_params,
                    arity,
                    constructors,
                    sort,
                },
            )
            .map_err(|e| format!("indexed inductive {id:?}: {e}"))?;
        Ok(())
    }

    pub(super) fn datatype(&mut self, id: ProgramInductiveId) -> Result<(), String> {
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
        self.inductive(raw.reflected())?;
        self.kernel.register_datatype(
            id.into(),
            ke::ProgramDatatype {
                parameters,
                constructors,
                level: 0,
                reflected: raw.reflected().into(),
            },
        )?;
        Ok(())
    }

    pub(crate) fn lower_all(&mut self) -> Result<(), String> {
        for id in self.raw.parameter_ids() {
            let captures = self.captures(Declaration::Parameter(id));
            self.in_scope(captures, 0, 0, |this| {
                let context = this.capture_context(true)?;
                kernel::check::Checker::new(this.kernel, context).check_context()
            })?;
        }
        for id in self.raw.inductive_ids() {
            self.inductive(id)?
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
