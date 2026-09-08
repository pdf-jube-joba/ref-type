//! Register declarations in dependency order, including datatype reflections.
use super::*;

impl Lowerer<'_> {
    pub(super) fn definition(&mut self, id: DefId) -> Result<(), String> {
        let mut pending = vec![(id, false)];
        let mut active = HashSet::new();
        while let Some((id, ready)) = pending.pop() {
            if self.kernel.definition(id).is_some() {
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
            for dependency in definition_dependencies(self.raw, id).into_iter().rev() {
                if self.kernel.definition(dependency).is_none() {
                    pending.push((dependency, false))
                }
            }
        }
        Ok(())
    }

    pub(super) fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
        if self.kernel.definition(id).is_some() {
            return Ok(());
        }
        tracing::debug!(target:"ref_type::lowering",?id,"lower definition");
        let raw = self.raw.definition(id).clone();
        let mut ctx = self.raw.definition_context(id.module);
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
                let body = self.value_term(body, &mut vec![])?;
                (body.into(), ty.into(), vec![])
            }
            raw::environment::DefinedConstant::ProgramComputation { ty, body, .. } => {
                let ty = self.computation_type(ty)?;
                let body = self.computation_term(body, &mut vec![])?;
                (body.into(), ty.into(), vec![])
            }
        };
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
        let ctx = self.raw.definition_context(id.module);
        let classifier = match p.kind {
            raw::environment::ModuleParameterKind::Pts { ty } => {
                self.set(ty, &mut ctx.clone(), id.module)?
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

// Materialized modules need not store declarations in dependency order. Schedule
// the dependency graph explicitly so a long import chain does not consume the
// Rust call stack while classifying syntax.
fn definition_dependencies(raw: &raw::environment::CrateEnv, id: DefId) -> Vec<DefId> {
    use raw::program::{
        ComputationTermNode as C, ComputationTypeNode as CT, ValueTermNode as V,
        ValueTypeNode as VT,
    };
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum E {
        Set(Exp),
        Vt(raw::program::ValueType),
        Ct(raw::program::ComputationType),
        V(raw::program::ValueTerm),
        C(raw::program::ComputationTerm),
    }

    fn ty(t: raw::program::ProgramType) -> E {
        match t {
            raw::program::ProgramType::ValueType(x) => E::Vt(x),
            raw::program::ProgramType::ComputationType(x) => E::Ct(x),
        }
    }

    fn term(t: raw::program::ProgramTerm) -> E {
        match t {
            raw::program::ProgramTerm::ValueTerm(x) => E::V(x),
            raw::program::ProgramTerm::ComputationTerm(x) => E::C(x),
        }
    }
    let mut stack = match raw.definition(id) {
        raw::environment::DefinedConstant::Pts { ty, body } => vec![E::Set(*ty), E::Set(*body)],
        raw::environment::DefinedConstant::ProgramValue {
            ty,
            body,
            certified_reflection,
        } => {
            let mut s = vec![E::Vt(*ty), E::V(*body)];
            s.extend(certified_reflection.map(E::Set));
            s
        }
        raw::environment::DefinedConstant::ProgramComputation {
            ty,
            body,
            certified_reflection,
        } => {
            let mut s = vec![E::Ct(*ty), E::C(*body)];
            s.extend(certified_reflection.map(E::Set));
            s
        }
    };
    let mut visited = HashSet::new();
    let mut definitions = HashSet::new();
    while let Some(e) = stack.pop() {
        if !visited.insert(e) {
            continue;
        }
        match e {
            E::Set(x) => {
                let node = raw.arena().get(x);
                match &node {
                    ExpNode::DefinedConstant(id) => {
                        definitions.insert(*id);
                    }
                    ExpNode::BoxType { program_ty } | ExpNode::ForceBox { program_ty, .. } => {
                        stack.push(ty(*program_ty))
                    }
                    ExpNode::BoxProgram {
                        program_ty,
                        program,
                        ..
                    } => {
                        stack.push(ty(*program_ty));
                        stack.push(term(*program));
                    }
                    _ => {}
                }
                raw::calculus::map_children(node, |e| {
                    stack.push(E::Set(e));
                    e
                });
            }
            E::Vt(x) => match raw.arena().get(x) {
                VT::Thunk { computation_ty } => stack.push(E::Ct(computation_ty)),
                VT::RunStep {
                    state_ty,
                    result_ty,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty)]),
                VT::Inductive { parameters, .. } => stack.extend(parameters.into_iter().map(E::Vt)),
                _ => {}
            },
            E::Ct(x) => match raw.arena().get(x) {
                CT::Return { value_ty } => stack.push(E::Vt(value_ty)),
                CT::Function { domain, codomain } => stack.extend([E::Vt(domain), E::Ct(codomain)]),
                _ => {}
            },
            E::V(x) => match raw.arena().get(x) {
                V::DefinedConstant(id) => {
                    definitions.insert(id);
                }
                V::Thunk { computation } => stack.push(E::C(computation)),
                V::Continue {
                    state_ty,
                    result_ty,
                    next,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(next)]),
                V::Finish {
                    state_ty,
                    result_ty,
                    output,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(output)]),
                V::InductiveConstructor {
                    parameters, fields, ..
                } => {
                    stack.extend(parameters.into_iter().map(E::Vt));
                    stack.extend(fields.into_iter().map(E::V));
                }
                _ => {}
            },
            E::C(x) => match raw.arena().get(x) {
                C::DefinedConstant(id) => {
                    definitions.insert(id);
                }
                C::Return { value } | C::Force { value } => stack.push(E::V(value)),
                C::Lambda { value_ty, body, .. } => stack.extend([E::Vt(value_ty), E::C(body)]),
                C::Application { computation, value } => {
                    stack.extend([E::C(computation), E::V(value)])
                }
                C::Sequence {
                    value_ty,
                    computation,
                    body,
                    ..
                } => stack.extend([E::Vt(value_ty), E::C(computation), E::C(body)]),
                C::ValueLet {
                    value_ty,
                    value,
                    body,
                    ..
                } => stack.extend([E::Vt(value_ty), E::V(value), E::C(body)]),
                C::Case {
                    scrutinee,
                    branches,
                    ..
                } => {
                    stack.push(E::V(scrutinee));
                    stack.extend(branches.into_iter().map(|b| E::C(b.body)));
                }
                C::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                } => stack.extend([E::Vt(state_ty), E::Vt(result_ty), E::V(step), E::V(initial)]),
                C::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                } => stack.extend([
                    E::Vt(state_ty),
                    E::Vt(result_ty),
                    E::V(step),
                    E::V(initial),
                    E::C(transition),
                ]),
                _ => {}
            },
        }
    }
    let mut definitions = definitions.into_iter().collect::<Vec<_>>();
    definitions.sort_by_key(|id| (id.module.0, id.index));
    definitions
}
