//! Lower CBPV types, terms, and contexts into their kernel families.
use super::*;

impl Lowerer<'_> {
    pub(crate) fn program_type(
        &mut self,
        ty: raw::program::ProgramType,
    ) -> Result<s::ProgramType, String> {
        match ty {
            raw::program::ProgramType::ValueType(t) => Ok(self.value_type(t)?.into()),
            raw::program::ProgramType::ComputationType(t) => Ok(self.computation_type(t)?.into()),
        }
    }

    pub(super) fn value_type(
        &mut self,
        ty: raw::program::ValueType,
    ) -> Result<s::ValueType, String> {
        use raw::program::ValueTypeNode as R;
        use s::ValueTypeForm as F;
        let form = match self.raw.arena().get(ty) {
            R::Bound(index) => F::Bound { index },
            R::ModuleParam(parameter) => {
                self.parameter(parameter)?;
                F::ModuleParam { parameter }
            }
            R::Meta { .. } => return Err("unresolved Program type".into()),
            R::Thunk { computation_ty } => F::Thunk {
                computation_ty: self.computation_type(computation_ty)?,
            },
            R::RunStep {
                state_ty,
                result_ty,
            } => F::RunStep {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
            },
            R::Inductive {
                indspec,
                parameters,
            } => {
                self.datatype(indspec)?;
                F::Inductive {
                    inductive: indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|p| self.value_type(p).map(Into::into))
                        .collect::<Result<_, _>>()?,
                }
            }
        };
        Ok(self
            .kernel
            .arena()
            .alloc(s::ValueTypeNode { level: 0, form }))
    }

    pub(super) fn computation_type(
        &mut self,
        ty: raw::program::ComputationType,
    ) -> Result<s::ComputationType, String> {
        use raw::program::ComputationTypeNode as R;
        use s::ComputationTypeForm as F;
        let form = match self.raw.arena().get(ty) {
            R::Meta { .. } => return Err("unresolved computation type".into()),
            R::Return { value_ty } => F::ReturnType {
                value_ty: self.value_type(value_ty)?,
            },
            R::Function { domain, codomain } => {
                let domain = self.value_type(domain)?;
                let body = self.computation_type(codomain)?;
                let body = kernel::stratified::calculus::shift(self.kernel.arena(), body, 1, 0)?
                    .try_into()
                    .map_err(|e| format!("{e:?}"))?;
                let rule = k::ProductRule::new(
                    k::Sort::Base(k::BaseSort::Value(0)),
                    k::Sort::Base(k::BaseSort::Computation(0)),
                )?;
                F::ProdTerm {
                    var: SymbolId::ANONYMOUS,
                    rule,
                    domain,
                    body,
                }
            }
        };
        Ok(self
            .kernel
            .arena()
            .alloc(s::ComputationTypeNode { level: 0, form }))
    }

    pub(super) fn program_term(
        &mut self,
        p: raw::program::ProgramTerm,
    ) -> Result<s::ProgramTerm, String> {
        self.program_in_context(p, &mut vec![])
    }

    pub(crate) fn program_in_context(
        &mut self,
        p: raw::program::ProgramTerm,
        context: &mut raw::program::ProgramContext,
    ) -> Result<s::ProgramTerm, String> {
        match p {
            raw::program::ProgramTerm::ValueTerm(value) => {
                Ok(self.value_term(value, context)?.into())
            }
            raw::program::ProgramTerm::ComputationTerm(computation) => {
                Ok(self.computation_term(computation, context)?.into())
            }
        }
    }

    pub(crate) fn program_context(
        &mut self,
        context: &raw::program::ProgramContext,
    ) -> Result<ke::Context, String> {
        context
            .iter()
            .map(|b| match b {
                raw::program::ProgramContextEntry::ValueType { var } => Ok(ke::Binding {
                    var: *var,
                    classifier: self
                        .kernel
                        .arena()
                        .alloc(s::ValueKindNode {
                            level: 0,
                            form: s::ValueKindForm::Base,
                        })
                        .into(),
                }),
                raw::program::ProgramContextEntry::ValueTerm { var, ty } => Ok(ke::Binding {
                    var: *var,
                    classifier: self.value_type(*ty)?.into(),
                }),
            })
            .collect()
    }

    pub(super) fn value_term(
        &mut self,
        v: raw::program::ValueTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::ValueTerm, String> {
        use raw::program::ValueTermNode as R;
        use s::ValueTermForm as F;
        let form = match self.raw.arena().get(v) {
            R::Bound(index) => F::Bound { index },
            R::ModuleParam(parameter) => {
                self.parameter(parameter)?;
                F::ModuleParam { parameter }
            }
            R::Meta { .. } => return Err("unresolved Program value".into()),
            R::DefinitionInstance {
                definition,
                parameters,
            } => {
                self.definition(definition)?;
                let raw::environment::DefinedConstant::ProgramValue { body, .. } =
                    self.raw.definition(definition)
                else {
                    return Err("wrong Program definition category".into());
                };
                let body = raw::program_definitions::instantiate_value(
                    self.raw.arena(),
                    *body,
                    &parameters,
                    0,
                );
                return self.value_term(body, ctx);
            }
            R::DefinedConstant(definition) => {
                self.definition(definition)?;
                F::Constant { definition }
            }
            R::Thunk { computation } => F::ThunkValue {
                computation: self.computation_term(computation, ctx)?,
            },
            R::Continue {
                state_ty,
                result_ty,
                next,
            } => F::Continue {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                next: self.value_term(next, ctx)?,
            },
            R::Finish {
                state_ty,
                result_ty,
                output,
            } => F::Finish {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                output: self.value_term(output, ctx)?,
            },
            R::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                self.datatype(indspec)?;
                F::InductiveConstructor {
                    inductive: indspec,
                    constructor: idx,
                    parameters: parameters
                        .into_iter()
                        .map(|p| self.value_type(p).map(Into::into))
                        .collect::<Result<_, _>>()?,
                    fields: fields
                        .into_iter()
                        .map(|v| self.value_term(v, ctx))
                        .collect::<Result<_, _>>()?,
                }
            }
        };
        Ok(self
            .kernel
            .arena()
            .alloc(s::ValueTermNode { level: 0, form }))
    }

    pub(super) fn computation_term(
        &mut self,
        e: raw::program::ComputationTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::ComputationTerm, String> {
        use raw::program::{ComputationTermNode as R, ProgramContextEntry};
        use s::ComputationTermForm as F;
        let form = match self.raw.arena().get(e) {
            R::Meta { .. } => return Err("unresolved computation".into()),
            R::DefinitionInstance {
                definition,
                parameters,
            } => {
                self.definition(definition)?;
                let raw::environment::DefinedConstant::ProgramComputation { body, .. } =
                    self.raw.definition(definition)
                else {
                    return Err("wrong Program definition category".into());
                };
                let body = raw::program_definitions::instantiate_computation(
                    self.raw.arena(),
                    *body,
                    &parameters,
                    0,
                );
                return self.computation_term(body, ctx);
            }
            R::DefinedConstant(definition) => {
                self.definition(definition)?;
                F::Constant { definition }
            }
            R::Return { value } => F::Return {
                value: self.value_term(value, ctx)?,
            },
            R::Force { value } => F::Force {
                value: self.value_term(value, ctx)?,
            },
            R::Lambda {
                var,
                value_ty,
                body,
            } => {
                let domain = self.value_type(value_ty)?;
                ctx.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.computation_term(body, ctx);
                ctx.pop();
                F::LambdaTerm {
                    rule: k::ProductRule::new(
                        k::Sort::Base(k::BaseSort::Value(0)),
                        k::Sort::Base(k::BaseSort::Computation(0)),
                    )?,
                    var,
                    domain,
                    body: body?,
                }
            }
            R::Application { computation, value } => F::AppTerm {
                rule: k::ProductRule::new(
                    k::Sort::Base(k::BaseSort::Value(0)),
                    k::Sort::Base(k::BaseSort::Computation(0)),
                )?,
                function: self.computation_term(computation, ctx)?,
                argument: self.value_term(value, ctx)?,
            },
            R::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let computation = self.computation_term(computation, ctx)?;
                ctx.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.computation_term(body, ctx);
                ctx.pop();
                F::Sequence {
                    var,
                    value_ty: self.value_type(value_ty)?,
                    computation,
                    body: body?,
                }
            }
            R::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let value = self.value_term(value, ctx)?;
                ctx.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body = self.computation_term(body, ctx);
                ctx.pop();
                F::ValueLet {
                    var,
                    value_ty: self.value_type(value_ty)?,
                    value,
                    body: body?,
                }
            }
            R::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => F::Run {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                step: self.value_term(step, ctx)?,
                initial: self.value_term(initial, ctx)?,
            },
            R::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => F::RunCase {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                step: self.value_term(step, ctx)?,
                initial: self.value_term(initial, ctx)?,
                transition: self.computation_term(transition, ctx)?,
            },
            R::Case {
                indspec,
                scrutinee,
                branches,
            } => {
                self.datatype(indspec)?;
                let mut checker = raw::program_derivation::ProgramCheckSession::new(self.raw, ctx);
                let ty = checker
                    .infer_computation_term(e)
                    .map_err(|e| format!("case inference: {e:?}"))?;
                let scrutinee_ty = checker
                    .infer_value_term(scrutinee)
                    .map_err(|e| format!("case inference: {e:?}"))?;
                let raw::program::ValueTypeNode::Inductive { parameters, .. } =
                    self.raw.arena().get(scrutinee_ty)
                else {
                    return Err("case scrutinee type".into());
                };
                let binders = branches.iter().map(|b| b.binders.clone()).collect();
                let spec = self.raw.program_inductive(indspec);
                let mut bodies = vec![];
                for (branch, ctor) in branches.into_iter().zip(spec.constructors()) {
                    let mut local = ctx.clone();
                    for (j, ((_, field), var)) in ctor
                        .instantiated_fields(self.raw.arena(), &parameters)
                        .into_iter()
                        .zip(&branch.binders)
                        .enumerate()
                    {
                        local.push(ProgramContextEntry::ValueTerm {
                            var: *var,
                            ty: raw::program_calculus::shift_value_type_indices(
                                self.raw.arena(),
                                field,
                                j,
                                0,
                            ),
                        });
                    }
                    bodies.push(self.computation_term(branch.body, &mut local)?);
                }
                F::Case {
                    inductive: indspec,
                    binders,
                    result_ty: self.computation_type(ty)?,
                    scrutinee: self.value_term(scrutinee, ctx)?,
                    branches: bodies,
                }
            }
        };
        Ok(self
            .kernel
            .arena()
            .alloc(s::ComputationTermNode { level: 0, form }))
    }
}
