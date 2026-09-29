//! Resolve Program source views and proof reflection into shared kernel terms.
use super::*;

impl Lowerer<'_> {
    pub(crate) fn source_term(
        &mut self,
        term: raw::traversal::Term,
        context: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        use raw::traversal::Term;
        self.scope.program_depth = context.len();
        self.scope.program_context = true;
        match term {
            Term::ValueType(e) => self.value_type(e),
            Term::ComputationType(e) => self.computation_type(e),
            Term::Value(e) => self.value_term(e, context),
            Term::Computation(e) => self.computation_term(e, context),
            Term::Logical(e) => self.set(e, &mut vec![], self.raw.root_module()),
        }
    }
    fn program_meta(
        &mut self,
        term: s::Expression,
        arguments: Vec<raw::program::ProgramArgument>,
    ) -> Result<s::Node, String> {
        let s::Node::Meta { id, .. } = self.raw.arena().core.get(term) else {
            unreachable!()
        };
        let arguments = arguments
            .into_iter()
            .map(|a| match a {
                raw::program::ProgramArgument::ValueType(e) => self.value_type(e),
                raw::program::ProgramArgument::ValueTerm(e) => self.value_term(e, &mut vec![]),
            })
            .collect::<Result<_, _>>()?;
        Ok(s::Node::Meta { id, arguments })
    }
    pub(crate) fn program_type(
        &mut self,
        ty: raw::program::ProgramType,
    ) -> Result<s::Expression, String> {
        match ty {
            raw::program::ProgramType::ValueType(t) => Ok(self.value_type(t)?),
            raw::program::ProgramType::ComputationType(t) => Ok(self.computation_type(t)?),
        }
    }

    pub(super) fn value_type(
        &mut self,
        ty: raw::program::ValueType,
    ) -> Result<s::Expression, String> {
        use raw::program::ValueTypeNode as R;
        use s::Node as F;
        if self.native_reference(ty.0) {
            return Ok(ty.0);
        }
        let form = match self.raw.arena().get(ty) {
            R::Bound(index) => F::Bound(index),
            R::ModuleParam(parameter) => {
                if self.scope.nominal {
                    return self.nominal_parameter(parameter);
                }
                F::Bound(self.parameter_index(parameter, self.scope.program_depth)?)
            }
            R::Meta { spine, .. } => self.program_meta(ty.0, spine)?,
            R::Thunk { computation_ty } => F::Thunk {
                computation_ty: self.computation_type(computation_ty)?,
            },
            R::RunStep {
                state_ty,
                result_ty,
            } => F::ProgramRunStep {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
            },
            R::Inductive {
                indspec,
                parameters,
            } => {
                self.datatype(indspec)?;
                F::Inductive {
                    inductive: indspec.into(),
                    parameters: self.datatype_arguments(indspec, parameters)?,
                }
            }
        };
        Ok(self.kernel.arena().alloc(form))
    }

    pub(super) fn computation_type(
        &mut self,
        ty: raw::program::ComputationType,
    ) -> Result<s::Expression, String> {
        use raw::program::ComputationTypeNode as R;
        use s::Node as F;
        let form = match self.raw.arena().get(ty) {
            R::Meta { spine, .. } => self.program_meta(ty.0, spine)?,
            R::Return { value_ty } => F::ReturnType {
                value_ty: self.value_type(value_ty)?,
            },
            R::Function { domain, codomain } => {
                let domain = self.value_type(domain)?;
                let body = self.computation_type(codomain)?;
                let body = kernel::calculus::shift(self.kernel.arena(), body, 1, 0)?;
                F::Product {
                    var: SymbolId::ANONYMOUS,
                    domain,
                    body,
                }
            }
        };
        Ok(self.kernel.arena().alloc(form))
    }

    pub(crate) fn program_in_context(
        &mut self,
        p: raw::program::ProgramTerm,
        context: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        match p {
            raw::program::ProgramTerm::ValueTerm(value) => {
                Ok(self.value_term(value, context)?)
            }
            raw::program::ProgramTerm::ComputationTerm(computation) => {
                Ok(self.computation_term(computation, context)?)
            }
        }
    }

    pub(crate) fn program_context(
        &mut self,
        context: &raw::program::ProgramContext,
    ) -> Result<ke::Context, String> {
        let mut result = self.capture_context(true)?;
        for (depth, binding) in context.iter().enumerate() {
            let previous = std::mem::replace(&mut self.scope.program_depth, depth);
            let binding = match binding {
                raw::program::ProgramContextEntry::ValueType { var } => ke::Binding {
                    var: *var,
                    ty: self
                        .kernel
                        .arena()
                        .sort(k::Sort::Base(k::BaseSort::Value(0))),
                },
                raw::program::ProgramContextEntry::ValueTerm { var, ty } => ke::Binding {
                    var: *var,
                    ty: self.value_type(*ty)?,
                },
            };
            self.scope.program_depth = previous;
            result.push(binding);
        }
        Ok(result)
    }

    fn datatype_arguments(
        &mut self,
        id: ProgramInductiveId,
        parameters: Vec<raw::program::ValueType>,
    ) -> Result<Vec<s::Expression>, String> {
        let captures = if self.structural && !self.raw.has_program_inductive(id) {
            vec![]
        } else {
            self.captures(Declaration::Datatype(id))
        };
        let arguments = self.capture_arguments(&captures, self.scope.program_depth, true)?;
        let mut arguments = arguments;
        arguments.extend(
            parameters
                .into_iter()
                .map(|p| self.value_type(p))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok(arguments)
    }

    pub(super) fn value_term(
        &mut self,
        v: raw::program::ValueTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        let previous_mode = std::mem::replace(&mut self.scope.program_context, true);
        let depth = std::mem::replace(&mut self.scope.program_depth, ctx.len());
        let result = self.value_term_inner(v, ctx);
        self.scope.program_depth = depth;
        self.scope.program_context = previous_mode;
        result
    }

    fn value_term_inner(
        &mut self,
        v: raw::program::ValueTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        use raw::program::ValueTermNode as R;
        use s::Node as F;
        if self.native_reference(v.0) {
            return Ok(v.0);
        }
        let form = match self.raw.arena().get(v) {
            R::Bound(index) => F::Bound(index),
            R::ModuleParam(parameter) => {
                if self.scope.nominal {
                    return self.nominal_parameter(parameter);
                }
                F::Bound(self.parameter_index(parameter, self.scope.program_depth)?)
            }
            R::Meta { spine, .. } => self.program_meta(v.0, spine)?,
            R::DefinitionInstance {
                definition,
                parameters,
            } => {
                self.definition(definition)?;
                let captures = self.captures(Declaration::Definition(definition));
                let mut arguments = self.capture_arguments(&captures, ctx.len(), true)?;
                for parameter in parameters {
                    arguments.push(self.value_type(parameter)?);
                }
                let id = self
                    .raw
                    .kernel_definitions
                    .borrow()
                    .get(&definition)
                    .copied()
                    .ok_or("unknown definition")?;
                return self.kernel.reference(id, arguments);
            }
            R::DefinedConstant(definition) => {
                return self.definition_expression(definition, ctx.len(), true);
            }
            R::Thunk { computation } => F::ThunkValue {
                computation: self.computation_term(computation, ctx)?,
            },
            R::Continue {
                state_ty,
                result_ty,
                next,
            } => F::ProgramContinue {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                next: self.value_term(next, ctx)?,
            },
            R::Finish {
                state_ty,
                result_ty,
                output,
            } => F::ProgramFinish {
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
                    inductive: indspec.into(),
                    constructor: idx,
                    parameters: self.datatype_arguments(indspec, parameters)?,
                    fields: fields
                        .into_iter()
                        .map(|v| self.value_term(v, ctx))
                        .collect::<Result<_, _>>()?,
                }
            }
        };
        Ok(self.kernel.arena().alloc(form))
    }

    fn program_proof(
        &mut self,
        proof: Exp,
        context: &raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        let mut reflected = context
            .iter()
            .map(|_| ExpContextEntry {
                var: SymbolId::ANONYMOUS,
                ty: self.raw.arena().sort(RawSort::Set(0)),
            })
            .collect::<Vec<_>>();
        let nominal = self.scope.nominal;
        self.in_scope(self.scope.captures.clone(), 0, context.len(), |this| {
            this.scope.nominal = nominal;
            this.scope.program_context = true;
            this.scope.proof_base = Some(context.len());
            this.set(proof, &mut reflected, this.raw.root_module())
        })
    }

    pub(super) fn computation_term(
        &mut self,
        e: raw::program::ComputationTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        let previous_mode = std::mem::replace(&mut self.scope.program_context, true);
        let depth = std::mem::replace(&mut self.scope.program_depth, ctx.len());
        let result = self.computation_term_inner(e, ctx);
        self.scope.program_depth = depth;
        self.scope.program_context = previous_mode;
        result
    }

    fn computation_term_inner(
        &mut self,
        e: raw::program::ComputationTerm,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Expression, String> {
        use raw::program::{ComputationTermNode as R, ProgramContextEntry};
        use s::Node as F;
        if self.native_reference(e.0) {
            return Ok(e.0);
        }
        let form = match self.raw.arena().get(e) {
            R::Meta { spine, .. } => self.program_meta(e.0, spine)?,
            R::DefinitionInstance {
                definition,
                parameters,
            } => {
                self.definition(definition)?;
                let captures = self.captures(Declaration::Definition(definition));
                let mut arguments = self.capture_arguments(&captures, ctx.len(), true)?;
                for parameter in parameters {
                    arguments.push(self.value_type(parameter)?);
                }
                let id = self
                    .raw
                    .kernel_definitions
                    .borrow()
                    .get(&definition)
                    .copied()
                    .ok_or("unknown definition")?;
                return self.kernel.reference(id, arguments);
            }
            R::DefinedConstant(definition) => {
                return self.definition_expression(definition, ctx.len(), true);
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
                F::Lambda {
                    mode: s::Mode::Computation,
                    var,
                    domain,
                    body: body?,
                }
            }
            R::Application { computation, value } => F::App {
                mode: s::Mode::Computation,
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
                accessibility,
            } => F::Run {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                step: self.value_term(step, ctx)?,
                initial: self.value_term(initial, ctx)?,
                accessibility: self.program_proof(accessibility, ctx)?,
            },
            R::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                transition,
                transition_equality,
            } => F::RunCase {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                step: self.value_term(step, ctx)?,
                initial: self.value_term(initial, ctx)?,
                accessibility: self.program_proof(accessibility, ctx)?,
                transition: self.computation_term(transition, ctx)?,
                transition_equality: self.program_proof(transition_equality, ctx)?,
            },
            R::Case {
                indspec,
                scrutinee,
                branches,
            } => {
                self.datatype(indspec)?;
                let binders = branches.iter().map(|b| b.binders.clone()).collect();
                let mut bodies = vec![];
                for branch in branches {
                    let mut local = ctx.clone();
                    for &var in &branch.binders {
                        local.push(ProgramContextEntry::ValueType { var });
                    }
                    bodies.push(self.computation_term(branch.body, &mut local)?);
                }
                F::ProgramCase {
                    inductive: indspec.into(),
                    binders,
                    scrutinee: self.value_term(scrutinee, ctx)?,
                    branches: bodies,
                }
            }
            R::StepRec {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => F::ProgramStepRec {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                computation_ty: self.computation_type(computation_ty)?,
                on_continue: self.computation_term(on_continue, ctx)?,
                on_finish: self.computation_term(on_finish, ctx)?,
                scrutinee: self.value_term(scrutinee, ctx)?,
            },
        };
        Ok(self.kernel.arena().alloc(form))
    }
}
