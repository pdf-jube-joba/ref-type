//! Resolve logical source identities into shared kernel expressions.
use super::*;

impl Lowerer<'_> {
    fn inductive_reference(
        &mut self,
        id: InductiveId,
        ctx: &mut ExpContext,
        module: ModuleId,
    ) -> Result<(kernel::ids::InductiveId, Vec<s::Expression>), crate::error::Error> {
        self.inductive(id)?;
        let origin = if self.raw.is_program_mirror(id) {
            None
        } else {
            self.raw.inductive_specialization(id).cloned()
        };
        let Some(origin) = origin else {
            let captures = self.captures(Declaration::Inductive(id));
            return Ok((
                id.into(),
                self.capture_arguments(&captures, ctx.len() - self.scope.logical_base, false)?,
            ));
        };
        let captures = self.captures(Declaration::Inductive(origin.source));
        let mut arguments = Vec::new();
        for parameter in captures {
            let Some((_, argument)) = origin.arguments.iter().find(|(id, _)| *id == parameter)
            else {
                arguments.extend(self.capture_arguments(
                    &[parameter],
                    ctx.len() - self.scope.logical_base,
                    false,
                )?);
                continue;
            };
            let term = match *argument {
                raw::environment::ModuleArgument::Pts(e) => e,
                raw::environment::ModuleArgument::ProgramType(t) => {
                    raw::reflection::reflect_value_type(self.raw, t)
                        .map_err(crate::error::Error::from)?
                }
                raw::environment::ModuleArgument::ProgramValue(v) => {
                    raw::reflection::reflect_program(
                        self.raw,
                        raw::program::ProgramTerm::ValueTerm(v),
                    )
                    .map_err(crate::error::Error::from)?
                }
            };
            let shift = ctx
                .len()
                .saturating_sub(self.raw.definition_context(id.module).len());
            let term = crate::kernel_bridge::shift_bound_indices(self.raw.arena(), term, shift, 0);
            arguments.push(self.set(term, ctx, module)?);
        }
        Ok((origin.source.into(), arguments))
    }

    fn inductive_application(
        &mut self,
        id: InductiveId,
        parameters: Vec<Exp>,
        ctx: &mut ExpContext,
        module: ModuleId,
    ) -> Result<(kernel::ids::InductiveId, Vec<s::Expression>), crate::error::Error> {
        self.inductive(id)?;
        let source = if self.raw.is_program_mirror(id) {
            id
        } else {
            self.raw
                .inductive_specialization(id)
                .map_or(id, |origin| origin.source)
        };
        let explicit_capture_arguments = self
            .raw
            .arena()
            .inductive_captures
            .borrow()
            .get(&source.into())
            .is_some_and(|(captures, explicit)| {
                !captures.is_empty() && parameters.len() == captures.len() + explicit
            });
        let (inductive, mut arguments) = if explicit_capture_arguments {
            (source.into(), Vec::new())
        } else {
            self.inductive_reference(id, ctx, module)?
        };
        arguments.extend(
            parameters
                .into_iter()
                .map(|x| self.set(x, ctx, module))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok((inductive, arguments))
    }

    fn induction_motive(
        &mut self,
        bindings: &[(SymbolId, Exp)],
        body: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<(Vec<(SymbolId, s::Expression)>, s::Expression), crate::error::Error> {
        let Some((&(var, domain), tail)) = bindings.split_first() else {
            return Ok((Vec::new(), self.set(body, ctx, m)?));
        };
        let ty = self.set(domain, ctx, m)?;
        let (tail, body) = self.under(ctx, var, domain, |this, ctx| {
            this.induction_motive(tail, body, ctx, m)
        })?;
        let mut bindings = Vec::with_capacity(tail.len() + 1);
        bindings.push((var, ty));
        bindings.extend(tail);
        Ok((bindings, body))
    }

    fn logical_key(
        &self,
        e: Exp,
        depth: usize,
        m: ModuleId,
    ) -> (Exp, usize, ModuleId, usize, bool) {
        (
            e,
            depth,
            m,
            self.scope.program_depth,
            self.scope.program_context,
        )
    }
    // Reflected Program data can contain long constructor applications.
    // Keep their recursive path out of the large match for the other forms.
    pub(crate) fn set(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, crate::error::Error> {
        let nominal = !self.structural
            && self.scope.nominal
            && self.scope.proof_base.is_none()
            && !self.scope.program_context
            && self.scope.program_depth == 0;
        if nominal && self.raw.arena().lowered_definitions.borrow().contains(&e.0) {
            return Ok(e.0);
        }
        let result = self.set_unresolved(e, ctx, m)?;
        if nominal && matches!(self.kernel.arena().get(result), s::Node::Definition { .. }) {
            self.raw
                .arena()
                .lowered_definitions
                .borrow_mut()
                .insert(result);
        }
        Ok(result)
    }

    fn set_unresolved(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, crate::error::Error> {
        if let s::Node::Definition { id, arguments } = self.kernel.arena().get(e.0) {
            let key = self.logical_key(e, ctx.len(), m);
            if let Some(&result) = self.cache.get(&key) {
                return Ok(result);
            }
            let arguments = arguments
                .into_iter()
                .map(|argument| self.set(Exp(argument), ctx, m))
                .collect::<Result<Vec<_>, _>>()?;
            let result = self
                .kernel
                .arena()
                .alloc(s::Node::Definition { id, arguments });
            self.cache.insert(key, result);
            return Ok(result);
        }
        let ExpNode::App { func, arg } = self.raw.arena().get(e) else {
            return self.set_non_application(e, ctx, m);
        };
        let key = self.logical_key(e, ctx.len(), m);
        if let Some(&result) = self.cache.get(&key) {
            return Ok(result);
        }
        let result = self.set_application(e, func, arg, ctx, m)?;
        self.cache.insert(key, result);
        Ok(result)
    }

    fn set_application(
        &mut self,
        e: Exp,
        func: Exp,
        arg: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, crate::error::Error> {
        let _ = e;
        let function = self.set(func, ctx, m)?;
        let argument = self.set(arg, ctx, m)?;
        Ok(self.kernel.arena().alloc(s::Node::App {
            mode: s::Mode::Pure,
            function,
            argument,
        }))
    }

    fn set_non_application(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, crate::error::Error> {
        let key = self.logical_key(e, ctx.len(), m);
        if let Some(&v) = self.cache.get(&key) {
            return Ok(v);
        }
        let node = self.raw.arena().get(e);
        let result = match node {
            ExpNode::Ascribe { term, ty } => {
                let term = self.set(term, ctx, m)?;
                let ty = self.set(ty, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Ascribe { term, ty })
            }
            ExpNode::Bound(index) => {
                let bound = self.kernel.arena().bound(index);
                if self
                    .scope
                    .proof_base
                    .is_some_and(|base| index >= ctx.len() - base)
                {
                    self.kernel.arena().alloc(s::Node::Reflect { term: bound })
                } else {
                    bound
                }
            }
            ExpNode::ModuleParam(parameter) => {
                if self.scope.nominal {
                    return self.nominal_parameter(parameter);
                }
                let index = self.parameter_index(parameter, ctx.len() - self.scope.logical_base)?;
                self.kernel.arena().bound(index)
            }
            ExpNode::DefinedConstant(definition) => {
                self.definition_expression(definition, ctx.len() - self.scope.logical_base, false)?
            }
            ExpNode::DefinitionInstance {
                definition,
                arguments,
            } => {
                let parameters = arguments
                    .into_iter()
                    .map(|argument| self.set(argument, ctx, m))
                    .collect::<Result<Vec<_>, _>>()?;
                self.definition_expression_with_parameters(
                    definition,
                    ctx.len() - self.scope.logical_base,
                    false,
                    &parameters,
                )?
            }
            ExpNode::SubSet {
                var,
                set,
                predicate,
            } => {
                let raw_set = set;
                let set = self.set(set, ctx, m)?;
                let predicate =
                    self.under(ctx, var, raw_set, |this, ctx| this.set(predicate, ctx, m))?;
                self.kernel.arena().alloc(s::Node::Subset {
                    var,
                    set,
                    predicate,
                })
            }
            ExpNode::PowerSet { set } => {
                let set = self.set(set, ctx, m)?;
                self.kernel.arena().alloc(s::Node::PowerSet { set })
            }
            ExpNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                let element = self.set(element, ctx, m)?;
                let proof = self.set(proof, ctx, m)?;
                self.kernel.arena().alloc(s::Node::SubsetIntro {
                    superset,
                    subset,
                    element,
                    proof,
                })
            }
            ExpNode::TypeLift { superset, subset } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                self.kernel
                    .arena()
                    .alloc(s::Node::TypeLift { superset, subset })
            }
            ExpNode::Pred {
                superset,
                subset,
                element,
            } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                let element = self.set(element, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Pred {
                    superset,
                    subset,
                    element,
                })
            }
            ExpNode::Equal { left, right } => {
                let left = self.set(left, ctx, m)?;
                let right = self.set(right, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Equal { left, right })
            }
            ExpNode::Exists { set } => {
                let set = self.set(set, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Exists { set })
            }
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                self.kernel.arena().alloc(s::Node::RunStep {
                    state_ty,
                    result_ty,
                })
            }
            ExpNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let next = self.set(next, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Continue {
                    state_ty,
                    result_ty,
                    next,
                })
            }
            ExpNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let output = self.set(output, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Finish {
                    state_ty,
                    result_ty,
                    output,
                })
            }
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let step = self.set(step, ctx, m)?;
                let initial = self.set(initial, ctx, m)?;
                let accessibility = self.set(accessibility, ctx, m)?;
                self.kernel.arena().alloc(s::Node::SetRun {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    accessibility,
                })
            }
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let step = self.set(step, ctx, m)?;
                let initial = self.set(initial, ctx, m)?;
                let transition = self.set(transition, ctx, m)?;
                let accessibility = self.set(accessibility, ctx, m)?;
                let transition_equality = self.set(transition_equality, ctx, m)?;
                self.kernel.arena().alloc(s::Node::SetRunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                    accessibility,
                    transition_equality,
                })
            }
            ExpNode::Choice {
                set,
                existence,
                uniqueness,
            } => {
                let set = self.set(set, ctx, m)?;
                let existence = self.set(existence, ctx, m)?;
                let uniqueness = self.set(uniqueness, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Choice {
                    set,
                    existence,
                    uniqueness,
                })
            }
            ExpNode::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => {
                let domain = self.set(domain, ctx, m)?;
                let proposition = self.set(proposition, ctx, m)?;
                let map = self.set(map, ctx, m)?;
                let existence = self.set(existence, ctx, m)?;
                self.kernel.arena().alloc(s::Node::TakeProp {
                    domain,
                    proposition,
                    map,
                    existence,
                })
            }
            ExpNode::BoxType { program_ty } => {
                let program_ty = self.computation_type(program_ty)?;
                self.kernel.arena().alloc(s::Node::BoxType { program_ty })
            }
            ExpNode::BoxProgram {
                program_ty,
                program,
            } => {
                let program_ty = self.computation_type(program_ty)?;
                let program = self.computation_term(program, &mut vec![])?;
                self.kernel.arena().alloc(s::Node::BoxProgram {
                    program_ty,
                    program,
                })
            }
            ExpNode::ForceBox { program_ty, boxed } => {
                let program_ty = self.computation_type(program_ty)?;
                let boxed = self.set(boxed, ctx, m)?;
                self.kernel
                    .arena()
                    .alloc(s::Node::ForceBox { program_ty, boxed })
            }
            ExpNode::IndType {
                indspec,
                parameters,
            } => {
                let (inductive, parameters) =
                    self.inductive_application(indspec, parameters, ctx, m)?;
                self.kernel.arena().alloc(s::Node::IndType {
                    inductive,
                    parameters,
                })
            }
            ExpNode::IndCtor {
                indspec,
                idx,
                parameters,
            } => {
                let (inductive, parameters) =
                    self.inductive_application(indspec, parameters, ctx, m)?;
                let constructor = idx;
                self.kernel.arena().alloc(s::Node::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                })
            }
            ExpNode::IndElim {
                motive_bindings,
                indspec,
                elim,
                return_type,
                cases,
            } => {
                self.inductive(indspec)?;
                let inductive = if self.raw.is_program_mirror(indspec) {
                    indspec
                } else {
                    self.raw
                        .inductive_specialization(indspec)
                        .map_or(indspec, |origin| origin.source)
                }
                .into();
                let scrutinee = self.set(elim, ctx, m)?;
                let (motive_bindings, motive) =
                    self.induction_motive(&motive_bindings, return_type, ctx, m)?;
                let cases = cases
                    .into_iter()
                    .map(|e| self.set(e, ctx, m))
                    .collect::<Result<_, _>>()?;
                self.kernel.arena().alloc(s::Node::IndElim {
                    motive_bindings,
                    inductive,
                    scrutinee,
                    motive,
                    cases,
                })
            }
            ExpNode::IndCase {
                indspec,
                scrutinee,
                return_type,
                branches,
            } => {
                self.inductive(indspec)?;
                let inductive = if self.raw.is_program_mirror(indspec) {
                    indspec
                } else {
                    self.raw
                        .inductive_specialization(indspec)
                        .map_or(indspec, |origin| origin.source)
                }
                .into();
                let scrutinee = self.set(scrutinee, ctx, m)?;
                let motive = self.set(return_type, ctx, m)?;
                let branches = branches
                    .into_iter()
                    .map(|e| self.set(e, ctx, m))
                    .collect::<Result<_, _>>()?;
                self.kernel.arena().alloc(s::Node::Case {
                    inductive,
                    scrutinee,
                    motive,
                    branches,
                })
            }
            ExpNode::SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let motive = self.set(motive, ctx, m)?;
                let on_continue = self.set(on_continue, ctx, m)?;
                let on_finish = self.set(on_finish, ctx, m)?;
                self.kernel.arena().alloc(s::Node::SetStepMatch {
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
                })
            }
            ExpNode::Prod { var, ty, body } | ExpNode::Lam { var, ty, body } => {
                let domain = self.set(ty, ctx, m)?;
                let body = self.under(ctx, var, ty, |this, ctx| this.set(body, ctx, m))?;
                if matches!(node, ExpNode::Prod { .. }) {
                    self.kernel
                        .arena()
                        .alloc(s::Node::Product { var, domain, body })
                } else {
                    self.kernel.arena().alloc(s::Node::Lambda {
                        mode: s::Mode::Pure,
                        var,
                        domain,
                        body,
                    })
                }
            }
            ExpNode::App { .. } => unreachable!("applications use the small-frame path"),
            ExpNode::IdElim {
                var,
                left,
                right,
                ty,
                family,
                base,
                equality,
            } => {
                let left = self.set(left, ctx, m)?;
                let right = self.set(right, ctx, m)?;
                let raw_ty = ty;
                let ty = self.set(ty, ctx, m)?;
                let family = self.under(ctx, var, raw_ty, |this, ctx| this.set(family, ctx, m))?;
                let base = self.set(base, ctx, m)?;
                let equality = self.set(equality, ctx, m)?;
                self.kernel.arena().alloc(s::Node::IdElim {
                    var,
                    left,
                    right,
                    ty,
                    family,
                    base,
                    equality,
                })
            }
            ExpNode::Prove(prove) => match prove {
                Prove::IdRefl { element } => {
                    let element = self.set(element, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::IdRefl { element })
                }
                Prove::ExistsIntro { element, set } => {
                    let element = self.set(element, ctx, m)?;
                    let set = self.set(set, ctx, m)?;
                    self.kernel
                        .arena()
                        .alloc(s::Node::ExistsIntro { element, set })
                }
                Prove::SubsetElim {
                    element,
                    subset,
                    superset,
                } => {
                    let element = self.set(element, ctx, m)?;
                    let subset = self.set(subset, ctx, m)?;
                    let superset = self.set(superset, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::SubsetElim {
                        element,
                        subset,
                        superset,
                    })
                }
                Prove::TransportEq {
                    var,
                    ty,
                    index,
                    family,
                    base,
                } => {
                    let raw_ty = ty;
                    let ty = self.set(ty, ctx, m)?;
                    let index = self.set(index, ctx, m)?;
                    let family =
                        self.under(ctx, var, raw_ty, |this, ctx| this.set(family, ctx, m))?;
                    let base = self.set(base, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::TransportEq {
                        var,
                        ty,
                        index,
                        family,
                        base,
                    })
                }
                Prove::ChoiceEq {
                    set,
                    element,
                    existence,
                    uniqueness,
                } => {
                    let set = self.set(set, ctx, m)?;
                    let element = self.set(element, ctx, m)?;
                    let existence = self.set(existence, ctx, m)?;
                    let uniqueness = self.set(uniqueness, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::ChoiceEq {
                        set,
                        element,
                        existence,
                        uniqueness,
                    })
                }
                Prove::Axiom(Axiom::SetExt {
                    left,
                    right,
                    left_to_right,
                    right_to_left,
                }) => {
                    let left = self.set(left, ctx, m)?;
                    let right = self.set(right, ctx, m)?;
                    let left_to_right = self.set(left_to_right, ctx, m)?;
                    let right_to_left = self.set(right_to_left, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::SetExt {
                        left,
                        right,
                        left_to_right,
                        right_to_left,
                    })
                }
                Prove::Axiom(Axiom::FunExt {
                    left,
                    right,
                    pointwise,
                }) => {
                    let left = self.set(left, ctx, m)?;
                    let right = self.set(right, ctx, m)?;
                    let pointwise = self.set(pointwise, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::FunExt {
                        left,
                        right,
                        pointwise,
                    })
                }
                Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
                    domain,
                    family,
                    inhabited,
                }) => {
                    let domain = self.set(domain, ctx, m)?;
                    let family = self.set(family, ctx, m)?;
                    let inhabited = self.set(inhabited, ctx, m)?;
                    self.kernel
                        .arena()
                        .alloc(s::Node::ClassicalIndefiniteChoice {
                            domain,
                            family,
                            inhabited,
                        })
                }
            },
            ExpNode::BoxApp { function, argument } => {
                let function = self.set(function, ctx, m)?;
                let argument = self.set(argument, ctx, m)?;
                self.kernel
                    .arena()
                    .alloc(s::Node::BoxApp { function, argument })
            }
            ExpNode::ReflectedProgramCase {
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
                        local.push(ExpContextEntry {
                            var,
                            ty: self.raw.arena().sort(RawSort::Set(0)),
                        });
                    }
                    bodies.push(self.set(branch.body, &mut local, m)?);
                }
                let scrutinee = self.set(scrutinee, ctx, m)?;
                self.kernel.arena().alloc(s::Node::SetCase {
                    inductive: indspec.into(),
                    binders,
                    scrutinee,
                    branches: bodies,
                })
            }
            ExpNode::ReflectedProgramParam(parameter) => {
                if self.scope.nominal {
                    let term = self.nominal_parameter(parameter)?;
                    return Ok(self.kernel.arena().alloc(s::Node::Reflect { term }));
                }
                let index = self.parameter_index(parameter, ctx.len() - self.scope.logical_base)?;
                let bound = self.kernel.arena().bound(index);
                if self.scope.program_context {
                    self.kernel.arena().alloc(s::Node::Reflect { term: bound })
                } else {
                    bound
                }
            }
            ExpNode::Meta { spine, .. } => {
                let s::Node::Meta { id, .. } = self.raw.arena().core.get(e.0) else {
                    unreachable!()
                };
                let arguments = spine
                    .into_iter()
                    .map(|e| self.set(e, ctx, m))
                    .collect::<Result<_, _>>()?;
                self.kernel.arena().alloc(s::Node::Meta { id, arguments })
            }
            ExpNode::Sort(sort) => self.kernel.arena().sort(Self::sort(sort)),
        };
        self.cache.insert(key, result);
        Ok(result)
    }
}
