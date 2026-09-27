//! Resolve logical source identities into shared kernel expressions.
use super::*;

impl Lowerer<'_> {
    // Reflected Program data can contain long constructor applications.
    // Keep their recursive path out of the large match for the other forms.
    pub(crate) fn set(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, String> {
        if self.native_reference(e.0) {
            return Ok(e.0);
        }
        let ExpNode::App { func, arg } = self.raw.arena().get(e) else {
            return self.set_non_application(e, ctx, m);
        };
        let key = (e, self.raw.context_id(ctx), m);
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
    ) -> Result<s::Expression, String> {
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
    ) -> Result<s::Expression, String> {
        let key = (e, self.raw.context_id(ctx), m);
        if let Some(&v) = self.cache.get(&key) {
            return Ok(v);
        }
        let node = self.raw.arena().get(e);
        let result = match node {
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
                    set: set,
                    predicate: predicate,
                })
            }
            ExpNode::PowerSet { set } => {
                let set = self.set(set, ctx, m)?;
                self.kernel.arena().alloc(s::Node::PowerSet { set: set })
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
                    superset: superset,
                    subset: subset,
                    element: element,
                    proof: proof,
                })
            }
            ExpNode::TypeLift { superset, subset } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                self.kernel.arena().alloc(s::Node::TypeLift {
                    superset: superset,
                    subset: subset,
                })
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
                    superset: superset,
                    subset: subset,
                    element: element,
                })
            }
            ExpNode::Equal { left, right } => {
                let left = self.set(left, ctx, m)?;
                let right = self.set(right, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Equal {
                    left: left,
                    right: right,
                })
            }
            ExpNode::Exists { set } => {
                let set = self.set(set, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Exists { set: set })
            }
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                self.kernel.arena().alloc(s::Node::RunStep {
                    state_ty: state_ty,
                    result_ty: result_ty,
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
                    state_ty: state_ty,
                    result_ty: result_ty,
                    next: next,
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
                    state_ty: state_ty,
                    result_ty: result_ty,
                    output: output,
                })
            }
            ExpNode::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let step = self.set(step, ctx, m)?;
                let state = self.set(state, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Acc {
                    state_ty: state_ty,
                    result_ty: result_ty,
                    step: step,
                    state: state,
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
                    state_ty: state_ty,
                    result_ty: result_ty,
                    step: step,
                    initial: initial,
                    accessibility: accessibility,
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
                    state_ty: state_ty,
                    result_ty: result_ty,
                    step: step,
                    initial: initial,
                    transition: transition,
                    accessibility: accessibility,
                    transition_equality: transition_equality,
                })
            }
            ExpNode::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => {
                let domain = self.set(domain, ctx, m)?;
                let codomain = self.set(codomain, ctx, m)?;
                let map = self.set(map, ctx, m)?;
                let existence = self.set(existence, ctx, m)?;
                let uniqueness = self.set(uniqueness, ctx, m)?;
                self.kernel.arena().alloc(s::Node::TakeSet {
                    domain: domain,
                    codomain: codomain,
                    map: map,
                    existence: existence,
                    uniqueness: uniqueness,
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
                    domain: domain,
                    proposition: proposition,
                    map: map,
                    existence: existence,
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
                self.kernel.arena().alloc(s::Node::ForceBox {
                    program_ty,
                    boxed: boxed,
                })
            }
            ExpNode::IndType {
                indspec,
                parameters,
            } => {
                self.inductive(indspec)?;
                let inductive = indspec.into();
                let captures = self.captures(Declaration::Inductive(indspec));
                let mut arguments =
                    self.capture_arguments(&captures, ctx.len() - self.scope.logical_base, false)?;
                arguments.extend(
                    parameters
                        .into_iter()
                        .map(|x| self.set(x, ctx, m))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                let parameters = arguments;
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
                self.inductive(indspec)?;
                let inductive = indspec.into();
                let constructor = idx;
                let captures = self.captures(Declaration::Inductive(indspec));
                let mut arguments =
                    self.capture_arguments(&captures, ctx.len() - self.scope.logical_base, false)?;
                arguments.extend(
                    parameters
                        .into_iter()
                        .map(|x| self.set(x, ctx, m))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                let parameters = arguments;
                self.kernel.arena().alloc(s::Node::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                })
            }
            ExpNode::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => {
                self.inductive(indspec)?;
                let scrutinee = self.set(elim, ctx, m)?;
                let motive = self.set(return_type, ctx, m)?;
                let cases = cases
                    .into_iter()
                    .map(|e| self.set(e, ctx, m))
                    .collect::<Result<_, _>>()?;
                self.kernel.arena().alloc(s::Node::IndElim {
                    inductive: indspec.into(),
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
                let scrutinee = self.set(scrutinee, ctx, m)?;
                let motive = self.set(return_type, ctx, m)?;
                let branches = branches
                    .into_iter()
                    .map(|e| self.set(e, ctx, m))
                    .collect::<Result<_, _>>()?;
                self.kernel.arena().alloc(s::Node::Case {
                    inductive: indspec.into(),
                    scrutinee,
                    motive,
                    branches,
                })
            }
            ExpNode::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let motive = self.set(motive, ctx, m)?;
                let on_continue = self.set(on_continue, ctx, m)?;
                let on_finish = self.set(on_finish, ctx, m)?;
                let scrutinee = self.set(scrutinee, ctx, m)?;
                self.kernel.arena().alloc(s::Node::Recursor {
                    state_ty: state_ty,
                    result_ty: result_ty,
                    motive: motive,
                    on_continue: on_continue,
                    on_finish: on_finish,
                    scrutinee: scrutinee,
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
            ExpNode::Prove(prove) => match prove {
                Prove::IdRefl { element } => {
                    let element = self.set(element, ctx, m)?;
                    self.kernel
                        .arena()
                        .alloc(s::Node::IdRefl { element: element })
                }
                Prove::ExistsIntro { element, set } => {
                    let element = self.set(element, ctx, m)?;
                    let set = self.set(set, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::ExistsIntro {
                        element: element,
                        set: set,
                    })
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
                        element: element,
                        subset: subset,
                        superset: superset,
                    })
                }
                Prove::IdElim {
                    var,
                    left,
                    right,
                    ty,
                    predicate,
                    base,
                    equality,
                } => {
                    let left = self.set(left, ctx, m)?;
                    let right = self.set(right, ctx, m)?;
                    let raw_ty = ty;
                    let ty = self.set(ty, ctx, m)?;
                    let predicate =
                        self.under(ctx, var, raw_ty, |this, ctx| this.set(predicate, ctx, m))?;
                    let base = self.set(base, ctx, m)?;
                    let equality = self.set(equality, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::IdElim {
                        var,
                        left: left,
                        right: right,
                        ty: ty,
                        predicate: predicate,
                        base: base,
                        equality: equality,
                    })
                }
                Prove::TakeEq {
                    func,
                    domain,
                    codomain,
                    element,
                    existence,
                    uniqueness,
                } => {
                    let func = self.set(func, ctx, m)?;
                    let domain = self.set(domain, ctx, m)?;
                    let codomain = self.set(codomain, ctx, m)?;
                    let element = self.set(element, ctx, m)?;
                    let existence = self.set(existence, ctx, m)?;
                    let uniqueness = self.set(uniqueness, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::TakeEq {
                        func: func,
                        domain: domain,
                        codomain: codomain,
                        element: element,
                        existence: existence,
                        uniqueness: uniqueness,
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
                        left: left,
                        right: right,
                        left_to_right: left_to_right,
                        right_to_left: right_to_left,
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
                        left: left,
                        right: right,
                        pointwise: pointwise,
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
                            domain: domain,
                            family: family,
                            inhabited: inhabited,
                        })
                }
                Prove::AccIntro {
                    state_ty,
                    result_ty,
                    step,
                    state,
                    predecessors,
                } => {
                    let state_ty = self.set(state_ty, ctx, m)?;
                    let result_ty = self.set(result_ty, ctx, m)?;
                    let step = self.set(step, ctx, m)?;
                    let state = self.set(state, ctx, m)?;
                    let predecessors = self.set(predecessors, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::AccIntro {
                        state_ty: state_ty,
                        result_ty: result_ty,
                        step: step,
                        state: state,
                        predecessors: predecessors,
                    })
                }
                Prove::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from,
                    to,
                    accessibility,
                    transition,
                } => {
                    let state_ty = self.set(state_ty, ctx, m)?;
                    let result_ty = self.set(result_ty, ctx, m)?;
                    let step = self.set(step, ctx, m)?;
                    let from = self.set(from, ctx, m)?;
                    let to = self.set(to, ctx, m)?;
                    let accessibility = self.set(accessibility, ctx, m)?;
                    let transition = self.set(transition, ctx, m)?;
                    self.kernel.arena().alloc(s::Node::AccDescent {
                        state_ty: state_ty,
                        result_ty: result_ty,
                        step: step,
                        from: from,
                        to: to,
                        accessibility: accessibility,
                        transition: transition,
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
