//! Classify Set/Prop expressions and attach kernel product rules.
use super::nodes::logical_node;
use super::*;
use kernel::construction as build;

impl Lowerer<'_> {
    // Reflected Program data can contain long constructor applications.
    // Keep their recursive path out of the large match for the other forms.
    pub(crate) fn set(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, String> {
        let ExpNode::App { func, arg } = self.raw.arena().get(e) else {
            return self.set_non_application(e, ctx, m);
        };
        let key = (e, ctx.iter().map(|b| b.ty).collect(), m);
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
        self.infer(e, ctx, m)?;
        let ty = self.infer(func, ctx, m)?;
        let (_, domain, codomain) = raw::calculus::expose_product(self.raw, ty)
            .ok_or("application does not have product type")?;
        let domain_sort = self.formation(domain, ctx, m)?;
        let body_sort = self.under(ctx, SymbolId::ANONYMOUS, domain, |this, ctx| {
            this.formation(codomain, ctx, m)
        })?;
        let rule = k::ProductRule::new(domain_sort, body_sort)?;
        let function = self.set(func, ctx, m)?;
        let argument = self.set(arg, ctx, m)?;
        build::apply(self.kernel.arena(), rule, function, argument)
    }

    fn set_non_application(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<s::Expression, String> {
        let key = (e, ctx.iter().map(|b| b.ty).collect(), m);
        if let Some(&v) = self.cache.get(&key) {
            return Ok(v);
        }
        let node = self.raw.arena().get(e);
        if let ExpNode::Sort(raw) = node {
            let sort = Self::sort(raw);
            if sort.is_upper() {
                return Err("upper sort is a judgement classifier, not an expression".into());
            }
            return self.logical_base_kind(sort.base());
        }
        let ty = self.infer(e, ctx, m)?;
        let head = raw::calculus::whnf(self.raw, ty);
        let (sort, stage) = if let ExpNode::Sort(raw) = self.raw.arena().get(head) {
            let sort = Self::sort(raw);
            (
                sort.base(),
                if sort.is_upper() {
                    s::Stage::Kind
                } else {
                    s::Stage::Type
                },
            )
        } else {
            let sort = self.formation(ty, ctx, m)?;
            (
                sort.base(),
                if sort.is_upper() {
                    s::Stage::Type
                } else {
                    s::Stage::Term
                },
            )
        };
        let syntax_family = s::Family::at(sort, stage);
        let result = match node {
            ExpNode::Bound(index) => build::bound(self.kernel.arena(), sort, stage, index)?,
            ExpNode::ModuleParam(parameter) => {
                self.parameter(parameter)?;
                logical_node!(self, sort, syntax_family; SetTerm | PropTerm | SetType | PropType | SetKind | PropKind => ModuleParam { parameter })
            }
            ExpNode::DefinedConstant(definition) => {
                self.definition(definition)?;
                let definition = self
                    .kernel
                    .definition(definition)
                    .ok_or("unknown definition")?;
                self.kernel
                    .arena()
                    .annotated(definition.body, definition.classifier)?
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
                logical_node!(self, sort, syntax_family; SetTerm => Subset {
                    var,
                    set: set.try_into()?,
                    predicate: predicate.try_into()?,
                })
            }
            ExpNode::PowerSet { set } => {
                let set = self.set(set, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetType => PowerSet {
                    set: set.try_into()?,
                })
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
                logical_node!(self, sort, syntax_family; SetTerm => SubsetIntro {
                    superset: superset.try_into()?,
                    subset: subset.try_into()?,
                    element: element.try_into()?,
                    proof: proof.try_into()?,
                })
            }
            ExpNode::TypeLift { superset, subset } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetType => TypeLift {
                    superset: superset.try_into()?,
                    subset: subset.try_into()?,
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
                logical_node!(self, sort, syntax_family; PropType => Pred {
                    superset: superset.try_into()?,
                    subset: subset.try_into()?,
                    element: element.try_into()?,
                })
            }
            ExpNode::Equal { left, right } => {
                let left = self.set(left, ctx, m)?;
                let right = self.set(right, ctx, m)?;
                logical_node!(self, sort, syntax_family; PropType => Equal {
                    left: left.try_into()?,
                    right: right.try_into()?,
                })
            }
            ExpNode::Exists { set } => {
                let set = self.set(set, ctx, m)?;
                logical_node!(self, sort, syntax_family; PropType => Exists {
                    set: set.try_into()?,
                })
            }
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetType => RunStep {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
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
                logical_node!(self, sort, syntax_family; SetTerm => Continue {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    next: next.try_into()?,
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
                logical_node!(self, sort, syntax_family; SetTerm => Finish {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    output: output.try_into()?,
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
                logical_node!(self, sort, syntax_family; PropType => Acc {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    step: step.try_into()?,
                    state: state.try_into()?,
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
                logical_node!(self, sort, syntax_family; SetTerm => SetRun {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    step: step.try_into()?,
                    initial: initial.try_into()?,
                    accessibility: accessibility
                        .try_into()
                        .map_err(|e| format!("{e:?}"))?,
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
                logical_node!(self, sort, syntax_family; SetTerm => SetRunCase {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    step: step.try_into()?,
                    initial: initial.try_into()?,
                    transition: transition.try_into()?,
                    accessibility: accessibility
                        .try_into()
                        .map_err(|e| format!("{e:?}"))?,
                    transition_equality: transition_equality
                        .try_into()
                        .map_err(|e| format!("{e:?}"))?,
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
                logical_node!(self, sort, syntax_family; SetTerm => TakeSet {
                    domain: domain.try_into()?,
                    codomain: codomain.try_into()?,
                    map: map.try_into()?,
                    existence: existence.try_into()?,
                    uniqueness: uniqueness.try_into()?,
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
                logical_node!(self, sort, syntax_family; PropTerm => TakeProp {
                    domain: domain.try_into()?,
                    proposition: proposition
                        .try_into()
                        .map_err(|e| format!("{e:?}"))?,
                    map: map.try_into()?,
                    existence: existence.try_into()?,
                })
            }
            ExpNode::BoxType { program_ty } => {
                let program_ty = self.program_type(program_ty)?;
                logical_node!(self, sort, syntax_family; SetType => BoxType { program_ty })
            }
            ExpNode::BoxProgram {
                program_ty,
                program,
            } => {
                let program_ty = self.program_type(program_ty)?;
                let program = self.program_term(program)?;
                logical_node!(self, sort, syntax_family; SetTerm => BoxProgram {
                    program_ty,
                    program,
                })
            }
            ExpNode::ForceBox { program_ty, boxed } => {
                let program_ty = self.program_type(program_ty)?;
                let boxed = self.set(boxed, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetTerm => ForceBox {
                    program_ty,
                    boxed: boxed.try_into()?,
                })
            }
            ExpNode::IndType {
                indspec,
                parameters,
            } => {
                self.inductive(indspec, m, ctx)?;
                let inductive = indspec;
                let parameters = parameters
                    .into_iter()
                    .map(|x| self.set(x, ctx, m))
                    .collect::<Result<Vec<_>, _>>()?;
                build::inductive_type(
                    self.kernel.arena(),
                    sort,
                    stage,
                    inductive,
                    parameters
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                )?
            }
            ExpNode::IndCtor {
                indspec,
                idx,
                parameters,
            } => {
                self.inductive(indspec, m, ctx)?;
                let inductive = indspec;
                let constructor = idx;
                let parameters = parameters
                    .into_iter()
                    .map(|x| self.set(x, ctx, m))
                    .collect::<Result<Vec<_>, _>>()?;
                build::inductive_constructor(
                    self.kernel.arena(),
                    sort,
                    stage,
                    inductive,
                    constructor,
                    parameters
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                )?
            }
            ExpNode::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => {
                self.inductive(indspec, m, ctx)?;
                let inductive = indspec;
                let kind = raw::derivation::infer_motive_kind(
                    &mut raw::derivation::CheckSession::new(self.raw, m, ctx),
                    "Lower",
                    "motive",
                    return_type,
                )
                .map_err(|e| format!("motive: {e:?}"))?;
                let (binders, _) = raw::utils::decompose_prod(self.raw.arena(), kind);
                let mut local = ctx.clone();
                let mut motive_domains = vec![];
                let mut motive_vars = vec![];
                for (var, ty) in &binders {
                    motive_domains.push(self.set(*ty, &mut local, m)?.try_into()?);
                    motive_vars.push(*var);
                    local.push(ExpContextEntry { var: *var, ty: *ty });
                }
                let shifted = raw::calculus::shift_bound_indices(
                    self.raw.arena(),
                    return_type,
                    binders.len(),
                    0,
                );
                let arguments = (0..binders.len())
                    .rev()
                    .map(|i| self.raw.arena().exp_bound(i))
                    .collect();
                let body = raw::calculus::whnf(
                    self.raw,
                    raw::utils::assoc_apply(self.raw.arena(), shifted, arguments),
                );
                let motive_body = self.set(body, &mut local, m)?.try_into()?;
                let scrutinee = self.set(elim, ctx, m)?.try_into()?;
                let cases = cases
                    .into_iter()
                    .map(|e| self.set(e, ctx, m)?.try_into())
                    .collect::<Result<_, String>>()?;
                logical_node!(self, sort, syntax_family; SetTerm | PropTerm | SetType | PropType => IndElim {
                                inductive,
                                motive_vars,
                                scrutinee,
                                motive_domains,
                                motive_body,
                                cases,
                            }; "eliminator cannot return a kind")
            }
            ExpNode::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let ExpNode::Lam {
                    var,
                    ty: domain,
                    body: motive,
                } = self.raw.arena().get(motive)
                else {
                    return Err("recursor motive must be a lambda".into());
                };
                let sigma =
                    self.under(ctx, var, domain, |this, ctx| this.formation(motive, ctx, m))?;
                let rule = k::ProductRule::new(self.formation(state_ty, ctx, m)?, sigma)?;
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let motive = self.under(ctx, var, domain, |this, ctx| this.set(motive, ctx, m))?;
                let on_continue = self.set(on_continue, ctx, m)?;
                let on_finish = self.set(on_finish, ctx, m)?;
                let scrutinee = self.set(scrutinee, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetTerm | PropTerm | SetType | PropType => Recursor {
                    rule,
                    var,
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    motive: motive.try_into()?,
                    on_continue: on_continue
                        .try_into()
                        .map_err(|e| format!("{e:?}"))?,
                    on_finish: on_finish.try_into()?,
                    scrutinee: scrutinee.try_into()?,
                })
            }
            ExpNode::Prod { var, ty, body } | ExpNode::Lam { var, ty, body } => {
                let domain_sort = self.formation(ty, ctx, m)?;
                let body_sort = self.under(ctx, var, ty, |this, ctx| {
                    if matches!(node, ExpNode::Prod { .. }) {
                        this.formation(body, ctx, m)
                    } else {
                        let t = this.infer(body, ctx, m)?;
                        this.formation(t, ctx, m)
                    }
                })?;
                let rule = k::ProductRule::new(domain_sort, body_sort)?;
                let domain = self.set(ty, ctx, m)?;
                let body = self.under(ctx, var, ty, |this, ctx| this.set(body, ctx, m))?;
                if matches!(node, ExpNode::Prod { .. }) {
                    build::product(self.kernel.arena(), rule, var, domain, body)?
                } else {
                    build::lambda(self.kernel.arena(), rule, var, domain, body)?
                }
            }
            ExpNode::App { .. } => unreachable!("applications use the small-frame path"),
            ExpNode::Prove(prove) => match prove {
                Prove::IdRefl { element } => {
                    let element = self.set(element, ctx, m)?;
                    logical_node!(self, sort, syntax_family; PropTerm => IdRefl {
                        element: element.try_into()?,
                    })
                }
                Prove::ExistsIntro { element, set } => {
                    let element = self.set(element, ctx, m)?;
                    let set = self.set(set, ctx, m)?;
                    logical_node!(self, sort, syntax_family; PropTerm => ExistsIntro {
                        element: element.try_into()?,
                        set: set.try_into()?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => SubsetElim {
                        element: element.try_into()?,
                        subset: subset.try_into()?,
                        superset: superset.try_into()?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => IdElim {
                        var,
                        left: left.try_into()?,
                        right: right.try_into()?,
                        ty: ty.try_into()?,
                        predicate: predicate
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        base: base.try_into()?,
                        equality: equality.try_into()?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => TakeEq {
                        func: func.try_into()?,
                        domain: domain.try_into()?,
                        codomain: codomain.try_into()?,
                        element: element.try_into()?,
                        existence: existence
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        uniqueness: uniqueness
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => SetExt {
                        left: left.try_into()?,
                        right: right.try_into()?,
                        left_to_right: left_to_right
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        right_to_left: right_to_left
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => FunExt {
                        left: left.try_into()?,
                        right: right.try_into()?,
                        pointwise: pointwise
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => ClassicalIndefiniteChoice {
                        domain: domain.try_into()?,
                        family: family.try_into()?,
                        inhabited: inhabited
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => AccIntro {
                        state_ty: state_ty.try_into()?,
                        result_ty: result_ty
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        step: step.try_into()?,
                        state: state.try_into()?,
                        predecessors: predecessors
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
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
                    logical_node!(self, sort, syntax_family; PropTerm => AccDescent {
                        state_ty: state_ty.try_into()?,
                        result_ty: result_ty
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        step: step.try_into()?,
                        from: from.try_into()?,
                        to: to.try_into()?,
                        accessibility: accessibility
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                        transition: transition
                            .try_into()
                            .map_err(|e| format!("{e:?}"))?,
                    })
                }
            },
            ExpNode::BoxApp { function, argument } => {
                let ty = self.infer(function, ctx, m)?;
                let head = raw::calculus::whnf(self.raw, ty);
                let ExpNode::BoxType {
                    program_ty: raw::program::ProgramType::ComputationType(ty),
                } = self.raw.arena().get(head)
                else {
                    return Err("expected boxed function".into());
                };
                let raw::program::ComputationTypeNode::Function { domain, codomain } =
                    self.raw.arena().get(ty)
                else {
                    return Err("expected Program function".into());
                };
                let domain = self.value_type(domain)?;
                let codomain = self.computation_type(codomain)?;
                let rule = k::ProductRule::new(
                    k::Sort::Base(self.kernel.arena().sort(domain)),
                    k::Sort::Base(self.kernel.arena().sort(codomain)),
                )?;
                let function = self.set(function, ctx, m)?;
                let argument = self.set(argument, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetTerm => BoxApp {
                    rule,
                    domain,
                    codomain,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                })
            }
            ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee,
                branches,
            } => {
                self.datatype(indspec)?;
                let inductive = indspec;
                let binders = branches
                    .iter()
                    .map(|b| b.binders.clone())
                    .collect::<Vec<_>>();
                let result_ty = self.set(ty, ctx, m)?;
                let sty = self.infer(scrutinee, ctx, m)?;
                let head = raw::calculus::whnf(self.raw, sty);
                let ExpNode::IndType { parameters, .. } = self.raw.arena().get(head) else {
                    return Err("case scrutinee has no datatype".into());
                };
                let spec = self.raw.program_inductive(indspec);
                let mut bodies = vec![];
                for (branch, ctor) in branches.into_iter().zip(spec.constructors()) {
                    let mut local = ctx.clone();
                    for (i, ((_, field), var)) in
                        ctor.fields().iter().zip(&branch.binders).enumerate()
                    {
                        let field = raw::reflection::reflect_value_type(self.raw, *field)
                            .map_err(|e| e.to_string())?;
                        let field = raw::calculus::instantiate_telescope(
                            self.raw.arena(),
                            field,
                            &parameters,
                        );
                        local.push(ExpContextEntry {
                            var: *var,
                            ty: raw::calculus::shift_bound_indices(self.raw.arena(), field, i, 0),
                        });
                    }
                    bodies.push(self.set(branch.body, &mut local, m)?);
                }
                let branches = bodies;
                let scrutinee = self.set(scrutinee, ctx, m)?;
                logical_node!(self, sort, syntax_family; SetTerm => SetCase {
                    inductive,
                    binders,
                    result_ty: result_ty.try_into()?,
                    scrutinee: scrutinee.try_into()?,
                    branches: branches
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            ExpNode::ReflectedProgramParam(parameter) => {
                self.parameter(parameter)?;
                let binding = self
                    .raw
                    .module_parameter_opt(parameter)
                    .ok_or("unknown reflected parameter")?;
                match binding.kind {
                    raw::environment::ModuleParameterKind::ProgramType => {
                        let form = s::SetTypeForm::ReflectedProgramParam { parameter };
                        self.kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form,
                            })
                            .into()
                    }
                    raw::environment::ModuleParameterKind::ProgramValue { .. } => {
                        let form = s::SetTermForm::ReflectedProgramParam { parameter };
                        self.kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form,
                            })
                            .into()
                    }
                    _ => return Err("not a Program parameter".into()),
                }
            }
            ExpNode::Meta { .. } => return Err("unresolved metavariable at kernel boundary".into()),
            ExpNode::Sort(_) => unreachable!(),
        };
        self.cache.insert(key, result);
        Ok(result)
    }
}
