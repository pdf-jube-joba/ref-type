//! Classify Set/Prop expressions and attach kernel product rules.
use super::*;

impl Lowerer<'_> {
    pub(crate) fn set(
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
            ExpNode::Bound(index) => match syntax_family {
                s::Family::SetTerm => self
                    .kernel
                    .arena()
                    .alloc(s::SetTermNode {
                        level: sort.level().ok_or("expected Set level")?,
                        form: s::SetTermForm::Bound { index },
                    })
                    .into(),
                s::Family::PropTerm => self
                    .kernel
                    .arena()
                    .alloc(s::PropTermNode {
                        form: s::PropTermForm::Bound { index },
                    })
                    .into(),
                s::Family::SetType => self
                    .kernel
                    .arena()
                    .alloc(s::SetTypeNode {
                        level: sort.level().ok_or("expected Set level")?,
                        form: s::SetTypeForm::Bound { index },
                    })
                    .into(),
                s::Family::PropType => self
                    .kernel
                    .arena()
                    .alloc(s::PropTypeNode {
                        form: s::PropTypeForm::Bound { index },
                    })
                    .into(),
                _ => return Err("constructor cannot inhabit this syntax family".into()),
            },
            ExpNode::ModuleParam(parameter) => {
                self.parameter(parameter)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::SetKind => self
                        .kernel
                        .arena()
                        .alloc(s::SetKindNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetKindForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::PropKind => self
                        .kernel
                        .arena()
                        .alloc(s::PropKindNode {
                            form: s::PropKindForm::ModuleParam { parameter },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::DefinedConstant(definition) => {
                self.definition(definition)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::Constant { definition },
                        })
                        .into(),
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::Constant { definition },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::Constant { definition },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Constant { definition },
                        })
                        .into(),
                    s::Family::SetKind => self
                        .kernel
                        .arena()
                        .alloc(s::SetKindNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetKindForm::Constant { definition },
                        })
                        .into(),
                    s::Family::PropKind => self
                        .kernel
                        .arena()
                        .alloc(s::PropKindNode {
                            form: s::PropKindForm::Constant { definition },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::Subset {
                                var,
                                set: set.try_into().map_err(|e| format!("{e:?}"))?,
                                predicate: predicate.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::PowerSet { set } => {
                let set = self.set(set, ctx, m)?;
                match syntax_family {
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::PowerSet {
                                set: set.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::SubsetIntro {
                                superset: superset.try_into().map_err(|e| format!("{e:?}"))?,
                                subset: subset.try_into().map_err(|e| format!("{e:?}"))?,
                                element: element.try_into().map_err(|e| format!("{e:?}"))?,
                                proof: proof.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::TypeLift { superset, subset } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                match syntax_family {
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::TypeLift {
                                superset: superset.try_into().map_err(|e| format!("{e:?}"))?,
                                subset: subset.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::Pred {
                superset,
                subset,
                element,
            } => {
                let superset = self.set(superset, ctx, m)?;
                let subset = self.set(subset, ctx, m)?;
                let element = self.set(element, ctx, m)?;
                match syntax_family {
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Pred {
                                superset: superset.try_into().map_err(|e| format!("{e:?}"))?,
                                subset: subset.try_into().map_err(|e| format!("{e:?}"))?,
                                element: element.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::Equal { left, right } => {
                let left = self.set(left, ctx, m)?;
                let right = self.set(right, ctx, m)?;
                match syntax_family {
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Equal {
                                left: left.try_into().map_err(|e| format!("{e:?}"))?,
                                right: right.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::Exists { set } => {
                let set = self.set(set, ctx, m)?;
                match syntax_family {
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Exists {
                                set: set.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                match syntax_family {
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::RunStep {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let next = self.set(next, ctx, m)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::Continue {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                next: next.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.set(state_ty, ctx, m)?;
                let result_ty = self.set(result_ty, ctx, m)?;
                let output = self.set(output, ctx, m)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::Finish {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                output: output.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Acc {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                step: step.try_into().map_err(|e| format!("{e:?}"))?,
                                state: state.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::SetRun {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                step: step.try_into().map_err(|e| format!("{e:?}"))?,
                                initial: initial.try_into().map_err(|e| format!("{e:?}"))?,
                                accessibility: accessibility
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::SetRunCase {
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                step: step.try_into().map_err(|e| format!("{e:?}"))?,
                                initial: initial.try_into().map_err(|e| format!("{e:?}"))?,
                                transition: transition.try_into().map_err(|e| format!("{e:?}"))?,
                                accessibility: accessibility
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                transition_equality: transition_equality
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::TakeSet {
                                domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                codomain: codomain.try_into().map_err(|e| format!("{e:?}"))?,
                                map: map.try_into().map_err(|e| format!("{e:?}"))?,
                                existence: existence.try_into().map_err(|e| format!("{e:?}"))?,
                                uniqueness: uniqueness.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::TakeProp {
                                domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                proposition: proposition
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                map: map.try_into().map_err(|e| format!("{e:?}"))?,
                                existence: existence.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::BoxType { program_ty } => {
                let program_ty = self.program_type(program_ty)?;
                match syntax_family {
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::BoxType { program_ty },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::BoxProgram {
                program_ty,
                program,
                certified_reflection,
            } => {
                let program_ty = self.program_type(program_ty)?;
                let program = self.program_term(program)?;
                let certified_reflection = self.set(certified_reflection, ctx, m)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::BoxProgram {
                                program_ty,
                                program,
                                certified_reflection: certified_reflection
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
            }
            ExpNode::ForceBox { program_ty, boxed } => {
                let program_ty = self.program_type(program_ty)?;
                let boxed = self.set(boxed, ctx, m)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::ForceBox {
                                program_ty,
                                boxed: boxed.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::IndType {
                                inductive,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::IndType {
                                inductive,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::SetKind => self
                        .kernel
                        .arena()
                        .alloc(s::SetKindNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetKindForm::IndType {
                                inductive,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::PropKind => self
                        .kernel
                        .arena()
                        .alloc(s::PropKindNode {
                            form: s::PropKindForm::IndType {
                                inductive,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::IndCtor {
                                inductive,
                                constructor,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::IndCtor {
                                inductive,
                                constructor,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::IndCtor {
                                inductive,
                                constructor,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::IndCtor {
                                inductive,
                                constructor,
                                parameters: parameters
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::IndElim {
                                inductive,
                                motive_vars,
                                scrutinee,
                                motive_domains,
                                motive_body,
                                cases,
                            },
                        })
                        .into(),
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::IndElim {
                                inductive,
                                motive_vars,
                                scrutinee,
                                motive_domains,
                                motive_body,
                                cases,
                            },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::IndElim {
                                inductive,
                                motive_vars,
                                scrutinee,
                                motive_domains,
                                motive_body,
                                cases,
                            },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::IndElim {
                                inductive,
                                motive_vars,
                                scrutinee,
                                motive_domains,
                                motive_body,
                                cases,
                            },
                        })
                        .into(),
                    _ => return Err("eliminator cannot return a kind".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::Recursor {
                                rule,
                                var,
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                motive: motive.try_into().map_err(|e| format!("{e:?}"))?,
                                on_continue: on_continue
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                on_finish: on_finish.try_into().map_err(|e| format!("{e:?}"))?,
                                scrutinee: scrutinee.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    s::Family::PropTerm => self
                        .kernel
                        .arena()
                        .alloc(s::PropTermNode {
                            form: s::PropTermForm::Recursor {
                                rule,
                                var,
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                motive: motive.try_into().map_err(|e| format!("{e:?}"))?,
                                on_continue: on_continue
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                on_finish: on_finish.try_into().map_err(|e| format!("{e:?}"))?,
                                scrutinee: scrutinee.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTypeForm::Recursor {
                                rule,
                                var,
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                motive: motive.try_into().map_err(|e| format!("{e:?}"))?,
                                on_continue: on_continue
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                on_finish: on_finish.try_into().map_err(|e| format!("{e:?}"))?,
                                scrutinee: scrutinee.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    s::Family::PropType => self
                        .kernel
                        .arena()
                        .alloc(s::PropTypeNode {
                            form: s::PropTypeForm::Recursor {
                                rule,
                                var,
                                state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                motive: motive.try_into().map_err(|e| format!("{e:?}"))?,
                                on_continue: on_continue
                                    .try_into()
                                    .map_err(|e| format!("{e:?}"))?,
                                on_finish: on_finish.try_into().map_err(|e| format!("{e:?}"))?,
                                scrutinee: scrutinee.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match (matches!(node, ExpNode::Prod { .. }), domain_sort.is_upper()) {
                    (true, false) => match syntax_family {
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::ProdTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::ProdTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetKind => self
                            .kernel
                            .arena()
                            .alloc(s::SetKindNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetKindForm::ProdTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropKind => self
                            .kernel
                            .arena()
                            .alloc(s::PropKindNode {
                                form: s::PropKindForm::ProdTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    },
                    (true, true) => match syntax_family {
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::ProdType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::ProdType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetKind => self
                            .kernel
                            .arena()
                            .alloc(s::SetKindNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetKindForm::ProdType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropKind => self
                            .kernel
                            .arena()
                            .alloc(s::PropKindNode {
                                form: s::PropKindForm::ProdType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    },
                    (false, false) => match syntax_family {
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTermForm::LambdaTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::LambdaTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::LambdaTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::LambdaTerm {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    },
                    (false, true) => match syntax_family {
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTermForm::LambdaType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::LambdaType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::LambdaType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::LambdaType {
                                    rule,
                                    var,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    body: body.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    },
                }
            }
            ExpNode::App { func, arg } => {
                let ty = self.infer(func, ctx, m)?;
                let (_, domain, codomain) = raw::calculus::expose_product(self.raw, ty)
                    .ok_or("application does not have product type")?;
                let s = self.formation(domain, ctx, m)?;
                let t = self.under(ctx, SymbolId::ANONYMOUS, domain, |this, ctx| {
                    this.formation(codomain, ctx, m)
                })?;
                let rule = k::ProductRule::new(s, t)?;
                let function = self.set(func, ctx, m)?;
                let argument = self.set(arg, ctx, m)?;
                if s.is_upper() {
                    match syntax_family {
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTermForm::AppType {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::AppType {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::AppType {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::AppType {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                } else {
                    match syntax_family {
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTermForm::AppTerm {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::AppTerm {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::SetType => self
                            .kernel
                            .arena()
                            .alloc(s::SetTypeNode {
                                level: sort.level().ok_or("expected Set level")?,
                                form: s::SetTypeForm::AppTerm {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        s::Family::PropType => self
                            .kernel
                            .arena()
                            .alloc(s::PropTypeNode {
                                form: s::PropTypeForm::AppTerm {
                                    rule,
                                    function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                    argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                }
            }
            ExpNode::Prove(prove) => match prove {
                Prove::IdRefl { element } => {
                    let element = self.set(element, ctx, m)?;
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::IdRefl {
                                    element: element.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                }
                Prove::ExistsIntro { element, set } => {
                    let element = self.set(element, ctx, m)?;
                    let set = self.set(set, ctx, m)?;
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::ExistsIntro {
                                    element: element.try_into().map_err(|e| format!("{e:?}"))?,
                                    set: set.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                }
                Prove::SubsetElim {
                    element,
                    subset,
                    superset,
                } => {
                    let element = self.set(element, ctx, m)?;
                    let subset = self.set(subset, ctx, m)?;
                    let superset = self.set(superset, ctx, m)?;
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::SubsetElim {
                                    element: element.try_into().map_err(|e| format!("{e:?}"))?,
                                    subset: subset.try_into().map_err(|e| format!("{e:?}"))?,
                                    superset: superset.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::IdElim {
                                    var,
                                    left: left.try_into().map_err(|e| format!("{e:?}"))?,
                                    right: right.try_into().map_err(|e| format!("{e:?}"))?,
                                    ty: ty.try_into().map_err(|e| format!("{e:?}"))?,
                                    predicate: predicate
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    base: base.try_into().map_err(|e| format!("{e:?}"))?,
                                    equality: equality.try_into().map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::TakeEq {
                                    func: func.try_into().map_err(|e| format!("{e:?}"))?,
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    codomain: codomain.try_into().map_err(|e| format!("{e:?}"))?,
                                    element: element.try_into().map_err(|e| format!("{e:?}"))?,
                                    existence: existence
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    uniqueness: uniqueness
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::SetExt {
                                    left: left.try_into().map_err(|e| format!("{e:?}"))?,
                                    right: right.try_into().map_err(|e| format!("{e:?}"))?,
                                    left_to_right: left_to_right
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    right_to_left: right_to_left
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                }
                Prove::Axiom(Axiom::FunExt {
                    left,
                    right,
                    pointwise,
                }) => {
                    let left = self.set(left, ctx, m)?;
                    let right = self.set(right, ctx, m)?;
                    let pointwise = self.set(pointwise, ctx, m)?;
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::FunExt {
                                    left: left.try_into().map_err(|e| format!("{e:?}"))?,
                                    right: right.try_into().map_err(|e| format!("{e:?}"))?,
                                    pointwise: pointwise
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
                }
                Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
                    domain,
                    family,
                    inhabited,
                }) => {
                    let domain = self.set(domain, ctx, m)?;
                    let family = self.set(family, ctx, m)?;
                    let inhabited = self.set(inhabited, ctx, m)?;
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::ClassicalIndefiniteChoice {
                                    domain: domain.try_into().map_err(|e| format!("{e:?}"))?,
                                    family: family.try_into().map_err(|e| format!("{e:?}"))?,
                                    inhabited: inhabited
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::AccIntro {
                                    state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                    result_ty: result_ty
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    step: step.try_into().map_err(|e| format!("{e:?}"))?,
                                    state: state.try_into().map_err(|e| format!("{e:?}"))?,
                                    predecessors: predecessors
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                    match syntax_family {
                        s::Family::PropTerm => self
                            .kernel
                            .arena()
                            .alloc(s::PropTermNode {
                                form: s::PropTermForm::AccDescent {
                                    state_ty: state_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                    result_ty: result_ty
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    step: step.try_into().map_err(|e| format!("{e:?}"))?,
                                    from: from.try_into().map_err(|e| format!("{e:?}"))?,
                                    to: to.try_into().map_err(|e| format!("{e:?}"))?,
                                    accessibility: accessibility
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                    transition: transition
                                        .try_into()
                                        .map_err(|e| format!("{e:?}"))?,
                                },
                            })
                            .into(),
                        _ => return Err("constructor cannot inhabit this syntax family".into()),
                    }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::BoxApp {
                                rule,
                                domain,
                                codomain,
                                function: function.try_into().map_err(|e| format!("{e:?}"))?,
                                argument: argument.try_into().map_err(|e| format!("{e:?}"))?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            level: sort.level().ok_or("expected Set level")?,
                            form: s::SetTermForm::SetCase {
                                inductive,
                                binders,
                                result_ty: result_ty.try_into().map_err(|e| format!("{e:?}"))?,
                                scrutinee: scrutinee.try_into().map_err(|e| format!("{e:?}"))?,
                                branches: branches
                                    .into_iter()
                                    .map(TryInto::try_into)
                                    .collect::<Result<_, _>>()?,
                            },
                        })
                        .into(),
                    _ => return Err("constructor cannot inhabit this syntax family".into()),
                }
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
