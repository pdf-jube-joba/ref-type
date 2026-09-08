//! Elaboration boundary: attach syntax families and rule labels, then check in the kernel.
use crate::raw::{self, exp::*, ids::*, sort::Sort as RawSort};
use kernel::stratified::{environment as ke, sort as k, syntax as s};
use std::collections::{HashMap, HashSet};

pub(crate) struct Lowerer<'a> {
    raw: &'a raw::environment::CrateEnv,
    pub(crate) kernel: ke::Environment,
    active: HashSet<InductiveId>,
    active_program: HashSet<ProgramInductiveId>,
    cache: HashMap<(Exp, Vec<Exp>, ModuleId), s::Expression>,
}

impl<'a> Lowerer<'a> {
    pub(crate) fn new(raw: &'a raw::environment::CrateEnv) -> Self {
        Self {
            raw,
            kernel: ke::Environment::new(),
            active: HashSet::new(),
            active_program: HashSet::new(),
            cache: HashMap::new(),
        }
    }

    fn sort(s: RawSort) -> k::Sort {
        match s {
            RawSort::Set(i) => k::Sort::Base(k::BaseSort::Set(i)),
            RawSort::Prop => k::Sort::Base(k::BaseSort::Prop),
            RawSort::SetKind(i) => k::Sort::Upper(k::BaseSort::Set(i)),
            RawSort::PropKind => k::Sort::Upper(k::BaseSort::Prop),
        }
    }

    fn infer(&self, e: Exp, ctx: &mut ExpContext, m: ModuleId) -> Result<Exp, String> {
        raw::derivation::CheckSession::new(self.raw, m, ctx)
            .infer_pts(e)
            .map_err(|e| format!("classification: {e:?}"))
    }

    fn formation(&self, e: Exp, ctx: &mut ExpContext, m: ModuleId) -> Result<k::Sort, String> {
        raw::derivation::CheckSession::new(self.raw, m, ctx)
            .infer_sort(e)
            .map(Self::sort)
            .map_err(|e| format!("classification formation: {e:?}"))
    }

    fn under<T>(
        &mut self,
        ctx: &mut ExpContext,
        var: SymbolId,
        ty: Exp,
        f: impl FnOnce(&mut Self, &mut ExpContext) -> Result<T, String>,
    ) -> Result<T, String> {
        ctx.push(ExpContextEntry { var, ty });
        let r = f(self, ctx);
        ctx.pop();
        r
    }

    pub(crate) fn context(&mut self, ctx: &ExpContext, m: ModuleId) -> Result<ke::Context, String> {
        let mut prefix = vec![];
        let mut result = vec![];
        for b in ctx {
            let classifier = self.set(b.ty, &mut prefix, m)?;
            result.push(ke::Binding {
                var: b.var,
                classifier,
            });
            prefix.push(b.clone())
        }
        Ok(result)
    }

    pub(crate) fn classifier(
        &mut self,
        e: Exp,
        ctx: &mut ExpContext,
        m: ModuleId,
    ) -> Result<ke::Classifier, String> {
        if let ExpNode::Sort(s @ (RawSort::SetKind(_) | RawSort::PropKind)) =
            self.raw.arena().get(e)
        {
            Ok(ke::Classifier::Upper(Self::sort(s).base()))
        } else {
            Ok(self.set(e, ctx, m)?.into())
        }
    }

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
            return Ok(self
                .kernel
                .arena()
                .alloc(s::SetKindNode {
                    sort: sort.base().try_into().map_err(|e| format!("{e:?}"))?,
                    form: s::SetKindForm::Base,
                })
                .into());
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
        let sort_index: k::SetSort = sort.try_into().map_err(|e| format!("{e:?}"))?;
        let syntax_family = s::Family::at(sort, stage);
        let result = match node {
            ExpNode::Bound(index) => match syntax_family {
                s::Family::SetTerm => self
                    .kernel
                    .arena()
                    .alloc(s::SetTermNode {
                        sort: sort_index,
                        form: s::SetTermForm::Bound { index },
                    })
                    .into(),
                s::Family::SetType => self
                    .kernel
                    .arena()
                    .alloc(s::SetTypeNode {
                        sort: sort_index,
                        form: s::SetTypeForm::Bound { index },
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
                            sort: sort_index,
                            form: s::SetTermForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::ModuleParam { parameter },
                        })
                        .into(),
                    s::Family::SetKind => self
                        .kernel
                        .arena()
                        .alloc(s::SetKindNode {
                            sort: sort_index,
                            form: s::SetKindForm::ModuleParam { parameter },
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
                            sort: sort_index,
                            form: s::SetTermForm::Constant { definition },
                        })
                        .into(),
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::Constant { definition },
                        })
                        .into(),
                    s::Family::SetKind => self
                        .kernel
                        .arena()
                        .alloc(s::SetKindNode {
                            sort: sort_index,
                            form: s::SetKindForm::Constant { definition },
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::Pred {
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::Equal {
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::Exists {
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
                            form: s::SetTypeForm::Acc {
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            sort: sort_index,
                            form: s::SetTermForm::TakeProp {
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
                            sort: sort_index,
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
                let program = self.program(program)?;
                let certified_reflection = self.set(certified_reflection, ctx, m)?;
                match syntax_family {
                    s::Family::SetTerm => self
                        .kernel
                        .arena()
                        .alloc(s::SetTermNode {
                            sort: sort_index,
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
                            sort: sort_index,
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
                            sort: sort_index,
                            form: s::SetTypeForm::IndType {
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
                            sort: sort_index,
                            form: s::SetKindForm::IndType {
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
                            sort: sort_index,
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
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
                            sort: sort_index,
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
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
                            sort: sort_index,
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
                    s::Family::SetType => self
                        .kernel
                        .arena()
                        .alloc(s::SetTypeNode {
                            sort: sort_index,
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
                                sort: sort_index,
                                form: s::SetTypeForm::ProdTerm {
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
                                sort: sort_index,
                                form: s::SetKindForm::ProdTerm {
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
                                sort: sort_index,
                                form: s::SetTypeForm::ProdType {
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
                                sort: sort_index,
                                form: s::SetKindForm::ProdType {
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
                                sort: sort_index,
                                form: s::SetTermForm::LambdaTerm {
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
                                sort: sort_index,
                                form: s::SetTypeForm::LambdaTerm {
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
                                sort: sort_index,
                                form: s::SetTermForm::LambdaType {
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
                                sort: sort_index,
                                form: s::SetTypeForm::LambdaType {
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
                                sort: sort_index,
                                form: s::SetTermForm::AppType {
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
                                sort: sort_index,
                                form: s::SetTypeForm::AppType {
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
                                sort: sort_index,
                                form: s::SetTermForm::AppTerm {
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
                                sort: sort_index,
                                form: s::SetTypeForm::AppTerm {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::IdRefl {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::ExistsIntro {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::SubsetElim {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::IdElim {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::TakeEq {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::SetExt {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::FunExt {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::ClassicalIndefiniteChoice {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::AccIntro {
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
                        s::Family::SetTerm => self
                            .kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
                                form: s::SetTermForm::AccDescent {
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
                    program_ty: raw::program::ProgramType::Computation(ty),
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
                            sort: sort_index,
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
                            sort: sort_index,
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
                                sort: sort_index,
                                form,
                            })
                            .into()
                    }
                    raw::environment::ModuleParameterKind::ProgramValue { .. } => {
                        let form = s::SetTermForm::ReflectedProgramParam { parameter };
                        self.kernel
                            .arena()
                            .alloc(s::SetTermNode {
                                sort: sort_index,
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

    pub(crate) fn program_type(
        &mut self,
        ty: raw::program::ProgramType,
    ) -> Result<s::ProgramType, String> {
        match ty {
            raw::program::ProgramType::Value(t) => Ok(self.value_type(t)?.into()),
            raw::program::ProgramType::Computation(t) => Ok(self.computation_type(t)?.into()),
        }
    }

    fn value_type(&mut self, ty: raw::program::ValueType) -> Result<s::ValueType, String> {
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

    fn computation_type(
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

    fn program(&mut self, p: raw::program::Program) -> Result<s::Program, String> {
        self.program_in_context(p, &mut vec![])
    }

    pub(crate) fn program_in_context(
        &mut self,
        p: raw::program::Program,
        context: &mut raw::program::ProgramContext,
    ) -> Result<s::Program, String> {
        match p {
            raw::program::Program::Value(value) => Ok(self.value(value, context)?.into()),
            raw::program::Program::Computation(computation) => {
                Ok(self.computation(computation, context)?.into())
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
                raw::program::ProgramContextEntry::Type { var } => Ok(ke::Binding {
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
                raw::program::ProgramContextEntry::Value { var, ty } => Ok(ke::Binding {
                    var: *var,
                    classifier: self.value_type(*ty)?.into(),
                }),
            })
            .collect()
    }

    fn value(
        &mut self,
        v: raw::program::Value,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Value, String> {
        use raw::program::ValueNode as R;
        use s::ValueForm as F;
        let form = match self.raw.arena().get(v) {
            R::Bound(index) => F::Bound { index },
            R::ModuleParam(parameter) => {
                self.parameter(parameter)?;
                F::ModuleParam { parameter }
            }
            R::Meta { .. } => return Err("unresolved Program value".into()),
            R::DefinedConstant(definition) => {
                self.definition(definition)?;
                F::Constant { definition }
            }
            R::Thunk { computation } => F::ThunkValue {
                computation: self.computation(computation, ctx)?,
            },
            R::Continue {
                state_ty,
                result_ty,
                next,
            } => F::Continue {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                next: self.value(next, ctx)?,
            },
            R::Finish {
                state_ty,
                result_ty,
                output,
            } => F::Finish {
                state_ty: self.value_type(state_ty)?,
                result_ty: self.value_type(result_ty)?,
                output: self.value(output, ctx)?,
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
                        .map(|v| self.value(v, ctx))
                        .collect::<Result<_, _>>()?,
                }
            }
        };
        Ok(self.kernel.arena().alloc(s::ValueNode { level: 0, form }))
    }

    fn computation(
        &mut self,
        e: raw::program::Computation,
        ctx: &mut raw::program::ProgramContext,
    ) -> Result<s::Computation, String> {
        use raw::program::{ComputationNode as R, ProgramContextEntry};
        use s::ComputationForm as F;
        let form = match self.raw.arena().get(e) {
            R::Meta { .. } => return Err("unresolved computation".into()),
            R::DefinedConstant(definition) => {
                self.definition(definition)?;
                F::Constant { definition }
            }
            R::Return { value } => F::Return {
                value: self.value(value, ctx)?,
            },
            R::Force { value } => F::Force {
                value: self.value(value, ctx)?,
            },
            R::Lambda {
                var,
                value_ty,
                body,
            } => {
                let domain = self.value_type(value_ty)?;
                ctx.push(ProgramContextEntry::Value { var, ty: value_ty });
                let body = self.computation(body, ctx);
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
                function: self.computation(computation, ctx)?,
                argument: self.value(value, ctx)?,
            },
            R::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let computation = self.computation(computation, ctx)?;
                ctx.push(ProgramContextEntry::Value { var, ty: value_ty });
                let body = self.computation(body, ctx);
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
                let value = self.value(value, ctx)?;
                ctx.push(ProgramContextEntry::Value { var, ty: value_ty });
                let body = self.computation(body, ctx);
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
                step: self.value(step, ctx)?,
                initial: self.value(initial, ctx)?,
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
                step: self.value(step, ctx)?,
                initial: self.value(initial, ctx)?,
                transition: self.computation(transition, ctx)?,
            },
            R::Case {
                indspec,
                scrutinee,
                branches,
            } => {
                self.datatype(indspec)?;
                let mut checker = raw::program_derivation::ProgramCheckSession::new(self.raw, ctx);
                let ty = checker
                    .infer_computation(e)
                    .map_err(|e| format!("case inference: {e:?}"))?;
                let scrutinee_ty = checker
                    .infer_value(scrutinee)
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
                        local.push(ProgramContextEntry::Value {
                            var: *var,
                            ty: raw::program_calculus::shift_value_type_indices(
                                self.raw.arena(),
                                field,
                                j,
                                0,
                            ),
                        });
                    }
                    bodies.push(self.computation(branch.body, &mut local)?);
                }
                F::Case {
                    inductive: indspec,
                    binders,
                    result_ty: self.computation_type(ty)?,
                    scrutinee: self.value(scrutinee, ctx)?,
                    branches: bodies,
                }
            }
        };
        Ok(self
            .kernel
            .arena()
            .alloc(s::ComputationNode { level: 0, form }))
    }

    fn definition(&mut self, id: DefId) -> Result<(), String> {
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

    fn definition_ready(&mut self, id: DefId) -> Result<(), String> {
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
                let body = self.value(body, &mut vec![])?;
                (body.into(), ty.into(), vec![])
            }
            raw::environment::DefinedConstant::ProgramComputation { ty, body, .. } => {
                let ty = self.computation_type(ty)?;
                let body = self.computation(body, &mut vec![])?;
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

    fn parameter(&mut self, id: ModuleParamId) -> Result<(), String> {
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

    fn inductive(
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
            self.kernel
                .arena()
                .alloc(s::SetKindNode {
                    sort: sort.base().try_into().map_err(|e| format!("{e:?}"))?,
                    form: s::SetKindForm::Base,
                })
                .into()
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

    fn datatype(&mut self, id: ProgramInductiveId) -> Result<(), String> {
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

    pub(crate) fn extend(
        mut self,
        existing: ke::Environment,
    ) -> (ke::Environment, Result<(), String>) {
        self.kernel = existing;
        let result = self.lower_all();
        (self.kernel, result)
    }

    fn lower_all(&mut self) -> Result<(), String> {
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
        ComputationNode as C, ComputationTypeNode as CT, ValueNode as V, ValueTypeNode as VT,
    };
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum E {
        Set(Exp),
        Vt(raw::program::ValueType),
        Ct(raw::program::ComputationType),
        V(raw::program::Value),
        C(raw::program::Computation),
    }

    fn ty(t: raw::program::ProgramType) -> E {
        match t {
            raw::program::ProgramType::Value(x) => E::Vt(x),
            raw::program::ProgramType::Computation(x) => E::Ct(x),
        }
    }

    fn term(t: raw::program::Program) -> E {
        match t {
            raw::program::Program::Value(x) => E::V(x),
            raw::program::Program::Computation(x) => E::C(x),
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
