//! Elaboration boundary: attach syntax families and rule labels, then check in the kernel.
use crate::raw::{self, exp::*, ids::*, sort::Sort as RawSort};
use kernel::stratified::{environment as ke, sort as k, syntax as s};
use std::collections::{HashMap, HashSet};

mod declarations;
mod logical;
mod program;

pub(crate) struct Lowerer<'a> {
    raw: &'a raw::environment::CrateEnv,
    pub(crate) kernel: &'a mut ke::Environment,
    active: HashSet<InductiveId>,
    checked_templates: HashSet<DefId>,
    active_program: HashSet<ProgramInductiveId>,
    cache: HashMap<(Exp, Vec<Exp>, ModuleId), s::Expression>,
}

impl<'a> Lowerer<'a> {
    pub(crate) fn new(
        raw: &'a raw::environment::CrateEnv,
        kernel: &'a mut ke::Environment,
    ) -> Self {
        Self {
            raw,
            kernel,
            active: HashSet::new(),
            checked_templates: HashSet::new(),
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

    fn logical_base_kind(&self, sort: k::BaseSort) -> Result<s::Expression, String> {
        Ok(match sort {
            k::BaseSort::Set(level) => self
                .kernel
                .arena()
                .alloc(s::SetKindNode {
                    level,
                    form: s::SetKindForm::Base,
                })
                .into(),
            k::BaseSort::Prop => self
                .kernel
                .arena()
                .alloc(s::PropKindNode {
                    form: s::PropKindForm::Base,
                })
                .into(),
            _ => return Err("expected Set/Prop sort".into()),
        })
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
}
