//! Elaboration boundary: attach syntax families and rule labels, then check in the kernel.
use crate::{exp::*, ids::*, sort::Sort as RawSort};
use kernel::sharing::ContextId;
use kernel::{environment as ke, sort as k, syntax as s};
use rustc_hash::FxHashMap;
use std::collections::HashSet;

mod bridge;
mod declarations;
mod logical;
mod nodes;
mod program;
use bridge::IdMap;
pub use bridge::KernelEnvironment;

pub struct Lowerer<'a> {
    raw: &'a crate::environment::CrateEnv,
    pub kernel: &'a mut ke::Environment,
    ids: &'a mut IdMap,
    active: HashSet<InductiveId>,
    active_program: HashSet<ProgramInductiveId>,
    cache: FxHashMap<(Exp, ContextId, ModuleId), s::Expression>,
}

impl<'a> Lowerer<'a> {
    pub fn new(raw: &'a crate::environment::CrateEnv, bridge: &'a mut KernelEnvironment) -> Self {
        Self {
            raw,
            kernel: &mut bridge.kernel,
            ids: &mut bridge.ids,
            active: HashSet::new(),
            active_program: HashSet::new(),
            cache: FxHashMap::default(),
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
        match sort {
            k::BaseSort::Set(_) | k::BaseSort::Prop => {
                kernel::construction::base_kind(self.kernel.arena(), sort)
            }
            _ => Err("expected Set/Prop sort".into()),
        }
    }

    fn infer(&self, e: Exp, ctx: &mut ExpContext) -> Result<Exp, String> {
        crate::derivation::CheckSession::new(self.raw, ctx)
            .infer_pts(e)
            .map_err(|e| format!("classification: {e:?}"))
    }

    fn formation(&self, e: Exp, ctx: &mut ExpContext) -> Result<k::Sort, String> {
        crate::derivation::CheckSession::new(self.raw, ctx)
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

    pub fn context(&mut self, ctx: &ExpContext, m: ModuleId) -> Result<ke::Context, String> {
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

    pub fn classifier(
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
