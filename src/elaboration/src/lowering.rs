//! Source identities, module capture telescopes, and checked kernel declarations.
use crate::raw::{self, exp::*, ids::*, sort::Sort as RawSort};
use kernel::{environment as ke, sort as k, syntax as s};
use rustc_hash::{FxHashMap, FxHashSet};

mod captures;
use captures::{Declaration, Scope};
mod declarations;
pub(crate) mod diagnostics;
mod logical;
mod program;
mod queries;

pub(crate) struct Lowerer<'a> {
    raw: &'a raw::environment::CrateEnv,
    pub(crate) kernel: &'a mut ke::Environment,
    metas: kernel::metavariables::MetaContext,
    pub(crate) structural: bool,
    active_parameters: FxHashSet<ModuleParamId>,
    active: FxHashSet<InductiveId>,
    active_program: FxHashSet<ProgramInductiveId>,
    scope: Scope,
    capture_cache: FxHashMap<Declaration, Vec<ModuleParamId>>,
    // Translation uses binder depth, not binding classifiers. Type checking
    // still uses the full telescope in the kernel. `in_scope` isolates captures,
    // logical/proof bases and nominal mode; Program mode can change within it.
    cache: FxHashMap<(Exp, usize, ModuleId, usize, bool), s::Expression>,
}

impl<'a> Lowerer<'a> {
    pub(crate) fn new(
        raw: &'a raw::environment::CrateEnv,
        kernel: &'a mut ke::Environment,
    ) -> Self {
        if kernel.arena().is_empty() {
            *kernel = ke::Environment::with_arena(raw.arena().core.clone());
        }
        Self {
            raw,
            kernel,
            metas: kernel::metavariables::MetaContext::new(),
            structural: false,
            active_parameters: FxHashSet::default(),
            active: FxHashSet::default(),
            active_program: FxHashSet::default(),
            scope: Scope::default(),
            capture_cache: FxHashMap::default(),
            cache: FxHashMap::default(),
        }
    }

    fn native_reference(&self, e: s::Expression) -> bool {
        if !self.scope.nominal {
            return false;
        }
        match self.kernel.arena().get(e) {
            s::Node::Definition { .. } => true,
            s::Node::Inductive {
                inductive,
                parameters,
            }
            | s::Node::InductiveConstructor {
                inductive,
                parameters,
                ..
            } => self.kernel.datatype(inductive).is_some_and(|spec| {
                parameters.len() == spec.parameters.len()
                    && spec.parameters.len()
                        > self
                            .raw
                            .program_inductive(inductive.into())
                            .parameters()
                            .len()
            }),
            _ => false,
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

    pub(crate) fn nominal(&mut self, base: usize) {
        if !self.scope.nominal || self.scope.logical_base != base {
            self.cache.clear();
        }
        self.scope.nominal = true;
        self.scope.logical_base = base;
    }
    fn nominal_parameter(
        &mut self,
        id: ModuleParamId,
    ) -> Result<s::Expression, crate::error::Error> {
        if self.structural && self.raw.module_parameter_opt(id).is_none() {
            return Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())));
        }
        if self.kernel.parameter(id.into()).is_some() {
            return Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())));
        }
        if !self.active_parameters.insert(id) {
            return Err(crate::error::Error::Invalid(
                crate::error::Invalid::CyclicModuleParameterType,
            ));
        }
        let parameter = self
            .raw
            .module_parameter_opt(id)
            .ok_or(crate::error::Error::Invalid(
                crate::error::Invalid::UnknownModuleParameter,
            ))?
            .clone();
        let ty = self.in_scope(vec![], 0, 0, |this| {
            this.scope.nominal = true;
            match parameter.kind {
                raw::environment::ModuleParameterKind::Pts { ty } => {
                    this.set(ty, &mut vec![], id.module)
                }
                raw::environment::ModuleParameterKind::ProgramType => Ok(this
                    .kernel
                    .arena()
                    .sort(k::Sort::Base(k::BaseSort::Value(0)))),
                raw::environment::ModuleParameterKind::ProgramValue { ty } => this.value_type(ty),
            }
        });
        self.active_parameters.remove(&id);
        self.kernel
            .register_parameter(id.into(), ty?)
            .map_err(crate::error::Error::from)?;
        Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())))
    }
    pub(crate) fn nominal_context(
        &mut self,
        context: &ExpContext,
        base: usize,
        module: ModuleId,
    ) -> Result<s::Context, crate::error::Error> {
        self.nominal(base);
        let mut prefix = context[..base].to_vec();
        let mut result = vec![];
        for binding in &context[base..] {
            let ty = self.set(binding.ty, &mut prefix, module)?;
            result.push(s::Binding {
                var: binding.var,
                ty,
            });
            prefix.push(binding.clone());
        }
        Ok(result)
    }
    fn logical_base_kind(&self, sort: k::BaseSort) -> Result<s::Expression, crate::error::Error> {
        Ok(self.kernel.arena().sort(k::Sort::Base(sort)))
    }

    fn under<T>(
        &mut self,
        ctx: &mut ExpContext,
        var: SymbolId,
        ty: Exp,
        f: impl FnOnce(&mut Self, &mut ExpContext) -> Result<T, crate::error::Error>,
    ) -> Result<T, crate::error::Error> {
        ctx.push(ExpContextEntry { var, ty });
        let r = f(self, ctx);
        ctx.pop();
        r
    }

    pub(crate) fn context(
        &mut self,
        ctx: &ExpContext,
        m: ModuleId,
    ) -> Result<ke::Context, crate::error::Error> {
        let mut prefix = ctx[..self.scope.logical_base].to_vec();
        let mut result = self.capture_context(false)?;
        for b in &ctx[self.scope.logical_base..] {
            let classifier = self.set(b.ty, &mut prefix, m)?;
            result.push(ke::Binding {
                var: b.var,
                ty: classifier,
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
    ) -> Result<s::Expression, crate::error::Error> {
        self.set(e, ctx, m)
    }
}

pub(crate) fn format_kernel_error(
    raw: &raw::environment::CrateEnv,
    error: &kernel::metavariables::Error,
) -> String {
    diagnostics::format_error(raw, error)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translation_shares_depth_without_sharing_typing_judgements() {
        let raw = raw::environment::CrateEnv::new();
        let mut kernel = ke::Environment::new();
        let mut lower = Lowerer::new(&raw, &mut kernel);
        lower.nominal(0);
        let e = raw.arena().alloc(ExpNode::Ascribe {
            term: raw.arena().exp_bound(0),
            ty: raw.arena().sort(RawSort::Set(0)),
        });
        let module = raw.root_module();
        let mut metas = kernel::metavariables::MetaContext::new();
        for (sort, valid) in [(RawSort::Set(0), true), (RawSort::Prop, false)] {
            let mut context = vec![ExpContextEntry {
                var: SymbolId::ANONYMOUS,
                ty: raw.arena().sort(sort),
            }];
            let term = lower.set(e, &mut context, module).unwrap();
            let context = lower.nominal_context(&context, 0, module).unwrap();
            assert_eq!(
                kernel::check::Checker::new(lower.kernel, &mut metas, context)
                    .infer(term)
                    .is_ok(),
                valid
            );
        }
        // Reflection depends on binder depth even when the source term is shared.
        lower
            .in_scope(vec![], 0, 0, |lower| {
                lower.scope.proof_base = Some(1);
                let bound = raw.arena().exp_bound(0);
                let binding = ExpContextEntry {
                    var: SymbolId::ANONYMOUS,
                    ty: raw.arena().sort(RawSort::Set(0)),
                };
                let reflected = lower.set(bound, &mut vec![binding.clone()], module)?;
                assert!(matches!(
                    lower.kernel.arena().get(reflected),
                    s::Node::Reflect { .. }
                ));
                let local = lower.set(bound, &mut vec![binding.clone(), binding], module)?;
                assert_eq!(lower.kernel.arena().get(local), s::Node::Bound(0));
                Ok(())
            })
            .unwrap();
    }
}
