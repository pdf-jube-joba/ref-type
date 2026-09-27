//! Source identities, module capture telescopes, and checked kernel declarations.
use crate::raw::{self, exp::*, ids::*, sort::Sort as RawSort};
use kernel::sharing::ContextId;
use kernel::{environment as ke, sort as k, syntax as s};
use rustc_hash::FxHashMap;
use std::collections::HashSet;

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
    active_parameters: HashSet<ModuleParamId>,
    active: HashSet<InductiveId>,
    active_program: HashSet<ProgramInductiveId>,
    scope: Scope,
    capture_cache: FxHashMap<Declaration, Vec<ModuleParamId>>,
    cache: FxHashMap<(Exp, ContextId, ModuleId), s::Expression>,
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
            active_parameters: HashSet::new(),
            active: HashSet::new(),
            active_program: HashSet::new(),
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
            s::Node::IndType {
                inductive,
                parameters,
            }
            | s::Node::IndCtor {
                inductive,
                parameters,
                ..
            } => self
                .raw
                .arena()
                .inductive_captures
                .borrow()
                .get(&inductive)
                .is_some_and(|(captures, explicit)| {
                    *captures > 0 && parameters.len() == captures + explicit
                }),
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
        self.scope.nominal = true;
        self.scope.logical_base = base;
    }
    fn nominal_parameter(&mut self, id: ModuleParamId) -> Result<s::Expression, String> {
        if self.structural && self.raw.module_parameter_opt(id).is_none() {
            return Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())));
        }
        if self.kernel.parameter(id.into()).is_some() {
            return Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())));
        }
        if !self.active_parameters.insert(id) {
            return Err("cyclic module parameter type".into());
        }
        let parameter = self
            .raw
            .module_parameter_opt(id)
            .ok_or("unknown module parameter")?
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
            .map_err(|e| e.to_string())?;
        Ok(self.kernel.arena().alloc(s::Node::Parameter(id.into())))
    }
    pub(crate) fn nominal_context(
        &mut self,
        context: &ExpContext,
        base: usize,
        module: ModuleId,
    ) -> Result<s::Context, String> {
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
    fn logical_base_kind(&self, sort: k::BaseSort) -> Result<s::Expression, String> {
        Ok(self.kernel.arena().sort(k::Sort::Base(sort)))
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
    ) -> Result<s::Expression, String> {
        self.set(e, ctx, m)
    }
}

pub(crate) fn format_kernel_error(
    raw: &raw::environment::CrateEnv,
    error: &kernel::metavariables::Error,
) -> String {
    diagnostics::format_error(raw, error)
}
