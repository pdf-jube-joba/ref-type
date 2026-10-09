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
    // A captured telescope is independent of local binders. Preserve its
    // classifiers across declaration scopes, keyed by the complete telescope.
    capture_context_cache: FxHashMap<(Vec<ModuleParamId>, bool, bool), ke::Context>,
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
            capture_context_cache: FxHashMap::default(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn captured_classifier_indices_follow_the_complete_telescope() {
        use raw::environment::{ModuleParameter, ModuleParameterKind};
        let mut raw = raw::environment::CrateEnv::new();
        let module = raw.reserve_child_module(raw.root_module(), "Captured".into());
        let a = ModuleParamId {
            module,
            position: 0,
        };
        let b = ModuleParamId {
            module,
            position: 1,
        };
        let x = ModuleParamId {
            module,
            position: 2,
        };
        for ty in [
            raw.arena().sort(RawSort::Set(0)),
            raw.arena().sort(RawSort::Prop),
            raw.arena().alloc(ExpNode::ModuleParam(a)),
        ] {
            raw.add_module_parameter(
                module,
                ModuleParameter {
                    name: SymbolId::ANONYMOUS,
                    kind: ModuleParameterKind::Pts { ty },
                },
            );
        }
        let mut kernel = ke::Environment::new();
        let mut lower = Lowerer::new(&raw, &mut kernel);
        for (captures, expected) in [(vec![a, x], 0), (vec![a, b, x], 1), (vec![a, x], 0)] {
            lower
                .in_scope(captures, 0, 0, |lower| {
                    let context = lower.capture_context(false)?;
                    assert_eq!(
                        lower.kernel.arena().get(context.last().unwrap().ty),
                        s::Node::Bound(expected)
                    );
                    Ok(())
                })
                .unwrap();
        }
    }

    #[test]
    fn reserved_inductive_keeps_source_identity_before_canonicalization() {
        use raw::environment::{
            DeclarationRemapping, ModuleArgument, ModuleParameter, ModuleParameterKind,
        };
        let mut raw = raw::environment::CrateEnv::new();
        let source_module = raw.reserve_child_module(raw.root_module(), "Source".into());
        let caller = raw.reserve_child_module(raw.root_module(), "Caller".into());
        for module in [source_module, caller] {
            raw.add_module_parameter(
                module,
                ModuleParameter {
                    name: SymbolId::ANONYMOUS,
                    kind: ModuleParameterKind::Pts {
                        ty: raw.arena().sort(RawSort::Set(0)),
                    },
                },
            );
        }
        let source_parameter = ModuleParamId {
            module: source_module,
            position: 0,
        };
        let caller_parameter = ModuleParamId {
            module: caller,
            position: 0,
        };
        let source = raw.add_inductive(
            source_module,
            raw::inductive::InductiveTypeSpecs::unchecked(vec![], vec![], RawSort::Set(0), vec![]),
        );
        let caller_type = raw.arena().exp_module_param(caller_parameter);
        let adapter = raw.arena().alloc(ExpNode::Prod {
            var: SymbolId::ANONYMOUS,
            ty: caller_type,
            body: caller_type,
        });
        let reflected = vec![(source_parameter, adapter)];
        let substitutions = vec![(source_parameter, ModuleArgument::Pts(adapter))];
        let reserved_module = raw.add_module();
        let reserved = raw.reserve_lazy_inductive(reserved_module, source, reflected.clone());
        let remapping = DeclarationRemapping::default();
        raw.preview_lazy_inductive(reserved, &substitutions, &reflected, &remapping);
        let expression = raw.arena().alloc(ExpNode::IndType {
            indspec: reserved,
            parameters: vec![],
        });
        let mut kernel = ke::Environment::new();
        let before = Lowerer::new(&raw, &mut kernel)
            .in_scope(vec![caller_parameter], 0, 0, |lower| {
                lower.set(expression, &mut vec![], caller)
            })
            .unwrap();
        let s::Node::IndType {
            inductive,
            parameters,
        } = kernel.arena().get(before)
        else {
            panic!("expected an inductive reference")
        };
        assert_eq!(inductive, source.into());
        assert_eq!(parameters.len(), 1);
        assert!(matches!(
            kernel.arena().get(parameters[0]),
            s::Node::Product { .. }
        ));
        assert!(kernel.inductive(reserved.into()).is_none());
        raw.reuse_lazy_inductive(reserved, &substitutions, &reflected, &remapping);
        let after = Lowerer::new(&raw, &mut kernel)
            .in_scope(vec![caller_parameter], 0, 0, |lower| {
                lower.set(expression, &mut vec![], caller)
            })
            .unwrap();
        assert_eq!(before, after);
    }

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
