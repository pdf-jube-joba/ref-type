use crate::elaborator::ItemAccessResult;
use crate::raw::calculus::{exp_contains_bound, instantiate, shift_bound_indices};
use crate::raw::environment::{CrateEnv, DefinedConstant};
use crate::raw::exp::*;
use crate::raw::ids::*;
use crate::raw::inductive::InductiveTypeSpecs;
use crate::raw::program::{ComputationTerm, ComputationType};
use crate::syntax::*;

pub(crate) trait Handler {
    fn env(&self) -> &CrateEnv;
    fn arena(&self) -> &Arena;
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String>;
    fn field_projection(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        field_name: &Identifier,
    ) -> Result<Exp, String>;
    fn infer(&mut self, local_ctx: &mut ExpContext, e: Exp) -> Result<Exp, String>;
    fn elaborate_boxed_computation_type(
        &mut self,
        expression: &SExp,
    ) -> Result<ComputationType, String>;
    fn elaborate_boxed_computation(&mut self, expression: &SExp)
    -> Result<ComputationTerm, String>;
    fn intern(&mut self, name: &str) -> SymbolId;
    fn symbol(&self, symbol: SymbolId) -> &str;
    fn fresh_meta(
        &mut self,
        kind: SurfaceMeta,
        span: SourceSpan,
        local_context: &ExpContext,
    ) -> Exp;
    fn expand_math_macro(
        &mut self,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String>;
    fn expand_named_macro(
        &mut self,
        name: &Identifier,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String>;
}

// Expand the entire selected syntax before entering the much larger elaborator
// stack frames. Non-tail macro recursion must reach the expansion limit rather
// than overflowing the stack while elaborating intermediate templates.
fn expand_macros(exp: &SExp, handler: &mut impl Handler) -> Result<SExp, String> {
    let mut expanded = exp.clone();
    let mut result = Ok(());
    crate::macros::walk_sexp_control(&mut expanded, &mut |node| {
        if result.is_err() {
            return false;
        }
        loop {
            let next = match node {
                SExp::MathMacro {
                    tokens,
                    scope,
                    depth,
                    max_order,
                } => handler.expand_math_macro(tokens, *scope, *depth, *max_order),
                SExp::NamedMacro {
                    name,
                    tokens,
                    scope,
                    depth,
                    max_order,
                } => handler.expand_named_macro(name, tokens, *scope, *depth, *max_order),
                _ => return true,
            };
            match next {
                Ok(next) => *node = next,
                Err(error) => {
                    result = Err(error);
                    return false;
                }
            }
        }
    });
    result.map(|()| expanded)
}

#[derive(Debug, Clone)]
struct LocalBinding {
    var: SymbolId,
    // The typing context before this binding was introduced. Definitions do
    // not extend it; their free variables are shifted when the name is used.
    depth: usize,
    value: Option<Exp>,
}

// local scope during elaboration
#[derive(Debug, Clone)]
pub(crate) struct LocalScope {
    // Variables and local definitions share lexical shadowing order.
    bindings: Vec<LocalBinding>,
    // Types of local variables known to the elaborator. Module variables are
    // supplied by the handler and therefore do not appear here.
    typing_binds: ExpContext,
}

impl Default for LocalScope {
    fn default() -> Self {
        Self::new()
    }
}

impl LocalScope {
    pub(crate) fn new() -> Self {
        LocalScope {
            bindings: vec![],
            typing_binds: vec![],
        }
    }

    pub(crate) fn from_typing_context(context: ExpContext) -> Self {
        Self {
            bindings: context
                .iter()
                .enumerate()
                .map(|(depth, entry)| LocalBinding {
                    var: entry.var,
                    depth,
                    value: None,
                })
                .collect(),
            typing_binds: context,
        }
    }

    pub(crate) fn push_decl_var_exp(&mut self, var: SymbolId, exp: Exp) {
        self.bindings.push(LocalBinding {
            var,
            depth: self.typing_binds.len(),
            value: Some(exp),
        });
    }

    pub(crate) fn push_typed_decl_var(&mut self, var: SymbolId, ty: Exp) {
        self.push_binded_var(var, ty);
    }

    pub(crate) fn push_typed_decl_var_exp(&mut self, var: SymbolId, ty: Exp, exp: Exp) {
        self.push_decl_var_exp(var, exp);
        self.typing_binds.push(ExpContextEntry { var, ty });
    }

    // Keeps the telescope in the local scope.
    pub(crate) fn elab_telescope_bind_in_decl(
        &mut self,
        binds: &[RightBind],
        handler: &mut impl Handler,
    ) -> Result<Vec<(SymbolId, Exp)>, String> {
        let mut result = vec![];
        for RightBind { vars, ty } in binds.iter() {
            let ty_elab = self.elab_exp(ty, handler)?;
            handler.infer(&mut self.typing_binds, ty_elab)?;
            for (depth, var) in vars.iter().enumerate() {
                let var = handler.intern(var.as_str());
                // The shared annotation was elaborated before this binder group.
                let ty = shift_bound_indices(handler.arena(), ty_elab, depth, 0);
                result.push((var, ty));
                self.push_typed_decl_var(var, ty);
            }
        }
        Ok(result)
    }

    pub(crate) fn infer_elaborated(
        &mut self,
        exp: Exp,
        handler: &mut impl Handler,
    ) -> Result<Exp, String> {
        handler.infer(&mut self.typing_binds, exp)
    }

    fn get_var(&self, arena: &Arena, name: &Identifier, handler: &impl Handler) -> Option<Exp> {
        let binding = self
            .bindings
            .iter()
            .rev()
            .find(|binding| handler.symbol(binding.var) == name.as_str())?;
        let depth = self.typing_binds.len() - binding.depth;
        Some(match binding.value {
            Some(value) => shift_bound_indices(arena, value, depth, 0),
            None => arena.exp_bound(depth - 1),
        })
    }

    fn push_binded_var(&mut self, var: SymbolId, ty: Exp) {
        self.bindings.push(LocalBinding {
            var,
            depth: self.typing_binds.len(),
            value: None,
        });
        self.typing_binds.push(ExpContextEntry { var, ty });
    }

    fn push_named_binder(&mut self, var: SymbolId, ty: Exp, _handler: &impl Handler) {
        self.push_binded_var(var, ty);
    }

    fn associated_parameters(
        &mut self,
        parameters: &[SExp],
        expected: usize,
        handler: &mut impl Handler,
    ) -> Result<Vec<Exp>, String> {
        if parameters.is_empty() && expected > 0 {
            return Ok((0..expected)
                .map(|_| {
                    handler.fresh_meta(
                        SurfaceMeta::Implicit,
                        SourceSpan { start: 0, end: 0 },
                        &self.typing_binds,
                    )
                })
                .collect());
        }
        if parameters.len() != expected {
            return Err(format!(
                "associated item expects {expected} type parameter(s), found {}",
                parameters.len()
            ));
        }
        parameters
            .iter()
            .map(|parameter| self.elab_exp_rec(parameter, handler))
            .collect()
    }

    fn elab_inductive_cases(
        &mut self,
        constructors: &[Identifier],
        cases: &[(Identifier, SExp)],
        handler: &mut impl Handler,
    ) -> Result<Vec<Exp>, String> {
        if cases.len() != constructors.len() {
            return Err(format!(
                "Expected {} inductive branches, found {}",
                constructors.len(),
                cases.len()
            ));
        }
        let mut ordered = vec![None; constructors.len()];
        for (name, case) in cases {
            let Some(index) = constructors
                .iter()
                .position(|constructor| constructor.as_str() == name.as_str())
            else {
                return Err(format!("Unknown inductive constructor {}", name.as_str()));
            };
            if ordered[index].replace(case).is_some() {
                return Err(format!(
                    "Duplicate inductive branch for constructor {}",
                    name.as_str()
                ));
            }
        }
        ordered
            .into_iter()
            .zip(constructors)
            .map(|(case, constructor)| {
                let case = case.ok_or_else(|| {
                    format!(
                        "Missing inductive branch for constructor {}",
                        constructor.as_str()
                    )
                })?;
                self.elab_exp_rec(case, handler)
            })
            .collect()
    }

    fn pop_binded_var(&mut self) {
        self.bindings.pop();
        self.typing_binds.pop();
    }

    pub(crate) fn elab_exp(
        &mut self,
        exp: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, String> {
        let bindings = self.bindings.len();
        let depth = self.typing_binds.len();
        let e = self.elab_exp_rec(exp, handler);
        if e.is_err() {
            self.bindings.truncate(bindings);
            self.typing_binds.truncate(depth);
        } else {
            assert_eq!(self.bindings.len(), bindings);
            assert_eq!(self.typing_binds.len(), depth);
        }
        e
    }

    fn elab_take_parts(
        &mut self,
        bind: &Bind,
        body: &SExp,
        handler: &mut impl Handler,
    ) -> Result<(Exp, Exp, Exp), String> {
        match bind {
            Bind::Named(right_bind) => {
                if right_bind.vars.len() != 1 {
                    return Err("\\take currently expects exactly one named variable".into());
                }

                let var = handler.intern(right_bind.vars[0].as_str());
                let domain = self.elab_exp_rec(&right_bind.ty, handler)?;
                self.push_binded_var(var, domain);
                let map_body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                let map = handler.arena().alloc(ExpNode::Lam {
                    var,
                    ty: domain,
                    body: map_body,
                });
                let map_ty = handler.infer(&mut self.typing_binds, map)?;
                let ExpNode::Prod { body: codomain, .. } = handler.arena().get(map_ty) else {
                    return Err("failed to infer a product type for \\take map".into());
                };
                if exp_contains_bound(handler.arena(), codomain, 0) {
                    return Err("\\take map must have a non-dependent codomain".into());
                }
                let codomain = instantiate(handler.arena(), codomain, domain);
                Ok((domain, map, codomain))
            }
            Bind::Subset { var, ty, predicate } => {
                let carrier = self.elab_exp_rec(ty, handler)?;
                let var = handler.intern(var.as_str());
                self.push_binded_var(var, carrier);
                let predicate = self.elab_exp_rec(predicate, handler)?;
                self.pop_binded_var();

                let subset = handler.arena().alloc(ExpNode::SubSet {
                    var,
                    set: carrier,
                    predicate,
                });
                let domain = handler.arena().alloc(ExpNode::TypeLift {
                    superset: carrier,
                    subset,
                });
                self.push_binded_var(var, domain);
                let map_body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                let map = handler.arena().alloc(ExpNode::Lam {
                    var,
                    ty: domain,
                    body: map_body,
                });
                let map_ty = handler.infer(&mut self.typing_binds, map)?;
                let ExpNode::Prod { body: codomain, .. } = handler.arena().get(map_ty) else {
                    return Err("failed to infer a product type for \\take map".into());
                };
                if exp_contains_bound(handler.arena(), codomain, 0) {
                    return Err("\\take map must have a non-dependent codomain".into());
                }
                let codomain = instantiate(handler.arena(), codomain, domain);
                Ok((domain, map, codomain))
            }
            Bind::SubsetWithProof { .. } => {
                Err("\\take with proof bind is not supported by kernel Take(X,T,f)".into())
            }
        }
    }

    fn elab_exp_rec(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<Exp, String> {
        match exp {
            SExp::Meta { kind, span } => Ok(handler.fresh_meta(*kind, *span, &self.typing_binds)),
            SExp::AccessPath { access, parameters } => {
                // this includes (term binding) access path

                // 1. find from binded vars first (if no parameters)
                if let LocalAccess::Current { access: name } = access
                    && let Some(var) = self.get_var(handler.arena(), name, handler)
                    && parameters.is_empty()
                {
                    return Ok(var);
                }

                // 2. others via handler
                let item = handler.get_item_from_access_path(access)?;
                match item {
                    ItemAccessResult::Definition(ModItemDefinition { definition, .. }) => {
                        if !parameters.is_empty() {
                            return Err(format!(
                                "Defined constant {:?} cannot be applied with parameters",
                                access
                            ));
                        }
                        if !matches!(
                            handler.env().definition(definition),
                            DefinedConstant::Pts { .. }
                        ) {
                            return Err(
                                "Program definitions require explicit Set reflection (^)".into()
                            );
                        }
                        Ok(handler.arena().alloc(ExpNode::DefinedConstant(definition)))
                    }
                    ItemAccessResult::ReflectedDefinition(ModItemDefinition {
                        definition, ..
                    }) => {
                        if !parameters.is_empty() {
                            return Err(
                                "Reflected definition cannot be applied with parameters".into()
                            );
                        }
                        match handler.env().definition(definition) {
                            DefinedConstant::ProgramValue { body, .. } => {
                                crate::raw::reflection::reflect_value(handler.env(), *body)
                                    .map_err(|e| e.to_string())
                            }
                            DefinedConstant::ProgramComputation { body, .. } => {
                                crate::raw::reflection::reflect_computation(handler.env(), *body)
                                    .map_err(|e| e.to_string())
                            }
                            _ => Err("Set reflection requires a Program definition".into()),
                        }
                    }
                    ItemAccessResult::Inductive(ModItemInductive { inductive, .. })
                    | ItemAccessResult::Record(ModItemRecord { inductive, .. }) => {
                        let parameters: Vec<Exp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(handler.arena().alloc(ExpNode::IndType {
                            indspec: inductive,
                            parameters,
                        }))
                    }
                    ItemAccessResult::Expression(exp) => {
                        if parameters.is_empty() {
                            Ok(exp)
                        } else {
                            Err("Module parameter cannot be applied with parameters".to_string())
                        }
                    }
                    ItemAccessResult::ProgramInductive(_)
                    | ItemAccessResult::ProgramTypeParameter(_)
                    | ItemAccessResult::ProgramValueParameter(_) => {
                        Err("Program names require explicit Set reflection (^)".into())
                    }
                }
            }
            // this includes accessing constructor of the inductive type, accessing field of record type
            // `List[Nat]#nil` or `some_group#unit`
            SExp::AssociatedAccess { base, field } => {
                // 1. if base is local access, try to get constructor (parameter is allowed)
                if let SExp::AccessPath { access, parameters } = base.as_ref() {
                    let item = handler.get_item_from_access_path(access)?;
                    match item {
                        ItemAccessResult::Inductive(ModItemInductive {
                            inductive,
                            type_name,
                            ctor_names,
                            associated_definitions,
                            ..
                        }) => {
                            for (idx, ctor_name) in ctor_names.iter().enumerate() {
                                if ctor_name.as_str() == field.as_str() {
                                    let count =
                                        handler.env().inductive(inductive).parameters().len();
                                    let parameters =
                                        self.associated_parameters(parameters, count, handler)?;
                                    return Ok(handler.arena().alloc(ExpNode::IndCtor {
                                        indspec: inductive,
                                        idx,
                                        parameters,
                                    }));
                                }
                            }
                            if let Some((_, definition)) = associated_definitions
                                .iter()
                                .find(|(name, _)| name.as_str() == field.as_str())
                            {
                                let count = handler.env().inductive(inductive).parameters().len();
                                let parameters =
                                    self.associated_parameters(parameters, count, handler)?;
                                let definition =
                                    handler.arena().alloc(ExpNode::DefinedConstant(*definition));
                                return Ok(crate::raw::utils::assoc_apply(
                                    handler.arena(),
                                    definition,
                                    parameters,
                                ));
                            }
                            Err(format!(
                                "Associated item {} not found in inductive type {}",
                                field.as_str(),
                                type_name.as_str()
                            ))
                        }
                        ItemAccessResult::Record(record) => {
                            if field.as_str() == "#" {
                                let count =
                                    handler.env().inductive(record.inductive).parameters().len();
                                let parameters =
                                    self.associated_parameters(parameters, count, handler)?;
                                return Ok(handler.arena().alloc(ExpNode::IndCtor {
                                    indspec: record.inductive,
                                    idx: 0,
                                    parameters,
                                }));
                            }
                            if let Some((_, definition)) = record
                                .associated_definitions
                                .iter()
                                .find(|(name, _)| name.as_str() == field.as_str())
                            {
                                let count =
                                    handler.env().inductive(record.inductive).parameters().len();
                                let parameters =
                                    self.associated_parameters(parameters, count, handler)?;
                                let definition =
                                    handler.arena().alloc(ExpNode::DefinedConstant(*definition));
                                return Ok(crate::raw::utils::assoc_apply(
                                    handler.arena(),
                                    definition,
                                    parameters,
                                ));
                            }
                            let count =
                                handler.env().inductive(record.inductive).parameters().len();
                            let parameters =
                                self.associated_parameters(parameters, count, handler)?;
                            let record_ty = handler.arena().alloc(ExpNode::IndType {
                                indspec: record.inductive,
                                parameters: parameters.clone(),
                            });
                            let shifted_parameters = parameters
                                .iter()
                                .map(|parameter| {
                                    crate::raw::calculus::shift_bound_indices(
                                        handler.arena(),
                                        *parameter,
                                        1,
                                        0,
                                    )
                                })
                                .collect::<Vec<_>>();
                            let value = handler.arena().exp_bound(0);
                            let Some(body) = record.field_projection(
                                handler.env(),
                                value,
                                field,
                                &shifted_parameters,
                            ) else {
                                return Err(format!(
                                    "Associated item {} not found in structure {}",
                                    field.as_str(),
                                    record.type_name.as_str()
                                ));
                            };
                            let var = handler.intern("structure");
                            Ok(handler.arena().alloc(ExpNode::Lam {
                                var,
                                ty: record_ty,
                                body,
                            }))
                        }
                        _ => Err(format!(
                            "Expected inductive constructor or record type in base of associated access {:?}",
                            base
                        )),
                    }
                } else {
                    // 2. otherwise, elab base first, then project field
                    let base_elab = self.elab_exp_rec(base, handler)?;
                    handler.field_projection(&mut self.typing_binds, base_elab, field)
                }
            }
            SExp::InferredProjection { value, field } => {
                let value = self.elab_exp_rec(value, handler)?;
                handler.field_projection(&mut self.typing_binds, value, field)
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
                let expanded = expand_macros(exp, handler)?;
                self.elab_exp_rec(&expanded, handler)
            }
            SExp::TokenMatch { .. } => Err("Token match escaped template expansion".into()),
            SExp::MacroParameter(name) => Err(format!(
                "Macro capture '${}' escaped template expansion",
                name.as_str()
            )),
            SExp::ResolvedExp(exp) => Ok(*exp),
            SExp::Where { exp, clauses } => {
                let declaration_mark = self.bindings.len();
                let depth = self.typing_binds.len();
                let result = (|| {
                    for (name, ty, body) in clauses {
                        let ty = self.elab_exp_rec(ty, handler)?;
                        let body = self.elab_exp_rec(body, handler)?;
                        // A typed identity application keeps the declared type
                        // (including subset weakening) while reducing to the value.
                        let identity = handler.arena().alloc(ExpNode::Lam {
                            var: SymbolId::ANONYMOUS,
                            ty,
                            body: handler.arena().exp_bound(0),
                        });
                        let value = handler.arena().alloc(ExpNode::App {
                            func: identity,
                            arg: body,
                        });
                        // Check even unused definitions, before publishing their
                        // names. This also records constraints for implicit types.
                        handler
                            .infer(&mut self.typing_binds, value)
                            .map_err(|error| {
                                format!("Local definition '{}': {error}", name.as_str())
                            })?;
                        let name = handler.intern(name.as_str());
                        self.push_decl_var_exp(name, value);
                    }
                    self.elab_exp_rec(exp, handler)
                })();
                self.bindings.truncate(declaration_mark);
                self.typing_binds.truncate(depth);
                result
            }
            SExp::Sort(sort) => Ok(handler.arena().sort(*sort)),
            SExp::ValueType => Err("\\VType is only valid in a Program binder".into()),
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(exp, SExp::Prod { .. });
                match bind {
                    Bind::Named(right_bind) => {
                        if right_bind.vars.is_empty() {
                            // same as Anonymous
                            let ty_elab = self.elab_exp_rec(&right_bind.ty, handler)?;
                            let var = SymbolId::ANONYMOUS;
                            self.push_named_binder(var, ty_elab, handler);
                            let body_elab = self.elab_exp_rec(body, handler)?;
                            self.pop_binded_var();
                            return Ok(if is_prod {
                                handler.arena().alloc(ExpNode::Prod {
                                    var,
                                    ty: ty_elab,
                                    body: body_elab,
                                })
                            } else {
                                handler.arena().alloc(ExpNode::Lam {
                                    var,
                                    ty: ty_elab,
                                    body: body_elab,
                                })
                            });
                        }

                        let ty_elab = self.elab_exp_rec(&right_bind.ty, handler)?;

                        let mut telescope: Vec<(SymbolId, Exp)> = vec![];
                        for (depth, var) in right_bind.vars.iter().enumerate() {
                            let var = handler.intern(var.as_str());
                            // Each preceding variable adds a binder around the annotation.
                            let ty = shift_bound_indices(handler.arena(), ty_elab, depth, 0);
                            telescope.push((var, ty));
                            self.push_named_binder(var, ty, handler);
                        }

                        let body_elab = self.elab_exp_rec(body, handler)?;

                        for _ in &right_bind.vars {
                            self.pop_binded_var();
                        }

                        Ok(if is_prod {
                            crate::raw::utils::assoc_prod(handler.arena(), telescope, body_elab)
                        } else {
                            crate::raw::utils::assoc_lam(handler.arena(), telescope, body_elab)
                        })
                    }
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var = handler.intern(var.as_str());
                        self.push_binded_var(var, ty_elab);
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        let subset = handler.arena().alloc(ExpNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        });

                        let refined_ty = handler.arena().alloc(ExpNode::TypeLift {
                            superset: ty_elab,
                            subset,
                        });
                        self.push_binded_var(var, refined_ty);
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();

                        Ok(if is_prod {
                            handler.arena().alloc(ExpNode::Prod {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        } else {
                            handler.arena().alloc(ExpNode::Lam {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        })
                    }
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var,
                    } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var = handler.intern(var.as_str());
                        self.push_binded_var(var, ty_elab);
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        let subset = handler.arena().alloc(ExpNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        });
                        let refined_ty = handler.arena().alloc(ExpNode::TypeLift {
                            superset: ty_elab,
                            subset,
                        });
                        self.push_binded_var(var, refined_ty);
                        let proof = handler.intern(proof_var.as_str());
                        self.push_binded_var(proof, predicate_elab);
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();
                        self.pop_binded_var();
                        let body_elab = handler.arena().alloc(ExpNode::Prod {
                            var: proof,
                            ty: predicate_elab,
                            body: body_elab,
                        });

                        Ok(if is_prod {
                            handler.arena().alloc(ExpNode::Prod {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        } else {
                            handler.arena().alloc(ExpNode::Lam {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        })
                    }
                }
            }
            SExp::App { func, arg } => {
                let mut arguments = vec![arg.as_ref()];
                let mut head = func.as_ref();
                while let SExp::App { func, arg } = head {
                    arguments.push(arg.as_ref());
                    head = func.as_ref();
                }
                arguments.reverse();
                if arguments.len() == 1
                    && let SExp::AssociatedAccess { base, field } = head
                    && let SExp::AccessPath { access, parameters } = base.as_ref()
                    && parameters.is_empty()
                {
                    let item = handler.get_item_from_access_path(access)?;
                    match item {
                        ItemAccessResult::Record(record)
                            if !record
                                .associated_definitions
                                .iter()
                                .any(|(name, _)| name == field) =>
                        {
                            let value = self.elab_exp_rec(arguments[0], handler)?;
                            let value_ty = handler.infer(&mut self.typing_binds, value)?;
                            if let ExpNode::IndType {
                                indspec,
                                parameters,
                            } = handler.arena().get(value_ty)
                                && indspec == record.inductive
                            {
                                return record
                                    .field_projection(handler.env(), value, field, &parameters)
                                    .ok_or_else(|| {
                                        format!(
                                            "Associated item {} not found in structure {}",
                                            field.as_str(),
                                            record.type_name.as_str()
                                        )
                                    });
                            }
                        }
                        _ => {}
                    }
                }
                let func_elab = self.elab_exp_rec(func, handler)?;
                let arg_elab = self.elab_exp_rec(arg, handler)?;
                Ok(handler.arena().alloc(ExpNode::App {
                    func: func_elab,
                    arg: arg_elab,
                }))
            }
            SExp::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                let element_elab = self.elab_exp_rec(element, handler)?;
                let proof_elab = self.elab_exp_rec(proof, handler)?;
                Ok(handler.arena().alloc(ExpNode::SubsetIntro {
                    superset: superset_elab,
                    subset: subset_elab,
                    element: element_elab,
                    proof: proof_elab,
                }))
            }
            SExp::IndCase {
                path,
                scrutinee,
                return_type,
                branches,
            } => {
                let (ctor_names, inductive) = match handler.get_item_from_access_path(path)? {
                    ItemAccessResult::Inductive(ModItemInductive {
                        ctor_names,
                        inductive,
                        ..
                    }) => (ctor_names, inductive),
                    _ => {
                        return Err(format!(
                            "Expected inductive type in case access path {:?}",
                            path
                        ));
                    }
                };

                let scrutinee = self.elab_exp_rec(scrutinee, handler)?;
                let return_type_elab = self.elab_exp_rec(return_type, handler)?;
                let branches = self.elab_inductive_cases(&ctor_names, branches, handler)?;

                Ok(handler.arena().alloc(ExpNode::IndCase {
                    indspec: inductive,
                    scrutinee,
                    return_type: return_type_elab,
                    branches,
                }))
            }
            SExp::Induction {
                binder,
                return_type,
                cases,
            } => {
                let SExp::AccessPath {
                    access: path,
                    parameters,
                } = binder.ty.as_ref()
                else {
                    return Err("Induction binder type must name an inductive type".into());
                };
                let (ctor_names, inductive) = match handler.get_item_from_access_path(path)? {
                    ItemAccessResult::Inductive(ModItemInductive {
                        ctor_names,
                        inductive,
                        ..
                    }) => (ctor_names, inductive),
                    _ => return Err("Induction binder type must name an inductive type".into()),
                };
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.elab_exp_rec(parameter, handler))
                    .collect::<Result<Vec<_>, _>>()?;
                let domain = handler.arena().alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameters.clone(),
                });
                let var = handler.intern(binder.vars[0].as_str());
                self.push_binded_var(var, domain);
                let motive_body = self.elab_exp_rec(return_type, handler);
                self.pop_binded_var();
                let motive = handler.arena().alloc(ExpNode::Lam {
                    var,
                    ty: domain,
                    body: motive_body?,
                });
                let motive_kind = handler.infer(&mut self.typing_binds, motive)?;
                let mut induction = InductiveTypeSpecs::primitive_recursion(
                    handler.arena(),
                    inductive,
                    handler.env().inductive(inductive),
                    &parameters,
                    motive_kind,
                );
                induction = handler.arena().alloc(ExpNode::App {
                    func: induction,
                    arg: motive,
                });
                for case in self.elab_inductive_cases(&ctor_names, cases, handler)? {
                    induction = handler.arena().alloc(ExpNode::App {
                        func: induction,
                        arg: case,
                    });
                }
                Ok(induction)
            }
            SExp::IndElimPrim {
                path,
                parameters,
                motive,
            } => {
                let inductive = match handler.get_item_from_access_path(path)? {
                    ItemAccessResult::Inductive(ModItemInductive { inductive, .. }) => inductive,
                    _ => {
                        return Err(format!(
                            "Expected inductive type in ind elim prim access path {:?}",
                            path
                        ));
                    }
                };

                let parameters: Vec<Exp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                let motive = self.elab_exp_rec(motive, handler)?;
                let motive_kind = handler.infer(&mut self.typing_binds, motive)?;
                let recursion = InductiveTypeSpecs::primitive_recursion(
                    handler.arena(),
                    inductive,
                    handler.env().inductive(inductive),
                    &parameters,
                    motive_kind,
                );
                Ok(handler.arena().alloc(ExpNode::App {
                    func: recursion,
                    arg: motive,
                }))
            }
            SExp::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                Ok(handler.arena().alloc(ExpNode::RunStep {
                    state_ty,
                    result_ty,
                }))
            }
            SExp::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let next = self.elab_exp_rec(next, handler)?;
                Ok(handler.arena().alloc(ExpNode::Continue {
                    state_ty,
                    result_ty,
                    next,
                }))
            }
            SExp::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let output = self.elab_exp_rec(output, handler)?;
                Ok(handler.arena().alloc(ExpNode::Finish {
                    state_ty,
                    result_ty,
                    output,
                }))
            }
            SExp::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let state = self.elab_exp_rec(state, handler)?;
                Ok(handler.arena().alloc(ExpNode::Acc {
                    state_ty,
                    result_ty,
                    step,
                    state,
                }))
            }
            SExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let initial = self.elab_exp_rec(initial, handler)?;
                let accessibility = self.elab_exp_rec(accessibility, handler)?;
                Ok(handler.arena().alloc(ExpNode::SetRun {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    accessibility,
                }))
            }
            SExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let initial = self.elab_exp_rec(initial, handler)?;
                let transition = self.elab_exp_rec(transition, handler)?;
                let accessibility = self.elab_exp_rec(accessibility, handler)?;
                let transition_equality = self.elab_exp_rec(transition_equality, handler)?;
                Ok(handler.arena().alloc(ExpNode::SetRunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                    accessibility,
                    transition_equality,
                }))
            }
            SExp::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let motive = self.elab_exp_rec(motive, handler)?;
                let on_continue = self.elab_exp_rec(on_continue, handler)?;
                let on_finish = self.elab_exp_rec(on_finish, handler)?;
                let scrutinee = self.elab_exp_rec(scrutinee, handler)?;
                Ok(handler.arena().alloc(ExpNode::RunStepRec {
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
                    scrutinee,
                }))
            }
            SExp::BoxType { program_ty } => {
                let program_ty = handler.elaborate_boxed_computation_type(program_ty)?;
                Ok(handler.arena().alloc(ExpNode::BoxType { program_ty }))
            }
            SExp::BoxProgram {
                program_ty,
                program,
            } => {
                let program_ty = handler.elaborate_boxed_computation_type(program_ty)?;
                let program = handler.elaborate_boxed_computation(program)?;
                Ok(handler.arena().alloc(ExpNode::BoxProgram {
                    program_ty,
                    program,
                }))
            }
            SExp::ForceBox { program_ty, boxed } => {
                let program_ty = handler.elaborate_boxed_computation_type(program_ty)?;
                let boxed = self.elab_exp_rec(boxed, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::ForceBox { program_ty, boxed }))
            }
            SExp::BoxApp { function, argument } => {
                let function = self.elab_exp_rec(function, handler)?;
                let argument = self.elab_exp_rec(argument, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::BoxApp { function, argument }))
            }
            SExp::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let state = self.elab_exp_rec(state, handler)?;
                let predecessors = self.elab_exp_rec(predecessors, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::AccIntro {
                    state_ty,
                    result_ty,
                    step,
                    state,
                    predecessors,
                })))
            }
            SExp::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let from = self.elab_exp_rec(from, handler)?;
                let to = self.elab_exp_rec(to, handler)?;
                let accessibility = self.elab_exp_rec(accessibility, handler)?;
                let transition = self.elab_exp_rec(transition, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from,
                    to,
                    accessibility,
                    transition,
                })))
            }

            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                let parameters: Vec<Exp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                let item = handler.get_item_from_access_path(access)?;
                let (declared_names, pts_inductive) = match item {
                    ItemAccessResult::Record(record) => {
                        let constructor =
                            &handler.env().inductive(record.inductive).constructors()[0];
                        let names = constructor
                            .telescope
                            .iter()
                            .map(|binder| match binder {
                                crate::raw::inductive::CtorBinder::Simple((name, _)) => {
                                    handler.symbol(*name).to_string()
                                }
                                _ => {
                                    unreachable!("structure fields are simple constructor binders")
                                }
                            })
                            .collect::<Vec<_>>();
                        (names, record.inductive)
                    }
                    _ => {
                        return Err(format!(
                            "Expected structure type in structure literal access path {:?}",
                            access
                        ));
                    }
                };
                let mut supplied = std::collections::HashMap::new();
                for (field_name, value) in fields {
                    if supplied.insert(field_name.as_str(), value).is_some() {
                        return Err(format!(
                            "Structure field {} was supplied more than once",
                            field_name.as_str()
                        ));
                    }
                }
                for supplied_name in supplied.keys() {
                    if !declared_names.iter().any(|name| name == supplied_name) {
                        return Err(format!("Unknown structure field {supplied_name}"));
                    }
                }
                let mut ordered = Vec::with_capacity(declared_names.len());
                for declared_name in declared_names {
                    let value = supplied
                        .get(declared_name.as_str())
                        .ok_or_else(|| format!("Missing structure field {declared_name}"))?;
                    ordered.push(self.elab_exp_rec(value, handler)?);
                }

                let constructor = handler.arena().alloc(ExpNode::IndCtor {
                    indspec: pts_inductive,
                    parameters,
                    idx: 0,
                });
                Ok(crate::raw::utils::assoc_apply(
                    handler.arena(),
                    constructor,
                    ordered,
                ))
            }

            SExp::PowerSet { set } => {
                let set_elab = self.elab_exp_rec(set, handler)?;
                Ok(handler.arena().alloc(ExpNode::PowerSet { set: set_elab }))
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                let set_elab = self.elab_exp_rec(set, handler)?;
                let var = handler.intern(var.as_str());
                self.push_binded_var(var, set_elab);
                let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                self.pop_binded_var();
                Ok(handler.arena().alloc(ExpNode::SubSet {
                    var,
                    set: set_elab,
                    predicate: predicate_elab,
                }))
            }
            SExp::Pred {
                superset,
                subset,
                element,
            } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                let element_elab = self.elab_exp_rec(element, handler)?;
                Ok(handler.arena().alloc(ExpNode::Pred {
                    superset: superset_elab,
                    subset: subset_elab,
                    element: element_elab,
                }))
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                Ok(handler.arena().alloc(ExpNode::TypeLift {
                    superset: superset_elab,
                    subset: subset_elab,
                }))
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(left, handler)?;
                let right_elab = self.elab_exp_rec(right, handler)?;
                Ok(handler.arena().alloc(ExpNode::Equal {
                    left: left_elab,
                    right: right_elab,
                }))
            }
            SExp::Exists { bind } => match bind {
                Bind::Named(rightbind) => {
                    if rightbind.vars.len() >= 2 {
                        return Err(
                            "Elaboration of multiple named binds in Exists is not implemented"
                                .to_string(),
                        );
                    }
                    let ty_elab = self.elab_exp_rec(&rightbind.ty, handler)?;
                    Ok(handler.arena().alloc(ExpNode::Exists { set: ty_elab }))
                }
                Bind::SubsetWithProof { .. } => Err(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string(),
                ),
                Bind::Subset { var, ty, predicate } => {
                    let subset_as_exp = {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var = handler.intern(var.as_str());
                        self.push_binded_var(var, ty_elab);
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        handler.arena().alloc(ExpNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        })
                    };
                    Ok(handler
                        .arena()
                        .alloc(ExpNode::Exists { set: subset_as_exp }))
                }
            },
            SExp::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
            } => {
                let (domain, map, codomain) = self.elab_take_parts(bind, body, handler)?;
                let existence = self.elab_exp_rec(existence, handler)?;
                let uniqueness = self.elab_exp_rec(uniqueness, handler)?;
                Ok(handler.arena().alloc(ExpNode::TakeSet {
                    domain,
                    codomain,
                    map,
                    existence,
                    uniqueness,
                }))
            }
            SExp::TakeProp {
                bind,
                body,
                existence,
            } => {
                let (domain, map, proposition) = self.elab_take_parts(bind, body, handler)?;
                let existence = self.elab_exp_rec(existence, handler)?;
                Ok(handler.arena().alloc(ExpNode::TakeProp {
                    domain,
                    proposition,
                    map,
                    existence,
                }))
            }
            SExp::ExistsIntro { element, set } => {
                let element = self.elab_exp_rec(element, handler)?;
                let set = self.elab_exp_rec(set, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::Prove(Prove::ExistsIntro { element, set })))
            }
            SExp::SubsetElim {
                element,
                subset,
                superset,
            } => {
                let element = self.elab_exp_rec(element, handler)?;
                let subset = self.elab_exp_rec(subset, handler)?;
                let superset = self.elab_exp_rec(superset, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::SubsetElim {
                    element,
                    subset,
                    superset,
                })))
            }
            SExp::IdRefl { element } => {
                let element = self.elab_exp_rec(element, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::Prove(Prove::IdRefl { element })))
            }
            SExp::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
                base,
                equality,
            } => {
                let left = self.elab_exp_rec(left, handler)?;
                let right = self.elab_exp_rec(right, handler)?;
                let ty = self.elab_exp_rec(ty, handler)?;
                let var = handler.intern(var.as_str());
                self.push_binded_var(var, ty);
                let predicate = self.elab_exp_rec(predicate, handler)?;
                self.pop_binded_var();
                let base = self.elab_exp_rec(base, handler)?;
                let equality = self.elab_exp_rec(equality, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::IdElim {
                    left,
                    right,
                    var,
                    ty,
                    predicate,
                    base,
                    equality,
                })))
            }
            SExp::AxiomSetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => {
                let left = self.elab_exp_rec(left, handler)?;
                let right = self.elab_exp_rec(right, handler)?;
                let left_to_right = self.elab_exp_rec(left_to_right, handler)?;
                let right_to_left = self.elab_exp_rec(right_to_left, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::Prove(Prove::Axiom(Axiom::SetExt {
                        left,
                        right,
                        left_to_right,
                        right_to_left,
                    }))))
            }
            SExp::AxiomFunExt {
                left,
                right,
                pointwise,
            } => {
                let left = self.elab_exp_rec(left, handler)?;
                let right = self.elab_exp_rec(right, handler)?;
                let pointwise = self.elab_exp_rec(pointwise, handler)?;
                Ok(handler
                    .arena()
                    .alloc(ExpNode::Prove(Prove::Axiom(Axiom::FunExt {
                        left,
                        right,
                        pointwise,
                    }))))
            }
            SExp::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => {
                let domain = self.elab_exp_rec(domain, handler)?;
                let family = self.elab_exp_rec(family, handler)?;
                let inhabited = self.elab_exp_rec(inhabited, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::Axiom(
                    Axiom::ClassicalIndefiniteChoice {
                        domain,
                        family,
                        inhabited,
                    },
                ))))
            }
            SExp::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => {
                let func = self.elab_exp_rec(func, handler)?;
                let domain = self.elab_exp_rec(domain, handler)?;
                let codomain = self.elab_exp_rec(codomain, handler)?;
                let element = self.elab_exp_rec(element, handler)?;
                let existence = self.elab_exp_rec(existence, handler)?;
                let uniqueness = self.elab_exp_rec(uniqueness, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::TakeEq {
                    func,
                    domain,
                    codomain,
                    element,
                    existence,
                    uniqueness,
                })))
            }
            SExp::ThunkType { .. }
            | SExp::ReturnType { .. }
            | SExp::ComputationFunction { .. }
            | SExp::Thunk { .. }
            | SExp::Return { .. }
            | SExp::Force { .. }
            | SExp::ComputationLam { .. }
            | SExp::Sequence { .. }
            | SExp::ValueLet { .. }
            | SExp::ProgramCase { .. } => {
                Err("Program syntax cannot be elaborated as a Set/Prop expression".into())
            }
            SExp::Block(block) => {
                let Block {
                    statements: declarations,
                    result: term,
                } = block;
                let mut term = term.as_ref().clone();
                for decl in declarations.iter().rev() {
                    match decl {
                        Statement::Fix(items) => {
                            for bind in items.iter().rev() {
                                term = SExp::Lam {
                                    bind: Bind::Named(bind.clone()),
                                    body: Box::new(term),
                                };
                            }
                        }
                        Statement::Let { var, ty, body } => {
                            term = SExp::Where {
                                exp: Box::new(term),
                                clauses: vec![(var.clone(), ty.clone(), body.clone())],
                            };
                        }
                        Statement::Bind { .. } => {
                            return Err(
                                "\\bind statements are only available in Program blocks".into()
                            );
                        }
                        Statement::Sufficient { map, map_ty } => {
                            let argument = Identifier("enoughArgument".into());
                            term = SExp::App {
                                func: Box::new(map.clone()),
                                arg: Box::new(SExp::Where {
                                    exp: Box::new(SExp::AccessPath {
                                        access: LocalAccess::Current {
                                            access: argument.clone(),
                                        },
                                        parameters: Vec::new(),
                                    }),
                                    clauses: vec![(argument, map_ty.clone(), term)],
                                }),
                            };
                        }
                    }
                }
                self.elab_exp_rec(&term, handler)
            }
            SExp::Program(_) => {
                Err("Program block syntax cannot be elaborated as a Set/Prop expression".into())
            }
        }
    }
}
