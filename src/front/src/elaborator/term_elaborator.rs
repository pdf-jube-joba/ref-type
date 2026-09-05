use crate::elaborator::ItemAccessResult;
use crate::syntax::*;
use kernel::calculus::{exp_contains_bound, instantiate};
use kernel::environment::CrateEnv;
use kernel::exp::*;
use kernel::ids::*;
use kernel::inductive::InductiveTypeSpecs;

pub trait Handler {
    fn env(&self) -> &CrateEnv;
    fn arena(&self) -> &Arena;
    fn current_module(&self) -> ModuleId;
    fn module_context(&self) -> Context;
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String>;
    fn field_projection(&mut self, e: RawExp, field_name: &Identifier) -> Result<RawExp, String>;
    fn infer(&mut self, local_ctx: &mut Context, e: RawExp) -> Result<RawExp, String>;
    fn intern(&mut self, name: &str) -> SymbolId;
    fn symbol(&self, symbol: SymbolId) -> &str;
    fn fresh_meta(
        &mut self,
        kind: SurfaceMeta,
        span: SourceSpan,
        local_context: &Context,
    ) -> RawExp;
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

// local scope during elaboration
#[derive(Debug, Clone)]
pub struct LocalScope {
    // for find binded variables inside term
    // lambda abstraction variables, product, subset,
    // after any call of elab_exp outside the elab_exp, this should be cleared
    binded_vars: Vec<SymbolId>,
    // for find decl levels
    decl_binds: Vec<(SymbolId, Option<RawExp>)>,
    // Types of local variables known to the elaborator. Module variables are
    // supplied by the handler and therefore do not appear here.
    typing_binds: Context,
}

impl Default for LocalScope {
    fn default() -> Self {
        Self::new()
    }
}

impl LocalScope {
    pub fn new() -> Self {
        LocalScope {
            binded_vars: vec![],
            decl_binds: vec![],
            typing_binds: vec![],
        }
    }

    pub fn typing_context(&self) -> &Context {
        &self.typing_binds
    }

    fn kernel_context(&self, handler: &impl Handler) -> Context {
        let mut context = handler.module_context();
        context.extend(self.typing_binds.iter().cloned());
        context
    }

    fn is_set_type(&self, handler: &impl Handler, ty: RawExp) -> bool {
        let mut context = self.kernel_context(handler);
        matches!(
            kernel::derivation::CheckSession::new(
                handler.env(),
                handler.current_module(),
                &mut context,
            )
            .infer_sort(ty),
            Ok(kernel::sort::Sort::Set(_))
        )
    }

    fn program_context(&self, handler: &impl Handler) -> Context {
        self.kernel_context(handler)
            .into_iter()
            .filter(|entry| {
                matches!(
                    entry,
                    ContextEntry::ProgramType { .. } | ContextEntry::ProgramValue { .. }
                )
            })
            .collect()
    }

    pub fn push_decl_var(&mut self, var: SymbolId) {
        self.decl_binds.push((var, None));
    }

    pub fn push_decl_var_exp(&mut self, var: SymbolId, exp: RawExp) {
        self.decl_binds.push((var, Some(exp)));
    }

    pub fn push_typed_decl_var(&mut self, var: SymbolId, ty: RawExp) {
        self.decl_binds.push((var, None));
        self.typing_binds.push(ContextEntry::Pts { var, ty });
    }

    pub fn push_program_type_decl_var(&mut self, var: SymbolId) {
        self.decl_binds.push((var, None));
        self.typing_binds.push(ContextEntry::ProgramType { var });
    }

    pub fn push_program_value_decl_var(&mut self, var: SymbolId, ty: RawExp) {
        self.decl_binds.push((var, None));
        self.typing_binds
            .push(ContextEntry::ProgramValue { var, ty });
    }

    pub fn push_typed_decl_var_exp(&mut self, var: SymbolId, ty: RawExp, exp: RawExp) {
        self.decl_binds.push((var, Some(exp)));
        self.typing_binds.push(ContextEntry::Pts { var, ty });
    }

    pub fn push_program_type_decl_var_exp(&mut self, var: SymbolId, exp: RawExp) {
        self.decl_binds.push((var, Some(exp)));
        self.typing_binds.push(ContextEntry::ProgramType { var });
    }

    pub fn push_program_value_decl_var_exp(&mut self, var: SymbolId, ty: RawExp, exp: RawExp) {
        self.decl_binds.push((var, Some(exp)));
        self.typing_binds
            .push(ContextEntry::ProgramValue { var, ty });
    }

    // does not pop decl_binds
    pub fn elab_telescope_bind_in_decl(
        &mut self,
        binds: &[RightBind],
        handler: &mut impl Handler,
    ) -> Result<Vec<(SymbolId, RawExp)>, String> {
        let mut result = vec![];
        for RightBind { vars, ty } in binds.iter() {
            let ty_elab = self.elab_exp(ty, handler)?;
            handler.infer(&mut self.typing_binds, ty_elab)?;
            for var in vars {
                let var = handler.intern(var.as_str());
                result.push((var, ty_elab));
                self.push_typed_decl_var(var, ty_elab);
            }
        }
        Ok(result)
    }

    pub fn infer_elaborated(
        &mut self,
        exp: RawExp,
        handler: &mut impl Handler,
    ) -> Result<RawExp, String> {
        handler.infer(&mut self.typing_binds, exp)
    }

    fn get_var(&self, arena: &Arena, name: &Identifier, handler: &impl Handler) -> Option<RawExp> {
        for (index, v) in self.binded_vars.iter().rev().enumerate() {
            if handler.symbol(*v) == name.as_str() {
                return Some(arena.bound(index));
            }
        }
        for (index, (v, exp)) in self.decl_binds.iter().rev().enumerate() {
            if handler.symbol(*v) == name.as_str() {
                return Some(exp.unwrap_or_else(|| arena.bound(self.binded_vars.len() + index)));
            }
        }
        None
    }

    fn push_binded_var(&mut self, var: SymbolId, ty: RawExp) {
        self.binded_vars.push(var);
        self.typing_binds.push(ContextEntry::Pts { var, ty });
    }
    pub(crate) fn push_program_value_var(&mut self, var: SymbolId, ty: RawExp) {
        self.binded_vars.push(var);
        self.typing_binds
            .push(ContextEntry::ProgramValue { var, ty });
    }
    fn push_program_type_var(&mut self, var: SymbolId) {
        self.binded_vars.push(var);
        self.typing_binds.push(ContextEntry::ProgramType { var });
    }

    fn push_named_binder(&mut self, var: SymbolId, ty: RawExp, handler: &impl Handler) {
        if matches!(handler.arena().get(ty), RawNode::ValueType) {
            self.push_program_type_var(var);
            return;
        }
        let mut context = self.kernel_context(handler);
        if kernel::derivation::CheckSession::new(
            handler.env(),
            handler.current_module(),
            &mut context,
        )
        .check_value_type(ty)
        .is_ok()
        {
            self.push_program_value_var(var, ty);
        } else {
            self.push_binded_var(var, ty);
        }
    }

    fn associated_parameters(
        &mut self,
        parameters: &[SExp],
        expected: usize,
        handler: &mut impl Handler,
    ) -> Result<Vec<RawExp>, String> {
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
    fn pop_binded_var(&mut self) {
        self.binded_vars.pop();
        self.typing_binds.pop();
    }

    pub fn elab_exp(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<RawExp, String> {
        assert!(self.binded_vars.is_empty());
        let e = self.elab_exp_rec(exp, handler);
        assert!(e.is_err() || self.binded_vars.is_empty());
        e
    }

    fn elab_take_parts(
        &mut self,
        bind: &Bind,
        body: &SExp,
        handler: &mut impl Handler,
    ) -> Result<(RawExp, RawExp, RawExp), String> {
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
                let map = handler.arena().alloc(RawNode::Lam {
                    var,
                    ty: domain,
                    body: map_body,
                });
                let map_ty = handler.infer(&mut self.typing_binds, map)?;
                let RawNode::Prod { body: codomain, .. } = handler.arena().get(map_ty) else {
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

                let subset = handler.arena().alloc(RawNode::SubSet {
                    var,
                    set: carrier,
                    predicate,
                });
                let domain = handler.arena().alloc(RawNode::TypeLift {
                    superset: carrier,
                    subset,
                });
                self.push_binded_var(var, domain);
                let map_body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                let map = handler.arena().alloc(RawNode::Lam {
                    var,
                    ty: domain,
                    body: map_body,
                });
                let map_ty = handler.infer(&mut self.typing_binds, map)?;
                let RawNode::Prod { body: codomain, .. } = handler.arena().get(map_ty) else {
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

    fn elab_exp_rec(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<RawExp, String> {
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
                        if parameters.is_empty() {
                            Ok(handler.arena().alloc(RawNode::DefinedConstant(definition)))
                        } else {
                            Err(format!(
                                "Defined constant {:?} cannot be applied with parameters",
                                access
                            ))
                        }
                    }
                    ItemAccessResult::Inductive(ModItemInductive { inductive, .. }) => {
                        let parameters: Vec<RawExp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;

                        Ok(handler.arena().alloc(RawNode::IndType {
                            indspec: inductive,
                            parameters,
                        }))
                    }
                    ItemAccessResult::Record(ModItemRecord {
                        type_name: _,
                        inductive,
                        ..
                    }) => {
                        let parameters: Vec<RawExp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(handler.arena().alloc(RawNode::IndType {
                            indspec: inductive,
                            parameters,
                        }))
                    }
                    ItemAccessResult::ProgramInductive(ModItemProgramInductive {
                        inductive,
                        ..
                    }) => {
                        let parameters = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(handler.arena().alloc(RawNode::ProgramIndType {
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
                                    return Ok(handler.arena().alloc(RawNode::IndCtor {
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
                                    handler.arena().alloc(RawNode::DefinedConstant(*definition));
                                return Ok(kernel::utils::assoc_apply(
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
                        ItemAccessResult::ProgramInductive(ModItemProgramInductive {
                            inductive,
                            type_name,
                            ctor_names,
                            associated_definitions,
                            ..
                        }) => {
                            if let Some((_, definition)) = associated_definitions
                                .iter()
                                .find(|(name, _)| name.as_str() == field.as_str())
                            {
                                let count = handler
                                    .env()
                                    .program_inductive(inductive)
                                    .parameters()
                                    .len();
                                let parameters =
                                    self.associated_parameters(parameters, count, handler)?;
                                let definition =
                                    handler.arena().alloc(RawNode::DefinedConstant(*definition));
                                return Ok(kernel::utils::assoc_apply(
                                    handler.arena(),
                                    definition,
                                    parameters,
                                ));
                            }
                            let Some(idx) = ctor_names
                                .iter()
                                .position(|ctor_name| ctor_name.as_str() == field.as_str())
                            else {
                                if ctor_names.is_empty() {
                                    let count = handler
                                        .env()
                                        .program_inductive(inductive)
                                        .parameters()
                                        .len();
                                    let parameters =
                                        self.associated_parameters(parameters, count, handler)?;
                                    let spec = handler.env().program_inductive(inductive);
                                    let field_index = spec.constructors()[0]
                                        .fields()
                                        .iter()
                                        .position(|(name, _)| {
                                            handler.symbol(*name) == field.as_str()
                                        })
                                        .ok_or_else(|| {
                                            format!(
                                                "Associated item {} not found in structure {}",
                                                field.as_str(),
                                                type_name.as_str()
                                            )
                                        })?;
                                    let structure_ty =
                                        handler.arena().alloc(RawNode::ProgramIndType {
                                            indspec: inductive,
                                            parameters: parameters.clone(),
                                        });
                                    let shifted_parameters = parameters
                                        .iter()
                                        .map(|parameter| {
                                            kernel::calculus::shift_bound_indices(
                                                handler.arena(),
                                                *parameter,
                                                1,
                                                0,
                                            )
                                        })
                                        .collect();
                                    let body =
                                        handler.arena().alloc(RawNode::ProgramIndProjection {
                                            indspec: inductive,
                                            parameters: shifted_parameters,
                                            value: handler.arena().bound(0),
                                            field: field_index,
                                        });
                                    let var = handler.intern("$structure");
                                    return Ok(handler.arena().alloc(RawNode::Lam {
                                        var,
                                        ty: structure_ty,
                                        body,
                                    }));
                                }
                                return Err(format!(
                                    "Constructor {} not found in Program datatype {}",
                                    field.as_str(),
                                    type_name.as_str()
                                ));
                            };
                            let count = handler
                                .env()
                                .program_inductive(inductive)
                                .parameters()
                                .len();
                            let parameters =
                                self.associated_parameters(parameters, count, handler)?;
                            let expected =
                                handler.env().program_inductive(inductive).constructors()[idx]
                                    .fields()
                                    .len();
                            if expected != 0 {
                                return Err(format!(
                                    "Program constructor {} expects {} field argument(s)",
                                    field.as_str(),
                                    expected
                                ));
                            }
                            Ok(handler.arena().alloc(RawNode::ProgramIndCtor {
                                indspec: inductive,
                                parameters,
                                idx,
                                fields: Vec::new(),
                            }))
                        }
                        ItemAccessResult::Record(record) => {
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
                                    handler.arena().alloc(RawNode::DefinedConstant(*definition));
                                return Ok(kernel::utils::assoc_apply(
                                    handler.arena(),
                                    definition,
                                    parameters,
                                ));
                            }
                            let count =
                                handler.env().inductive(record.inductive).parameters().len();
                            let parameters =
                                self.associated_parameters(parameters, count, handler)?;
                            let record_ty = handler.arena().alloc(RawNode::IndType {
                                indspec: record.inductive,
                                parameters: parameters.clone(),
                            });
                            let shifted_parameters = parameters
                                .iter()
                                .map(|parameter| {
                                    kernel::calculus::shift_bound_indices(
                                        handler.arena(),
                                        *parameter,
                                        1,
                                        0,
                                    )
                                })
                                .collect::<Vec<_>>();
                            let value = handler.arena().bound(0);
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
                            Ok(handler.arena().alloc(RawNode::Lam {
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
                    handler.field_projection(base_elab, field)
                }
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
                let mut expanded = exp.clone();
                loop {
                    expanded = match &expanded {
                        SExp::MathMacro {
                            tokens,
                            scope,
                            max_order,
                            depth,
                        } => handler.expand_math_macro(tokens, *scope, *depth, *max_order)?,
                        SExp::NamedMacro {
                            name,
                            tokens,
                            scope,
                            max_order,
                            depth,
                        } => {
                            handler.expand_named_macro(name, tokens, *scope, *depth, *max_order)?
                        }
                        _ => break,
                    };
                }
                self.elab_exp_rec(&expanded, handler)
            }
            SExp::MacroParameter(name) => Err(format!(
                "Macro capture '${}' escaped template expansion",
                name.as_str()
            )),
            SExp::ResolvedExp(exp) => Ok(*exp),
            SExp::Where { exp, clauses } => {
                let declaration_mark = self.decl_binds.len();
                let result = (|| {
                    for (name, ty, body) in clauses {
                        let ty = self.elab_exp_rec(ty, handler)?;
                        let body = self.elab_exp_rec(body, handler)?;
                        let inferred = handler.infer(&mut self.typing_binds, body)?;
                        if !kernel::calculus::convertible(handler.env(), inferred, ty) {
                            return Err(format!(
                                "where definition '{}' does not match its declared type",
                                name.as_str(),
                            ));
                        }
                        let name = handler.intern(name.as_str());
                        // `where` is non-recursive and definitions are processed in order.
                        // Store the elaborated body as the declaration's referent, so later
                        // clauses and the result expression inline it directly.
                        self.push_decl_var_exp(name, body);
                    }
                    self.elab_exp_rec(exp, handler)
                })();
                self.decl_binds.truncate(declaration_mark);
                result
            }
            SExp::Sort(sort) => Ok(handler.arena().sort(*sort)),
            SExp::ValueType => Ok(handler.arena().alloc(RawNode::ValueType)),
            SExp::ThunkType { computation_ty } => {
                let computation_ty = self.elab_exp_rec(computation_ty, handler)?;
                Ok(handler.arena().alloc(RawNode::ThunkType { computation_ty }))
            }
            SExp::ReturnType { value_ty } => {
                let value_ty = self.elab_exp_rec(value_ty, handler)?;
                Ok(handler.arena().alloc(RawNode::ReturnType { value_ty }))
            }
            SExp::ComputationFunction { domain, codomain } => {
                let domain = self.elab_exp_rec(domain, handler)?;
                let codomain = self.elab_exp_rec(codomain, handler)?;
                Ok(handler
                    .arena()
                    .alloc(RawNode::ComputationFunction { domain, codomain }))
            }
            SExp::Thunk { computation } => {
                let computation = self.elab_exp_rec(computation, handler)?;
                Ok(handler.arena().alloc(RawNode::Thunk { computation }))
            }
            SExp::Return { value } => {
                let value = self.elab_exp_rec(value, handler)?;
                Ok(handler.arena().alloc(RawNode::Return { value }))
            }
            SExp::Force { value } => {
                let value = self.elab_exp_rec(value, handler)?;
                Ok(handler.arena().alloc(RawNode::Force { value }))
            }
            SExp::ComputationLam {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.elab_exp_rec(value_ty, handler)?;
                let var = handler.intern(var.as_str());
                self.push_program_value_var(var, value_ty);
                let body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                Ok(handler.arena().alloc(RawNode::ComputationLam {
                    var,
                    value_ty,
                    body,
                }))
            }
            SExp::ComputationApp { computation, value } => {
                let computation = self.elab_exp_rec(computation, handler)?;
                let value = self.elab_exp_rec(value, handler)?;
                Ok(handler
                    .arena()
                    .alloc(RawNode::ComputationApp { computation, value }))
            }
            SExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let computation = self.elab_exp_rec(computation, handler)?;
                let value_ty = self.elab_exp_rec(value_ty, handler)?;
                let var = handler.intern(var.as_str());
                self.push_program_value_var(var, value_ty);
                let body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                Ok(handler.arena().alloc(RawNode::Sequence {
                    computation,
                    var,
                    value_ty,
                    body,
                }))
            }
            SExp::ValueLet { var, value, body } => {
                let value = self.elab_exp_rec(value, handler)?;
                let value_ty = {
                    let mut context = self.kernel_context(handler);
                    let mut session = kernel::derivation::CheckSession::new(
                        handler.env(),
                        handler.current_module(),
                        &mut context,
                    );
                    session
                        .infer_value(value)
                        .map_err(|error| format!("failed to infer \\vlet value: {error:?}"))?
                };
                let var = handler.intern(var.as_str());
                self.push_program_value_var(var, value_ty);
                let body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                Ok(handler
                    .arena()
                    .alloc(RawNode::ValueLet { var, value, body }))
            }
            SExp::ProgramCase {
                path,
                scrutinee,
                branches,
            } => {
                let ItemAccessResult::ProgramInductive(item) =
                    handler.get_item_from_access_path(path)?
                else {
                    return Err("\\vcase path must name a Program datatype".into());
                };
                if branches.len() != item.ctor_names.len() {
                    return Err(
                        "\\vcase must contain exactly one ordered branch per constructor".into(),
                    );
                }
                let scrutinee = self.elab_exp_rec(scrutinee, handler)?;
                let scrutinee_ty = {
                    let mut context = self.kernel_context(handler);
                    let mut session = kernel::derivation::CheckSession::new(
                        handler.env(),
                        handler.current_module(),
                        &mut context,
                    );
                    session
                        .infer_value(scrutinee)
                        .map_err(|error| format!("failed to infer \\vcase scrutinee: {error:?}"))?
                };
                let RawNode::ProgramIndType {
                    indspec,
                    parameters,
                } = handler.arena().get(scrutinee_ty)
                else {
                    return Err("\\vcase scrutinee must have a Program datatype type".into());
                };
                if indspec != item.inductive {
                    return Err("\\vcase scrutinee datatype does not match its path".into());
                }
                let mut elaborated = Vec::with_capacity(branches.len());
                let spec = handler.env().program_inductive(item.inductive).clone();
                for (index, (constructor, binders, body)) in branches.iter().enumerate() {
                    if constructor != &item.ctor_names[index] {
                        return Err(format!(
                            "\\vcase constructor mismatch: expected {}, found {}",
                            item.ctor_names[index].as_str(),
                            constructor.as_str()
                        ));
                    }
                    let fields = spec.constructors()[index]
                        .instantiated_fields(handler.arena(), &parameters);
                    if binders.len() != fields.len() {
                        return Err(format!(
                            "\\vcase branch {} expects {} binders",
                            constructor.as_str(),
                            fields.len()
                        ));
                    }
                    let mut binder_ids = Vec::with_capacity(binders.len());
                    for (binder, (_, field_ty)) in binders.iter().zip(&fields) {
                        let binder = handler.intern(binder.as_str());
                        self.push_program_value_var(binder, *field_ty);
                        binder_ids.push(binder);
                    }
                    let body = self.elab_exp_rec(body, handler)?;
                    for _ in binders {
                        self.pop_binded_var();
                    }
                    elaborated.push(ProgramCaseBranch {
                        binders: binder_ids,
                        body,
                    });
                }
                Ok(handler.arena().alloc(RawNode::ProgramCase {
                    indspec: item.inductive,
                    scrutinee,
                    branches: elaborated,
                }))
            }
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
                                handler.arena().alloc(RawNode::Prod {
                                    var,
                                    ty: ty_elab,
                                    body: body_elab,
                                })
                            } else {
                                handler.arena().alloc(RawNode::Lam {
                                    var,
                                    ty: ty_elab,
                                    body: body_elab,
                                })
                            });
                        }

                        let ty_elab = self.elab_exp_rec(&right_bind.ty, handler)?;

                        let mut telescope: Vec<(SymbolId, RawExp)> = vec![];
                        for var in &right_bind.vars {
                            let var = handler.intern(var.as_str());
                            telescope.push((var, ty_elab));
                            self.push_named_binder(var, ty_elab, handler);
                        }

                        let body_elab = self.elab_exp_rec(body, handler)?;

                        for _ in &right_bind.vars {
                            self.pop_binded_var();
                        }

                        Ok(if is_prod {
                            kernel::utils::assoc_prod(handler.arena(), telescope, body_elab)
                        } else {
                            kernel::utils::assoc_lam(handler.arena(), telescope, body_elab)
                        })
                    }
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var = handler.intern(var.as_str());
                        self.push_binded_var(var, ty_elab);
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        let subset = handler.arena().alloc(RawNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        });

                        let refined_ty = handler.arena().alloc(RawNode::TypeLift {
                            superset: ty_elab,
                            subset,
                        });
                        self.push_binded_var(var, refined_ty);
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();

                        Ok(if is_prod {
                            handler.arena().alloc(RawNode::Prod {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        } else {
                            handler.arena().alloc(RawNode::Lam {
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

                        let subset = handler.arena().alloc(RawNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        });
                        let refined_ty = handler.arena().alloc(RawNode::TypeLift {
                            superset: ty_elab,
                            subset,
                        });
                        self.push_binded_var(var, refined_ty);
                        let proof = handler.intern(proof_var.as_str());
                        self.push_binded_var(proof, predicate_elab);
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();
                        self.pop_binded_var();
                        let body_elab = handler.arena().alloc(RawNode::Prod {
                            var: proof,
                            ty: predicate_elab,
                            body: body_elab,
                        });

                        Ok(if is_prod {
                            handler.arena().alloc(RawNode::Prod {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        } else {
                            handler.arena().alloc(RawNode::Lam {
                                var,
                                ty: refined_ty,
                                body: body_elab,
                            })
                        })
                    }
                }
            }
            SExp::App {
                func,
                arg,
                piped: _,
            } => {
                let mut arguments = vec![arg.as_ref()];
                let mut head = func.as_ref();
                while let SExp::App {
                    func,
                    arg,
                    piped: _,
                } = head
                {
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
                            if let RawNode::IndType {
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
                        ItemAccessResult::ProgramInductive(item)
                            if item.ctor_names.is_empty()
                                && !item
                                    .associated_definitions
                                    .iter()
                                    .any(|(name, _)| name == field) =>
                        {
                            let value = self.elab_exp_rec(arguments[0], handler)?;
                            let value_ty = handler.infer(&mut self.typing_binds, value)?;
                            if let RawNode::ProgramIndType {
                                indspec,
                                parameters,
                            } = handler.arena().get(value_ty)
                                && indspec == item.inductive
                            {
                                let field_index = handler
                                    .env()
                                    .program_inductive(item.inductive)
                                    .constructors()[0]
                                    .fields()
                                    .iter()
                                    .position(|(name, _)| handler.symbol(*name) == field.as_str())
                                    .ok_or_else(|| {
                                        format!(
                                            "Associated item {} not found in structure {}",
                                            field.as_str(),
                                            item.type_name.as_str()
                                        )
                                    })?;
                                return Ok(handler.arena().alloc(RawNode::ProgramIndProjection {
                                    indspec: item.inductive,
                                    parameters,
                                    value,
                                    field: field_index,
                                }));
                            }
                        }
                        _ => {}
                    }
                }
                if let SExp::AssociatedAccess { base, field } = head
                    && let SExp::AccessPath { access, parameters } = base.as_ref()
                    && let ItemAccessResult::ProgramInductive(item) =
                        handler.get_item_from_access_path(access)?
                {
                    let Some(idx) = item
                        .ctor_names
                        .iter()
                        .position(|ctor_name| ctor_name.as_str() == field.as_str())
                    else {
                        // Associated definitions and structure projections use
                        // ordinary application after their head is elaborated.
                        let func_elab = self.elab_exp_rec(func, handler)?;
                        let arg_elab = self.elab_exp_rec(arg, handler)?;
                        return Ok(handler.arena().alloc(RawNode::App {
                            func: func_elab,
                            arg: arg_elab,
                        }));
                    };
                    let parameters = parameters
                        .iter()
                        .map(|parameter| self.elab_exp_rec(parameter, handler))
                        .collect::<Result<Vec<_>, _>>()?;
                    let expected = handler
                        .env()
                        .program_inductive(item.inductive)
                        .constructors()[idx]
                        .fields()
                        .len();
                    if arguments.len() != expected {
                        return Err(format!(
                            "Program constructor {} expects {} field argument(s), found {}",
                            field.as_str(),
                            expected,
                            arguments.len()
                        ));
                    }
                    let fields = arguments
                        .into_iter()
                        .map(|argument| self.elab_exp_rec(argument, handler))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(handler.arena().alloc(RawNode::ProgramIndCtor {
                        indspec: item.inductive,
                        parameters,
                        idx,
                        fields,
                    }));
                }
                let func_elab = self.elab_exp_rec(func, handler)?;
                let arg_elab = self.elab_exp_rec(arg, handler)?;
                Ok(handler.arena().alloc(RawNode::App {
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
                Ok(handler.arena().alloc(RawNode::SubsetIntro {
                    superset: superset_elab,
                    subset: subset_elab,
                    element: element_elab,
                    proof: proof_elab,
                }))
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let (ctor_names, inductive) = match handler.get_item_from_access_path(path)? {
                    ItemAccessResult::Inductive(ModItemInductive {
                        ctor_names,
                        inductive,
                        ..
                    }) => (ctor_names, inductive),
                    ItemAccessResult::ProgramInductive(ModItemProgramInductive {
                        ctor_names,
                        reflected,
                        ..
                    }) => (ctor_names, reflected),
                    _ => {
                        return Err(format!(
                            "Expected inductive type in ind elim access path {:?}",
                            path
                        ));
                    }
                };

                let elim_elab = self.elab_exp_rec(elim, handler)?;
                let return_type_elab = self.elab_exp_rec(return_type, handler)?;
                let mut cases_elab: Vec<RawExp> = vec![];
                for (idx, (ctor_name, case)) in cases.iter().enumerate() {
                    let case_elab = self.elab_exp_rec(case, handler)?;
                    if ctor_names[idx].as_str() != ctor_name.as_str() {
                        return Err(format!(
                            "Constructor name mismatch in ind elim: expected {}, found {}",
                            ctor_names[idx].as_str(),
                            ctor_name.as_str()
                        ));
                    }
                    cases_elab.push(case_elab);
                }

                Ok(handler.arena().alloc(RawNode::IndElim {
                    indspec: inductive,
                    elim: elim_elab,
                    return_type: return_type_elab,
                    cases: cases_elab,
                }))
            }
            SExp::IndElimPrim {
                path,
                parameters,
                sort,
            } => {
                let inductive = match handler.get_item_from_access_path(path)? {
                    ItemAccessResult::Inductive(ModItemInductive { inductive, .. }) => inductive,
                    ItemAccessResult::ProgramInductive(ModItemProgramInductive {
                        reflected,
                        ..
                    }) => reflected,
                    _ => {
                        return Err(format!(
                            "Expected inductive type in ind elim prim access path {:?}",
                            path
                        ));
                    }
                };

                let parameters: Vec<RawExp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                Ok(InductiveTypeSpecs::primitive_recursion(
                    handler.arena(),
                    inductive,
                    handler.env().inductive(inductive),
                    parameters,
                    *sort,
                ))
            }
            SExp::RunStep {
                state_ty,
                result_ty,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                Ok(handler.arena().alloc(RawNode::RunStep {
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
                Ok(handler.arena().alloc(RawNode::Continue {
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
                Ok(handler.arena().alloc(RawNode::Finish {
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
                let mut state_ty = self.elab_exp_rec(state_ty, handler)?;
                let mut result_ty = self.elab_exp_rec(result_ty, handler)?;
                let mut step = self.elab_exp_rec(step, handler)?;
                let mut state = self.elab_exp_rec(state, handler)?;
                if !self.is_set_type(handler, state_ty) {
                    let context = self.program_context(handler);
                    state_ty = kernel::reflection::reflect_type(handler.env(), state_ty)
                        .map_err(|error| format!("cannot reflect Acc state type: {error}"))?;
                    result_ty = kernel::reflection::reflect_type(handler.env(), result_ty)
                        .map_err(|error| format!("cannot reflect Acc result type: {error}"))?;
                    step = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        step,
                    )
                    .map_err(|error| format!("cannot reflect Acc step: {error}"))?;
                    state = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        state,
                    )
                    .map_err(|error| format!("cannot reflect Acc state: {error}"))?;
                }
                Ok(handler.arena().alloc(RawNode::Acc {
                    state_ty,
                    result_ty,
                    step,
                    state,
                }))
            }
            SExp::RfType { compute_ty } => {
                let _ = compute_ty;
                Err("\\RfType was removed; reflection is performed by the kernel at Box/Force and reflected Program eliminators".to_string())
            }
            SExp::RfTerm { compute_ty, term } => {
                let _ = (compute_ty, term);
                Err("\\RfTerm was removed; reflection is performed by the kernel at Box/Force and reflected Program eliminators".to_string())
            }
            SExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let initial = self.elab_exp_rec(initial, handler)?;
                let is_set = self.is_set_type(handler, state_ty);
                if is_set {
                    Ok(handler.arena().alloc(RawNode::SetRun {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                    }))
                } else {
                    Ok(handler.arena().alloc(RawNode::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                    }))
                }
            }
            SExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let step = self.elab_exp_rec(step, handler)?;
                let initial = self.elab_exp_rec(initial, handler)?;
                let transition = self.elab_exp_rec(transition, handler)?;
                let is_set = self.is_set_type(handler, state_ty);
                if is_set {
                    Ok(handler.arena().alloc(RawNode::SetRunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                    }))
                } else {
                    Ok(handler.arena().alloc(RawNode::RunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                    }))
                }
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
                Ok(handler.arena().alloc(RawNode::RunStepRec {
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
                    scrutinee,
                }))
            }
            SExp::Proof { proposition } => {
                let proposition = self.elab_exp_rec(proposition, handler)?;
                Ok(handler.arena().alloc(RawNode::Proof { proposition }))
            }
            SExp::BoxType { program_ty } => {
                let program_ty = self.elab_exp_rec(program_ty, handler)?;
                Ok(handler.arena().alloc(RawNode::BoxType { program_ty }))
            }
            SExp::BoxProgram {
                program_ty,
                program,
            } => {
                let program_ty = self.elab_exp_rec(program_ty, handler)?;
                let program = self.elab_exp_rec(program, handler)?;
                Ok(handler.arena().alloc(RawNode::BoxProgram {
                    program_ty,
                    program,
                }))
            }
            SExp::ForceBox { program_ty, boxed } => {
                let program_ty = self.elab_exp_rec(program_ty, handler)?;
                let boxed = self.elab_exp_rec(boxed, handler)?;
                Ok(handler
                    .arena()
                    .alloc(RawNode::ForceBox { program_ty, boxed }))
            }
            SExp::BoxApp { function, argument } => {
                let function = self.elab_exp_rec(function, handler)?;
                let argument = self.elab_exp_rec(argument, handler)?;
                Ok(handler
                    .arena()
                    .alloc(RawNode::BoxApp { function, argument }))
            }
            SExp::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => {
                let mut state_ty = self.elab_exp_rec(state_ty, handler)?;
                let mut result_ty = self.elab_exp_rec(result_ty, handler)?;
                let mut step = self.elab_exp_rec(step, handler)?;
                let mut state = self.elab_exp_rec(state, handler)?;
                let predecessors = self.elab_exp_rec(predecessors, handler)?;
                if !self.is_set_type(handler, state_ty) {
                    let context = self.program_context(handler);
                    state_ty = kernel::reflection::reflect_type(handler.env(), state_ty)
                        .map_err(|error| format!("cannot reflect Acc state type: {error}"))?;
                    result_ty = kernel::reflection::reflect_type(handler.env(), result_ty)
                        .map_err(|error| format!("cannot reflect Acc result type: {error}"))?;
                    step = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        step,
                    )
                    .map_err(|error| format!("cannot reflect Acc step: {error}"))?;
                    state = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        state,
                    )
                    .map_err(|error| format!("cannot reflect Acc state: {error}"))?;
                }
                Ok(handler.arena().alloc(RawNode::AccIntro {
                    state_ty,
                    result_ty,
                    step,
                    state,
                    predecessors,
                }))
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
                let mut state_ty = self.elab_exp_rec(state_ty, handler)?;
                let mut result_ty = self.elab_exp_rec(result_ty, handler)?;
                let mut step = self.elab_exp_rec(step, handler)?;
                let mut from = self.elab_exp_rec(from, handler)?;
                let mut to = self.elab_exp_rec(to, handler)?;
                let accessibility = self.elab_exp_rec(accessibility, handler)?;
                let transition = self.elab_exp_rec(transition, handler)?;
                if !self.is_set_type(handler, state_ty) {
                    let context = self.program_context(handler);
                    state_ty = kernel::reflection::reflect_type(handler.env(), state_ty)
                        .map_err(|error| format!("cannot reflect Acc state type: {error}"))?;
                    result_ty = kernel::reflection::reflect_type(handler.env(), result_ty)
                        .map_err(|error| format!("cannot reflect Acc result type: {error}"))?;
                    step = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        step,
                    )
                    .map_err(|error| format!("cannot reflect Acc step: {error}"))?;
                    from = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        from,
                    )
                    .map_err(|error| format!("cannot reflect Acc source: {error}"))?;
                    to = kernel::reflection::reflect_term(
                        handler.env(),
                        handler.current_module(),
                        &context,
                        to,
                    )
                    .map_err(|error| format!("cannot reflect Acc target: {error}"))?;
                }
                Ok(handler.arena().alloc(RawNode::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from,
                    to,
                    accessibility,
                    transition,
                }))
            }

            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                let parameters: Vec<RawExp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                let item = handler.get_item_from_access_path(access)?;
                let (declared_names, program_inductive, pts_inductive) = match item {
                    ItemAccessResult::Record(record) => {
                        let constructor =
                            &handler.env().inductive(record.inductive).constructors()[0];
                        let names = constructor
                            .telescope
                            .iter()
                            .map(|binder| match binder {
                                kernel::inductive::CtorBinder::Simple((name, _)) => {
                                    handler.symbol(*name).to_string()
                                }
                                _ => {
                                    unreachable!("structure fields are simple constructor binders")
                                }
                            })
                            .collect::<Vec<_>>();
                        (names, None, Some(record.inductive))
                    }
                    ItemAccessResult::ProgramInductive(item) if item.ctor_names.is_empty() => {
                        let names = handler
                            .env()
                            .program_inductive(item.inductive)
                            .constructors()[0]
                            .fields()
                            .iter()
                            .map(|(name, _)| handler.symbol(*name).to_string())
                            .collect::<Vec<_>>();
                        (names, Some(item.inductive), None)
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

                if let Some(inductive) = program_inductive {
                    Ok(handler.arena().alloc(RawNode::ProgramIndCtor {
                        indspec: inductive,
                        parameters,
                        idx: 0,
                        fields: ordered,
                    }))
                } else {
                    let constructor = handler.arena().alloc(RawNode::IndCtor {
                        indspec: pts_inductive.expect("one structure representation was selected"),
                        parameters,
                        idx: 0,
                    });
                    Ok(kernel::utils::assoc_apply(
                        handler.arena(),
                        constructor,
                        ordered,
                    ))
                }
            }

            SExp::PowerSet { set } => {
                let set_elab = self.elab_exp_rec(set, handler)?;
                Ok(handler.arena().alloc(RawNode::PowerSet { set: set_elab }))
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
                Ok(handler.arena().alloc(RawNode::SubSet {
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
                Ok(handler.arena().alloc(RawNode::Pred {
                    superset: superset_elab,
                    subset: subset_elab,
                    element: element_elab,
                }))
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                Ok(handler.arena().alloc(RawNode::TypeLift {
                    superset: superset_elab,
                    subset: subset_elab,
                }))
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(left, handler)?;
                let right_elab = self.elab_exp_rec(right, handler)?;
                Ok(handler.arena().alloc(RawNode::Equal {
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
                    Ok(handler.arena().alloc(RawNode::Exists { set: ty_elab }))
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

                        handler.arena().alloc(RawNode::SubSet {
                            var,
                            set: ty_elab,
                            predicate: predicate_elab,
                        })
                    };
                    Ok(handler
                        .arena()
                        .alloc(RawNode::Exists { set: subset_as_exp }))
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
                Ok(handler.arena().alloc(RawNode::TakeSet {
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
                Ok(handler.arena().alloc(RawNode::TakeProp {
                    domain,
                    proposition,
                    map,
                    existence,
                }))
            }
            SExp::ExistsIntro { element, set } => {
                let element = self.elab_exp_rec(element, handler)?;
                let set = self.elab_exp_rec(set, handler)?;
                Ok(handler.arena().alloc(RawNode::ExistsIntro { element, set }))
            }
            SExp::SubsetElim {
                element,
                subset,
                superset,
            } => {
                let element = self.elab_exp_rec(element, handler)?;
                let subset = self.elab_exp_rec(subset, handler)?;
                let superset = self.elab_exp_rec(superset, handler)?;
                Ok(handler.arena().alloc(RawNode::SubsetElim {
                    element,
                    subset,
                    superset,
                }))
            }
            SExp::IdRefl { element } => {
                let element = self.elab_exp_rec(element, handler)?;
                Ok(handler.arena().alloc(RawNode::IdRefl { element }))
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
                Ok(handler.arena().alloc(RawNode::IdElim {
                    left,
                    right,
                    var,
                    ty,
                    predicate,
                    base,
                    equality,
                }))
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
                Ok(handler.arena().alloc(RawNode::AxiomSetExt {
                    left,
                    right,
                    left_to_right,
                    right_to_left,
                }))
            }
            SExp::AxiomFunExt {
                left,
                right,
                pointwise,
            } => {
                let left = self.elab_exp_rec(left, handler)?;
                let right = self.elab_exp_rec(right, handler)?;
                let pointwise = self.elab_exp_rec(pointwise, handler)?;
                Ok(handler.arena().alloc(RawNode::AxiomFunExt {
                    left,
                    right,
                    pointwise,
                }))
            }
            SExp::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => {
                let domain = self.elab_exp_rec(domain, handler)?;
                let family = self.elab_exp_rec(family, handler)?;
                let inhabited = self.elab_exp_rec(inhabited, handler)?;
                Ok(handler
                    .arena()
                    .alloc(RawNode::AxiomClassicalIndefiniteChoice {
                        domain,
                        family,
                        inhabited,
                    }))
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
                Ok(handler.arena().alloc(RawNode::TakeEq {
                    func,
                    domain,
                    codomain,
                    element,
                    existence,
                    uniqueness,
                }))
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
                            term = SExp::App {
                                func: Box::new(SExp::Lam {
                                    bind: Bind::Named(RightBind {
                                        vars: vec![var.clone()],
                                        ty: Box::new(ty.clone()),
                                    }),
                                    body: Box::new(term),
                                }),
                                arg: Box::new(body.clone()),
                                piped: false,
                            };
                        }
                        Statement::TakeSet {
                            bind,
                            existence,
                            uniqueness,
                        } => {
                            term = SExp::TakeSet {
                                bind: bind.clone(),
                                body: Box::new(term),
                                existence: Box::new(existence.clone()),
                                uniqueness: Box::new(uniqueness.clone()),
                            };
                        }
                        Statement::TakeProp { bind, existence } => {
                            term = SExp::TakeProp {
                                bind: bind.clone(),
                                body: Box::new(term),
                                existence: Box::new(existence.clone()),
                            };
                        }
                        Statement::Sufficient { map, map_ty: _ } => {
                            term = SExp::App {
                                func: Box::new(map.clone()),
                                arg: Box::new(term),
                                piped: false,
                            };
                        }
                    }
                }
                self.elab_exp_rec(&term, handler)
            }
        }
    }
}
