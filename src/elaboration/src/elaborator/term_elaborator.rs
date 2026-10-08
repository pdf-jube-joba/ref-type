use crate::elaborator::ItemAccessResult;
use crate::elaborator::profiling::ProfileTimer;
use crate::hir::*;
use crate::items::{ModItemDefinition, ModItemInductive, ModItemRecord};
use crate::metavariables::ElaborationError;
use crate::raw::calculus::{
    exp_contains_bound, instantiate, instantiate_telescope, shift_bound_indices, type_head_normal,
    whnf,
};
use crate::raw::environment::{CrateEnv, DefinedConstant, ModuleItem};
use crate::raw::exp::*;
use crate::raw::ids::*;
use crate::raw::program::{ComputationTerm, ComputationType, ValueType};

pub(crate) trait Handler {
    fn reflect_front_expression(&mut self, expression: &SExp) -> Result<Exp, ElaborationError>;
    fn check_program_member(&mut self, value: &SExp, ty: &SExp) -> Result<(), ElaborationError>;
    fn locate_error(&mut self, span: SourceSpan);
    fn env(&self) -> &CrateEnv;
    fn arena(&self) -> &Arena;
    fn instantiate_module(
        &mut self,
        path: &ModuleInstantiatePath,
        name: &Identifier,
        scope: &mut LocalScope,
    ) -> Result<(), ElaborationError>;
    fn direct_module_definition(
        &mut self,
        path: &ModuleInstantiatePath,
        name: &Identifier,
        access: &LocalAccess,
        scope: &mut LocalScope,
        arguments: &[&SExp],
    ) -> Result<Option<Exp>, ElaborationError>;
    fn materialize_module_term(
        &mut self,
        context: &ExpContext,
        term: Exp,
    ) -> Result<Exp, ElaborationError>;
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ElaborationError>;
    fn associated_reference(&mut self, access: &LocalAccess, field: &Identifier, span: SourceSpan);
    fn field_projection(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        field_name: &Identifier,
    ) -> Result<Exp, ElaborationError>;
    fn infer(&mut self, local_ctx: &mut ExpContext, e: Exp) -> Result<Exp, ElaborationError>;
    fn check(
        &mut self,
        local_ctx: &mut ExpContext,
        e: Exp,
        ty: Exp,
    ) -> Result<(), ElaborationError>;
    fn unify(
        &mut self,
        local_ctx: &ExpContext,
        left: Exp,
        right: Exp,
    ) -> Result<(), ElaborationError>;
    fn zonk(&self, exp: Exp) -> Exp;
    fn match_parameters(
        &mut self,
        local_ctx: &mut ExpContext,
        scrutinee: Exp,
        inductive: InductiveId,
    ) -> Result<Vec<Exp>, ElaborationError>;
    fn elaborate_boxed_computation_type(
        &mut self,
        expression: &SExp,
    ) -> Result<ComputationType, ElaborationError>;
    fn elaborate_boxed_program(
        &mut self,
        ty: &SExp,
        computation: &SExp,
    ) -> Result<(ComputationType, ComputationTerm), ElaborationError>;
    fn elaborate_program_type_arguments(
        &mut self,
        expressions: &[SExp],
        expected: usize,
    ) -> Result<Vec<ValueType>, ElaborationError>;
    fn intern(&mut self, name: &str) -> SymbolId;
    fn symbol(&self, symbol: SymbolId) -> &str;
    fn fresh_meta(
        &mut self,
        kind: SurfaceMeta,
        span: SourceSpan,
        local_context: &ExpContext,
    ) -> Result<Exp, ElaborationError>;
    fn assign_meta(&mut self, meta: Exp, value: Exp) -> Result<(), ElaborationError>;
    fn record_source(&mut self, term: Exp, span: SourceSpan);
    fn intern_name(&mut self, name: &Identifier) -> SymbolId;
    fn reflect_program_expression(
        &mut self,
        parameter: resolve::hir::BindingId,
        expression: &SExp,
    ) -> Result<Exp, ElaborationError>;
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
    // Resolve the declaration metadata only after reduction has identified the
    // actual datatype. Refinements are deliberately not stripped here.
    fn inductive_item(
        inductive: InductiveId,
        handler: &impl Handler,
    ) -> Result<ItemAccessResult, ElaborationError> {
        let item = handler
            .env()
            .item_for_inductive(inductive)
            .ok_or("Inductive declaration metadata was not found")?;
        let name = |name: &String| Identifier(name.clone());
        Ok(match item {
            ModuleItem::Inductive {
                name: type_name,
                constructor_names,
                associated_definitions,
                ..
            } => ItemAccessResult::Inductive(ModItemInductive {
                type_name: name(type_name),
                ctor_names: constructor_names.iter().map(name).collect(),
                associated_definitions: associated_definitions
                    .iter()
                    .map(|(n, d)| (name(n), *d))
                    .collect(),
                inductive,
            }),
            ModuleItem::Record {
                name: type_name,
                associated_definitions,
                ..
            } => ItemAccessResult::Record(ModItemRecord {
                type_name: name(type_name),
                associated_definitions: associated_definitions
                    .iter()
                    .map(|(n, d)| (name(n), *d))
                    .collect(),
                inductive,
            }),
            ModuleItem::ProgramInductive {
                name: type_name,
                constructor_names,
                ..
            } => ItemAccessResult::Inductive(ModItemInductive {
                type_name: name(type_name),
                ctor_names: constructor_names.iter().map(name).collect(),
                associated_definitions: Vec::new(),
                inductive,
            }),
            ModuleItem::Definition { .. } => unreachable!(),
        })
    }

    fn definition_reference(
        &mut self,
        definition: DefId,
        arguments: Vec<Exp>,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        let DefinedConstant::Contextual { parameters, ty, .. } =
            handler.env().resolve_definition(definition)?.clone()
        else {
            let constant = handler.arena().alloc(ExpNode::DefinedConstant(definition));
            return Ok(crate::raw::utils::assoc_apply(
                handler.arena(),
                constant,
                arguments,
            ));
        };
        if arguments.len() > parameters.len() {
            return Err(format!(
                "Definition expects at most {} argument(s), found {}",
                parameters.len(),
                arguments.len()
            )
            .into());
        }
        for (index, argument) in arguments.iter().enumerate() {
            let expected =
                instantiate_telescope(handler.arena(), parameters[index].1, &arguments[..index]);
            handler.check(&mut self.typing_binds, *argument, expected)?;
        }
        let remaining = parameters[arguments.len()..].to_vec();
        let reference = handler.arena().alloc(ExpNode::DefinitionInstance {
            definition,
            arguments: (0..parameters.len())
                .rev()
                .map(|index| handler.arena().exp_bound(index))
                .collect(),
        });
        let body = crate::raw::utils::assoc_lam(handler.arena(), remaining.clone(), reference);
        let value = instantiate_telescope(handler.arena(), body, &arguments);
        if !remaining.is_empty() {
            let ty = crate::raw::utils::assoc_prod(handler.arena(), remaining, ty);
            let ty = instantiate_telescope(handler.arena(), ty, &arguments);
            handler.check(&mut self.typing_binds, value, ty)?;
        }
        Ok(value)
    }

    fn elab_structure_literal(
        &mut self,
        ty: Exp,
        fields: &[(Identifier, SExp)],
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        let ty = whnf(handler.env(), handler.zonk(ty));
        if let ExpNode::TypeLift { superset, subset } = handler.arena().get(ty) {
            let data_ty = whnf(handler.env(), superset);
            let ExpNode::IndType { indspec, .. } = handler.arena().get(data_ty) else {
                return Err("expected a structure data type".into());
            };
            if handler.env().record_for_inductive(indspec).is_none() {
                return Err("expected a structure data type".into());
            }
            let constructor = &handler.env().inductive(indspec).constructors()[0];
            let data_names = constructor
                .telescope
                .iter()
                .map(|binder| match binder {
                    crate::raw::inductive::CtorBinder::Simple((name, _)) => {
                        handler.symbol(*name).to_owned()
                    }
                    _ => unreachable!("structure fields are simple constructor binders"),
                })
                .collect::<Vec<_>>();
            let (data, laws): (Vec<_>, Vec<_>) = fields
                .iter()
                .cloned()
                .partition(|(name, _)| data_names.iter().any(|field| field == name.as_str()));
            let element = self.elab_structure_literal(superset, &data, handler)?;
            let law_ty = handler.arena().alloc(ExpNode::Pred {
                superset,
                subset,
                element,
            });
            let proof = self.elab_structure_literal(law_ty, &laws, handler)?;
            return Ok(handler.arena().alloc(ExpNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            }));
        }
        let ExpNode::IndType {
            indspec,
            parameters,
        } = handler.arena().get(ty)
        else {
            return Err("expected a structure type in a structure literal".into());
        };
        if handler.env().record_for_inductive(indspec).is_none() {
            return Err("expected a structure type in a structure literal".into());
        }
        let (substitutions, explicit) = handler
            .arena()
            .split_inductive_arguments(indspec, &parameters);
        let constructor_spec = handler.env().inductive(indspec).constructors()[0].clone();
        let constructor = handler.arena().alloc(ExpNode::IndCtor {
            indspec,
            parameters: parameters.clone(),
            idx: 0,
        });
        let mut constructor_ty = handler.infer(&mut self.typing_binds, constructor)?;
        let mut supplied = std::collections::HashMap::new();
        for (name, value) in fields {
            if supplied.insert(name.as_str(), value).is_some() {
                return Err(format!(
                    "Structure field {} was supplied more than once",
                    name.as_str()
                )
                .into());
            }
        }
        let mut ordered = Vec::with_capacity(constructor_spec.telescope.len());
        for binder in &constructor_spec.telescope {
            let crate::raw::inductive::CtorBinder::Simple((name, _)) = binder else {
                unreachable!("structure fields are simple constructor binders")
            };
            let name = handler.symbol(*name).to_owned();
            let ExpNode::Prod {
                ty: expected,
                body: remaining,
                ..
            } = handler.arena().get(whnf(handler.env(), constructor_ty))
            else {
                return Err("record constructor has too few fields".into());
            };
            let value = if let Some(value) = supplied.remove(name.as_str()) {
                self.elab_with_expected(value, expected, handler)?
            } else {
                let default_name = format!("<default:{name}>");
                let Some(crate::raw::environment::ModuleItem::Record {
                    associated_definitions,
                    ..
                }) = handler.env().record_for_inductive(indspec)
                else {
                    unreachable!("structure type was checked above")
                };
                let definition = associated_definitions
                    .iter()
                    .find(|(name, _)| name == &default_name)
                    .map(|(_, definition)| *definition)
                    .ok_or_else(|| format!("Missing structure field {name}"))?;
                let arguments = explicit
                    .iter()
                    .copied()
                    .chain(ordered.iter().copied())
                    .collect::<Vec<_>>();
                let value = if substitutions.is_empty() {
                    self.definition_reference(definition, arguments, handler)?
                } else {
                    crate::kernel_bridge::captured_definition(
                        handler.env(),
                        definition,
                        &substitutions,
                        &arguments,
                    )?
                };
                handler.check(&mut self.typing_binds, value, expected)?;
                value
            };
            constructor_ty = instantiate(handler.arena(), remaining, value);
            ordered.push(value);
        }
        if let Some(name) = supplied.keys().next() {
            return Err(format!("Unknown structure field {name}").into());
        }
        Ok(crate::raw::utils::assoc_apply(
            handler.arena(),
            constructor,
            ordered,
        ))
    }

    fn elab_subset(
        &mut self,
        subset: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        let expression = self.elab_exp_rec(subset, handler)?;
        let normalized = whnf(handler.env(), handler.zonk(expression));
        Ok(match handler.arena().get(normalized) {
            ExpNode::TypeLift { subset, .. } => subset,
            _ => expression,
        })
    }

    pub(crate) fn elab_with_expected(
        &mut self,
        exp: &SExp,
        expected: Exp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        if let SExp::Lam {
            bind: Bind::Named(bind),
            body,
        } = exp
            && !bind.vars.is_empty()
        {
            let bindings_mark = self.bindings.len();
            let context_mark = self.typing_binds.len();
            let result = (|| {
                let annotation = self.elab_exp_rec(&bind.ty, handler)?;
                let mut expected = Some(expected);
                let mut telescope = Vec::new();
                for (depth, name) in bind.vars.iter().enumerate() {
                    let annotation = shift_bound_indices(handler.arena(), annotation, depth, 0);
                    let normalized = expected.map(|ty| whnf(handler.env(), handler.zonk(ty)));
                    expected = match normalized.map(|ty| handler.arena().get(ty)) {
                        Some(ExpNode::Prod { ty, body, .. }) => {
                            handler.unify(&self.typing_binds, annotation, ty)?;
                            Some(body)
                        }
                        _ => None,
                    };
                    let var = handler.intern_name(name);
                    telescope.push((var, annotation));
                    self.push_named_binder(var, annotation, handler);
                    // An unknown expected type still uses ordinary inference.
                    // The enclosing check will validate the resulting lambda.
                }
                let body = match expected {
                    Some(expected) => self.elab_with_expected(body, expected, handler)?,
                    None => self.elab_exp_rec(body, handler)?,
                };
                Ok(crate::raw::utils::assoc_lam(
                    handler.arena(),
                    telescope,
                    body,
                ))
            })();
            self.bindings.truncate(bindings_mark);
            self.typing_binds.truncate(context_mark);
            return result;
        }
        match exp {
            SExp::Checked { .. } | SExp::Where { .. } | SExp::Block(_) => {
                self.elab_exp_inner(exp, Some(expected), handler)
            }
            _ => self.elab_exp_rec(exp, handler),
        }
    }
    pub(crate) fn context(&self) -> &ExpContext {
        &self.typing_binds
    }

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
    ) -> Result<Vec<(SymbolId, Exp)>, ElaborationError> {
        let mut result = vec![];
        for RightBind { vars, ty } in binds.iter() {
            let ty_elab = self.elab_exp(ty, handler)?;
            handler.infer(&mut self.typing_binds, ty_elab)?;
            for (depth, var) in vars.iter().enumerate() {
                let var = handler.intern_name(var);
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
    ) -> Result<Exp, ElaborationError> {
        handler.infer(&mut self.typing_binds, exp)
    }

    fn get_var(&self, arena: &Arena, name: &Identifier, handler: &impl Handler) -> Option<Exp> {
        let binding = self
            .bindings
            .iter()
            .rev()
            .find(|binding| handler.env().name_matches(binding.var, name))?;
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
    ) -> Result<Vec<Exp>, ElaborationError> {
        if parameters.is_empty() && expected > 0 {
            return (0..expected)
                .map(|_| {
                    handler.fresh_meta(
                        SurfaceMeta::Implicit,
                        SourceSpan { start: 0, end: 0 },
                        &self.typing_binds,
                    )
                })
                .collect();
        }
        if parameters.len() != expected {
            return Err(format!(
                "associated item expects {expected} type parameter(s), found {}",
                parameters.len()
            )
            .into());
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
    ) -> Result<Vec<Exp>, ElaborationError> {
        Self::ordered_inductive_cases(constructors, cases, |case| &case.0)?
            .into_iter()
            .map(|case| self.elab_exp_rec(&case.1, handler))
            .collect()
    }

    fn ordered_inductive_cases<'a, T>(
        constructors: &[Identifier],
        cases: &'a [T],
        name: impl Fn(&T) -> &Identifier,
    ) -> Result<Vec<&'a T>, ElaborationError> {
        if cases.len() != constructors.len() {
            return Err(format!(
                "Expected {} inductive branches, found {}",
                constructors.len(),
                cases.len()
            )
            .into());
        }
        let mut ordered = vec![None; constructors.len()];
        for case in cases {
            let name = name(case);
            let Some(index) = constructors
                .iter()
                .position(|constructor| constructor.as_str() == name.as_str())
            else {
                return Err(format!("Unknown inductive constructor {}", name.as_str()).into());
            };
            if ordered[index].replace(case).is_some() {
                return Err(format!(
                    "Duplicate inductive branch for constructor {}",
                    name.as_str()
                )
                .into());
            }
        }
        ordered
            .into_iter()
            .zip(constructors)
            .map(|(case, constructor)| {
                case.ok_or_else(|| {
                    format!(
                        "Missing inductive branch for constructor {}",
                        constructor.as_str()
                    )
                    .into()
                })
            })
            .collect()
    }

    fn elab_nonrecursive_case(
        &mut self,
        constructor: &Identifier,
        binders: &[Identifier],
        body: &SExp,
        expected_type: Exp,
        field_count: usize,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        if binders.len() != field_count {
            return Err(format!(
                "Branch {} expects {field_count} field binder(s), found {}",
                constructor.as_str(),
                binders.len()
            )
            .into());
        }
        let bindings_mark = self.bindings.len();
        let context_mark = self.typing_binds.len();
        let result = (|| {
            let mut expected_type = expected_type;
            let mut typed_binders = Vec::new();
            for binder in binders {
                let ExpNode::Prod { ty, body, .. } = handler.arena().get(expected_type) else {
                    return Err(format!(
                        "Too many field binders in branch {}",
                        constructor.as_str()
                    )
                    .into());
                };
                let var = handler.intern_name(binder);
                typed_binders.push((var, ty));
                self.push_binded_var(var, ty);
                expected_type = body;
            }
            let body = self.elab_exp_rec(body, handler)?;
            Ok(crate::raw::utils::assoc_lam(
                handler.arena(),
                typed_binders,
                body,
            ))
        })();
        self.bindings.truncate(bindings_mark);
        self.typing_binds.truncate(context_mark);
        result
    }

    fn pop_binded_var(&mut self) {
        self.bindings.pop();
        self.typing_binds.pop();
    }

    pub(crate) fn elab_exp(
        &mut self,
        exp: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
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
    ) -> Result<(Exp, Exp, Exp), ElaborationError> {
        match bind {
            Bind::Named(right_bind) => {
                if right_bind.vars.len() != 1 {
                    return Err("\\take currently expects exactly one named variable".into());
                }

                let var = handler.intern_name(&right_bind.vars[0]);
                let domain = self.elab_exp_rec(&right_bind.ty, handler)?;
                self.elab_take_map(var, domain, body, handler)
            }
            Bind::Subset { var, ty, predicate } => {
                let carrier = self.elab_exp_rec(ty, handler)?;
                let var = handler.intern_name(var);
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
                self.elab_take_map(var, domain, body, handler)
            }
            Bind::SubsetWithProof { .. } => {
                Err("\\take with proof bind is not supported by kernel TakeProp(X,P,f)".into())
            }
        }
    }

    fn elab_take_map(
        &mut self,
        var: SymbolId,
        domain: Exp,
        body: &SExp,
        handler: &mut impl Handler,
    ) -> Result<(Exp, Exp, Exp), ElaborationError> {
        let map = self.elab_take_function(var, domain, body, handler)?;
        let map_ty = handler.infer(&mut self.typing_binds, map)?;
        let map_ty = whnf(handler.env(), handler.zonk(map_ty));
        let ExpNode::Prod { body: codomain, .. } = handler.arena().get(map_ty) else {
            return Err("failed to infer a product type for \\take map".into());
        };
        let codomain = whnf(handler.env(), handler.zonk(codomain));
        if exp_contains_bound(handler.arena(), codomain, 0) {
            return Err("\\take map must have a non-dependent codomain".into());
        }
        let codomain = instantiate(handler.arena(), codomain, domain);
        Ok((domain, map, codomain))
    }

    fn elab_take_function(
        &mut self,
        var: SymbolId,
        domain: Exp,
        body: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        self.push_binded_var(var, domain);
        let map_body = self.elab_exp_rec(body, handler);
        self.pop_binded_var();
        Ok(handler.arena().alloc(ExpNode::Lam {
            var,
            ty: domain,
            body: map_body?,
        }))
    }

    fn elab_exp_rec(
        &mut self,
        exp: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        let result = self.elab_exp_inner(exp, None, handler)?;
        let span = match exp {
            SExp::AccessPath { access, .. } => Some(access.span()),
            SExp::Meta { span, .. } | SExp::Assign { span, .. } => Some(*span),
            _ => None,
        };
        if let Some(span) = span {
            handler.record_source(result, span);
        }
        Ok(result)
    }

    fn elab_exp_inner(
        &mut self,
        exp: &SExp,
        expected: Option<Exp>,
        handler: &mut impl Handler,
    ) -> Result<Exp, ElaborationError> {
        match exp {
            SExp::Checked { checks, body } => {
                let mut direct_head = body.as_ref();
                let mut direct_arguments = Vec::new();
                while let SExp::App { func, arg } = direct_head {
                    direct_arguments.push(arg.as_ref());
                    direct_head = func.as_ref();
                }
                if let [(SExp::ModuleInstance { path, import_name }, _)] = checks.as_slice()
                    && let SExp::AccessPath { access, parameters } = direct_head
                {
                    let arguments = parameters
                        .iter()
                        .chain(direct_arguments.into_iter().rev())
                        .collect::<Vec<_>>();
                    if let Some(value) = handler.direct_module_definition(
                        path,
                        import_name,
                        access,
                        self,
                        &arguments,
                    )? {
                        return Ok(value);
                    }
                }
                for (value, ty) in checks {
                    if let SExp::ModuleInstance { path, import_name } = value {
                        handler.instantiate_module(path, import_name, self)?;
                    } else if let SExp::ConversionTarget { expression } = ty {
                        if let (Ok(left), Ok(right)) = (
                            self.elab_exp_rec(value, handler),
                            self.elab_exp_rec(expression, handler),
                        ) {
                            handler.infer(&mut self.typing_binds, left)?;
                            handler.infer(&mut self.typing_binds, right)?;
                            handler.unify(&self.typing_binds, left, right)?;
                        } else {
                            handler.check_program_member(value, ty)?;
                        }
                    } else if matches!(ty, SExp::ValueType) {
                        handler.check_program_member(value, ty)?;
                    } else if let Ok(expected) = self.elab_exp_rec(ty, handler) {
                        let value = self.elab_with_expected(value, expected, handler)?;
                        handler.check(&mut self.typing_binds, value, expected)?;
                    } else {
                        handler.check_program_member(value, ty)?;
                    }
                }
                let value = match expected {
                    Some(expected) => self.elab_with_expected(body, expected, handler),
                    None => self.elab_exp_rec(body, handler),
                }?;
                if checks
                    .iter()
                    .any(|(value, _)| matches!(value, SExp::ModuleInstance { .. }))
                {
                    handler.materialize_module_term(&self.typing_binds, value)
                } else {
                    Ok(value)
                }
            }
            SExp::ModuleInstance { .. }
            | SExp::ConversionTarget { .. }
            | SExp::ProgramValueReference { .. } => Err("Program value requires reflection".into()),
            SExp::MemberAccess { .. } | SExp::MemberLiteral { .. } => {
                Err("unresolved structure member".into())
            }
            SExp::Ascribe { term, ty } => {
                let ty = self.elab_exp_rec(ty, handler)?;
                let term = self.elab_with_expected(term, ty, handler)?;
                Ok(handler.arena().alloc(ExpNode::Ascribe { term, ty }))
            }
            SExp::ReflectTerm { expression } => {
                if let SExp::AccessPath {
                    access: LocalAccess::Current { access, .. },
                    parameters,
                } = expression.as_ref()
                    && parameters.is_empty()
                    && let Some(var) = self.get_var(handler.arena(), access, handler)
                {
                    return Ok(var);
                }
                handler.reflect_front_expression(expression)
            }
            SExp::Reflect {
                parameter,
                expression,
            } => handler.reflect_program_expression(*parameter, expression),
            SExp::Meta { kind, span } => handler.fresh_meta(*kind, *span, &self.typing_binds),
            SExp::Assign {
                value,
                number,
                span,
            } => {
                let value = self.elab_exp_rec(value, handler)?;
                let meta =
                    handler.fresh_meta(SurfaceMeta::Named(*number), *span, &self.typing_binds)?;
                handler.assign_meta(meta, value)?;
                Ok(value)
            }
            SExp::AccessPath { access, parameters } => {
                // this includes (term binding) access path

                // 1. find from binded vars first (if no parameters)
                if let LocalAccess::Current { access: name, .. }
                | LocalAccess::Resolved { access: name, .. } = access
                    && let Some(var) = self.get_var(handler.arena(), name, handler)
                    && parameters.is_empty()
                {
                    return Ok(var);
                }

                // 2. others via handler
                let item = handler.get_item_from_access_path(access)?;
                match item {
                    ItemAccessResult::Definition(ModItemDefinition { definition, .. }) => {
                        if matches!(
                            handler.env().resolve_definition(definition)?,
                            DefinedConstant::Contextual { .. }
                        ) {
                            let arguments = parameters
                                .iter()
                                .map(|expression| self.elab_exp_rec(expression, handler))
                                .collect::<Result<Vec<_>, _>>()?;
                            return self.definition_reference(definition, arguments, handler);
                        }
                        if !matches!(
                            handler.env().definition(definition),
                            DefinedConstant::Pts { .. }
                        ) {
                            return Err(format!(
                                "Program definitions require explicit Set reflection (^): '{access}'"
                            ).into());
                        }
                        let mut value = handler.arena().alloc(ExpNode::DefinedConstant(definition));
                        for parameter in parameters {
                            let arg = self.elab_exp_rec(parameter, handler)?;
                            let ty = handler.infer(&mut self.typing_binds, value)?;
                            let ty = whnf(handler.env(), handler.zonk(ty));
                            if let ExpNode::Prod { ty: domain, .. } = handler.arena().get(ty) {
                                handler.check(&mut self.typing_binds, arg, domain)?;
                            }
                            value = handler.arena().alloc(ExpNode::App { func: value, arg });
                        }
                        Ok(value)
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
                                Ok(crate::raw::reflection::reflect_value(handler.env(), *body)
                                    .map_err(|e| e.to_string())?)
                            }
                            DefinedConstant::ProgramComputation { body, .. } => Ok(
                                crate::raw::reflection::reflect_computation(handler.env(), *body)
                                    .map_err(|e| e.to_string())?,
                            ),
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
                            Err(ElaborationError::Message(
                                "Module parameter cannot be applied with parameters".to_string(),
                            ))
                        }
                    }
                    ItemAccessResult::ProgramInductive(_)
                    | ItemAccessResult::ProgramTypeParameter(_)
                    | ItemAccessResult::ProgramValueParameter(_)
                    | ItemAccessResult::Argument(_) => Err(format!(
                        "Program names require explicit Set reflection (^): '{access}'"
                    )
                    .into()),
                }
            }
            // this includes accessing constructor of the inductive type, accessing field of record type
            // `List[Nat]#nil` or `some_group#unit`
            SExp::AssociatedAccess { base, field, span } => {
                // 1. if base is local access, try to get constructor (parameter is allowed)
                if let SExp::AccessPath { access, parameters } = base.as_ref() {
                    let item = handler.get_item_from_access_path(access)?;
                    handler.associated_reference(access, field, *span);
                    if let Some(field) = field.as_str().strip_suffix('^') {
                        let ItemAccessResult::ProgramInductive(item) = item else {
                            return Err(format!(
                                "reflection of associated item '{field}' requires a Program datatype"
                            ).into());
                        };
                        let count = handler
                            .env()
                            .program_inductive(item.inductive)
                            .parameters()
                            .len();
                        let reflected_parameters = handler
                            .elaborate_program_type_arguments(parameters, count)?
                            .into_iter()
                            .map(|parameter| {
                                crate::raw::reflection::reflect_value_type(handler.env(), parameter)
                                    .map_err(|error| error.to_string())
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if field == "#" {
                            if item.record_fields.is_none() {
                                return Err("::#^ requires a Program record".into());
                            }
                            return Ok(handler.arena().alloc(ExpNode::IndCtor {
                                indspec: item.reflected,
                                parameters: reflected_parameters,
                                idx: 0,
                            }));
                        }
                        let (_, definition) = item
                            .associated_definitions
                            .iter()
                            .find(|(candidate, _)| candidate.as_str() == field)
                            .ok_or_else(|| {
                                format!("Program associated item {} was not found", field)
                            })?;
                        let reflected = match handler.env().definition(*definition) {
                            DefinedConstant::ProgramValue { body, .. } => {
                                crate::raw::reflection::reflect_value(handler.env(), *body)
                            }
                            DefinedConstant::ProgramComputation { body, .. } => {
                                crate::raw::reflection::reflect_computation(handler.env(), *body)
                            }
                            DefinedConstant::Pts { .. } | DefinedConstant::Contextual { .. } => {
                                return Err("associated item is not a Program definition".into());
                            }
                        };
                        let reflected = reflected.map_err(|error| error.to_string())?;
                        return Ok(crate::raw::calculus::instantiate_telescope(
                            handler.arena(),
                            reflected,
                            &reflected_parameters,
                        ));
                    }
                    let (item, parameters) = match item {
                        ItemAccessResult::Inductive(ref item) => {
                            let count = handler.env().inductive(item.inductive).parameters().len();
                            let parameters =
                                self.associated_parameters(parameters, count, handler)?;
                            (ItemAccessResult::Inductive(item.clone()), parameters)
                        }
                        ItemAccessResult::Record(ref record) => {
                            let count =
                                handler.env().inductive(record.inductive).parameters().len();
                            let parameters =
                                self.associated_parameters(parameters, count, handler)?;
                            (ItemAccessResult::Record(record.clone()), parameters)
                        }
                        _ => {
                            let ty = self.elab_exp_rec(base, handler)?;
                            handler.infer(&mut self.typing_binds, ty)?;
                            let ty = whnf(handler.env(), handler.zonk(ty));
                            let ExpNode::IndType {
                                indspec,
                                parameters,
                            } = handler.arena().get(ty)
                            else {
                                return Err(
                                    "Expected inductive type in base of associated access".into()
                                );
                            };
                            (Self::inductive_item(indspec, handler)?, parameters)
                        }
                    };
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
                                return self.definition_reference(*definition, parameters, handler);
                            }
                            Err(format!(
                                "Associated item {} not found in inductive type {}",
                                field.as_str(),
                                type_name.as_str()
                            ).into())
                        }
                        ItemAccessResult::Record(record) => {
                            if field.as_str() == "#" {
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
                                return self.definition_reference(*definition, parameters, handler);
                            }
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
                            )? else {
                                return Err(format!(
                                    "Associated item {} not found in structure {}",
                                    field.as_str(),
                                    record.type_name.as_str()
                                ).into());
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
                        ).into()),
                    }
                } else {
                    // 2. otherwise, elab base first, then project field
                    let base_elab = self.elab_exp_rec(base, handler)?;
                    handler
                        .field_projection(&mut self.typing_binds, base_elab, field)
                        .inspect_err(|_| handler.locate_error(*span))
                }
            }
            SExp::InferredProjection { value, field, span } => {
                let value = self.elab_exp_rec(value, handler)?;
                handler
                    .field_projection(&mut self.typing_binds, value, field)
                    .inspect_err(|_| handler.locate_error(*span))
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
                Err("unexpanded macro in HIR".into())
            }
            SExp::TokenMatch { .. } => Err("Token match escaped template expansion".into()),
            SExp::MacroParameter(name) => Err(format!(
                "Macro capture '${}' escaped template expansion",
                name.as_str()
            )
            .into()),
            SExp::Where { exp, clauses, span } => {
                let declaration_mark = self.bindings.len();
                let depth = self.typing_binds.len();
                let result = (|| {
                    for (name, ty, body) in clauses {
                        let value = (|| {
                            let ty = self.elab_exp_rec(ty, handler)?;
                            let body = self.elab_with_expected(body, ty, handler)?;
                            let value = handler.arena().alloc(ExpNode::Ascribe { term: body, ty });
                            // Check even unused definitions, before publishing their
                            // names. This also records constraints for implicit types.
                            let _profile_timer =
                                ProfileTimer::start("REF_TYPE_PROFILE_LOCAL_DEFINITIONS", || {
                                    format!("local definition {}", name.as_str())
                                });
                            handler
                                .infer(&mut self.typing_binds, value)
                                .map_err(|error| {
                                    format!("Local definition '{}': {error}", name.as_str())
                                })?;
                            Ok::<_, ElaborationError>(value)
                        })()
                        .inspect_err(|_| {
                            if let Some(span) = span {
                                handler.locate_error(*span);
                            }
                        })?;
                        let name = handler.intern_name(name);
                        self.push_decl_var_exp(name, value);
                    }
                    match expected {
                        Some(expected) => self.elab_with_expected(exp, expected, handler),
                        None => self.elab_exp_rec(exp, handler),
                    }
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
                            let var = handler.intern_name(var);
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
                        let var = handler.intern_name(var);
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
                        let var = handler.intern_name(var);
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
                        let proof = handler.intern_name(proof_var);
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
                if let SExp::AccessPath { access, parameters } = head
                    && let Ok(ItemAccessResult::Definition(item)) =
                        handler.get_item_from_access_path(access)
                    && let DefinedConstant::Contextual {
                        parameters: telescope,
                        ..
                    } = handler.env().resolve_definition(item.definition)?.clone()
                {
                    let count = telescope
                        .len()
                        .saturating_sub(parameters.len())
                        .min(arguments.len());
                    let mut supplied = parameters.clone();
                    supplied.extend(arguments.iter().take(count).map(|e| (*e).clone()));
                    let mut value = self.elab_exp_rec(
                        &SExp::AccessPath {
                            access: access.clone(),
                            parameters: supplied,
                        },
                        handler,
                    )?;
                    for argument in arguments.iter().skip(count) {
                        let arg = self.elab_exp_rec(argument, handler)?;
                        value = handler.arena().alloc(ExpNode::App { func: value, arg });
                    }
                    return Ok(value);
                }
                if let SExp::AssociatedAccess { base, field, .. } = head
                    && let SExp::AccessPath { access, parameters } = base.as_ref()
                    && let Ok(item) = handler.get_item_from_access_path(access)
                {
                    let (inductive, members) = match item {
                        ItemAccessResult::Inductive(item) => {
                            (Some(item.inductive), item.associated_definitions)
                        }
                        ItemAccessResult::Record(item) => {
                            (Some(item.inductive), item.associated_definitions)
                        }
                        _ => (None, Vec::new()),
                    };
                    if let Some(inductive) = inductive
                        && let Some((_, definition)) =
                            members.iter().find(|(name, _)| name == field)
                        && let DefinedConstant::Contextual {
                            parameters: telescope,
                            ..
                        } = handler.env().resolve_definition(*definition)?.clone()
                    {
                        let owner_count = handler.env().inductive(inductive).parameters().len();
                        let mut supplied =
                            self.associated_parameters(parameters, owner_count, handler)?;
                        let count = telescope
                            .len()
                            .saturating_sub(owner_count)
                            .min(arguments.len());
                        for argument in arguments.iter().take(count) {
                            supplied.push(self.elab_exp_rec(argument, handler)?);
                        }
                        let mut value =
                            self.definition_reference(*definition, supplied, handler)?;
                        for argument in arguments.iter().skip(count) {
                            let arg = self.elab_exp_rec(argument, handler)?;
                            value = handler.arena().alloc(ExpNode::App { func: value, arg });
                        }
                        return Ok(value);
                    }
                }
                if arguments.len() == 1
                    && let SExp::AssociatedAccess {
                        base,
                        field,
                        span: _,
                    } = head
                    && let SExp::AccessPath { access, parameters } = base.as_ref()
                    && parameters.is_empty()
                {
                    let item = handler.get_item_from_access_path(access)?;
                    match item {
                        ItemAccessResult::Record(record)
                            if !record
                                .associated_definitions
                                .iter()
                                .any(|(name, _)| name.as_str() == field.as_str()) =>
                        {
                            let value = self.elab_exp_rec(arguments[0], handler)?;
                            let value_ty = handler.infer(&mut self.typing_binds, value)?;
                            if let ExpNode::IndType {
                                indspec,
                                parameters,
                            } = handler.arena().get(value_ty)
                                && indspec == record.inductive
                            {
                                return Ok(record
                                    .field_projection(handler.env(), value, field, &parameters)?
                                    .ok_or_else(|| {
                                        format!(
                                            "Associated item {} not found in structure {}",
                                            field.as_str(),
                                            record.type_name.as_str()
                                        )
                                    })?);
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
                let subset_elab = self.elab_subset(subset, handler)?;
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
                        )
                        .into());
                    }
                };

                let scrutinee = self.elab_exp_rec(scrutinee, handler)?;
                let parameters =
                    handler.match_parameters(&mut self.typing_binds, scrutinee, inductive)?;
                let mut return_type_elab = self.elab_exp_rec(return_type, handler)?;
                // Motive lambdas are checked by the eliminator itself: their
                // function type need not have an ordinary product formation rule.
                let explicit_motive = matches!(
                    handler
                        .arena()
                        .get(whnf(handler.env(), handler.zonk(return_type_elab))),
                    ExpNode::Lam { .. }
                );
                let constant_motive = if explicit_motive {
                    false
                } else {
                    let ty = handler.infer(&mut self.typing_binds, return_type_elab)?;
                    matches!(
                        handler
                            .arena()
                            .get(type_head_normal(handler.env(), handler.zonk(ty))),
                        ExpNode::Sort(_)
                    )
                };
                if constant_motive {
                    // A result type denotes a constant motive; explicit motive
                    // functions retain their index and scrutinee dependencies.
                    let arena = handler.arena();
                    let arity = handler.env().inductive(inductive).arity(arena);
                    let mut arity = instantiate_telescope(arena, arity, &parameters);
                    let mut telescope = Vec::new();
                    while let ExpNode::Prod { var, ty, body } =
                        arena.get(type_head_normal(handler.env(), arity))
                    {
                        telescope.push((var, ty));
                        arity = body;
                    }
                    let depth = telescope.len();
                    let instance = arena.alloc(ExpNode::IndType {
                        indspec: inductive,
                        parameters: parameters
                            .iter()
                            .map(|&parameter| shift_bound_indices(arena, parameter, depth, 0))
                            .collect(),
                    });
                    let instance = crate::raw::utils::assoc_apply(
                        arena,
                        instance,
                        (0..depth)
                            .rev()
                            .map(|index| arena.exp_bound(index))
                            .collect(),
                    );
                    telescope.push((SymbolId::ANONYMOUS, instance));
                    return_type_elab = crate::raw::utils::assoc_lam(
                        arena,
                        telescope,
                        shift_bound_indices(arena, return_type_elab, depth + 1, 0),
                    );
                }
                let ordered = Self::ordered_inductive_cases(&ctor_names, branches, |case| &case.0)?;
                let this = handler.arena().alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameters.clone(),
                });
                let mut elaborated = Vec::with_capacity(ordered.len());
                for (index, (constructor_name, binders, body)) in ordered.into_iter().enumerate() {
                    let constructor = handler.env().inductive(inductive).constructors()[index]
                        .instantiate_parameters(handler.arena(), &parameters);
                    let constructor_term = handler.arena().alloc(ExpNode::IndCtor {
                        indspec: inductive,
                        parameters: parameters.clone(),
                        idx: index,
                    });
                    let expected_type = crate::raw::inductive::case_type(
                        handler.arena(),
                        &constructor,
                        return_type_elab,
                        constructor_term,
                        this,
                    );
                    elaborated.push(self.elab_nonrecursive_case(
                        constructor_name,
                        binders,
                        body,
                        expected_type,
                        constructor.telescope.len(),
                        handler,
                    )?);
                }

                Ok(handler.arena().alloc(ExpNode::IndCase {
                    indspec: inductive,
                    scrutinee,
                    return_type: return_type_elab,
                    branches: elaborated,
                }))
            }
            SExp::Induction {
                binders,
                return_type,
                cases,
            } => {
                let bindings_mark = self.bindings.len();
                let context_mark = self.typing_binds.len();
                let motive = (|| {
                    let mut telescope = Vec::new();
                    for binder in binders {
                        let domain = self.elab_exp_rec(&binder.ty, handler)?;
                        for (depth, name) in binder.vars.iter().enumerate() {
                            let var = handler.intern_name(name);
                            let domain = shift_bound_indices(handler.arena(), domain, depth, 0);
                            telescope.push((var, domain));
                            self.push_binded_var(var, domain);
                        }
                    }
                    Ok::<_, ElaborationError>((telescope, self.elab_exp_rec(return_type, handler)?))
                })();
                self.bindings.truncate(bindings_mark);
                self.typing_binds.truncate(context_mark);
                let (telescope, motive_body) = motive?;
                let (_, domain) = telescope.last().ok_or("expected induction binders")?;
                let domain = whnf(handler.env(), handler.zonk(*domain));
                let (head, _) = crate::raw::utils::decompose_app(handler.arena(), domain);
                let ExpNode::IndType {
                    indspec: inductive, ..
                } = handler.arena().get(head)
                else {
                    return Err("Induction binder type must reduce to an inductive type".into());
                };
                let ctor_names = match Self::inductive_item(inductive, handler)? {
                    ItemAccessResult::Inductive(ModItemInductive { ctor_names, .. }) => ctor_names,
                    ItemAccessResult::Record(_) => vec![Identifier("#".to_owned())],
                    _ => {
                        return Err("Induction binder type must reduce to an inductive type".into());
                    }
                };
                let cases = self.elab_inductive_cases(&ctor_names, cases, handler)?;
                let arena = handler.arena();
                let depth = telescope.len();
                let body = arena.alloc(ExpNode::IndElim {
                    indspec: inductive,
                    elim: arena.exp_bound(0),
                    motive_bindings: telescope
                        .iter()
                        .enumerate()
                        .map(|(i, &(var, domain))| {
                            (var, shift_bound_indices(arena, domain, depth, i))
                        })
                        .collect(),
                    return_type: shift_bound_indices(arena, motive_body, depth, depth),
                    cases: cases
                        .into_iter()
                        .map(|case| shift_bound_indices(arena, case, depth, 0))
                        .collect(),
                });
                Ok(crate::raw::utils::assoc_lam(arena, telescope, body))
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
            SExp::SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => {
                let state_ty = self.elab_exp_rec(state_ty, handler)?;
                let result_ty = self.elab_exp_rec(result_ty, handler)?;
                let motive = self.elab_exp_rec(motive, handler)?;
                let on_continue = self.elab_exp_rec(on_continue, handler)?;
                let on_finish = self.elab_exp_rec(on_finish, handler)?;
                Ok(handler.arena().alloc(ExpNode::SetStepMatch {
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
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
                let (program_ty, program) = handler.elaborate_boxed_program(program_ty, program)?;
                Ok(handler.arena().alloc(ExpNode::BoxProgram {
                    program_ty,
                    program,
                }))
            }
            SExp::ForceBox { program_ty, boxed } => {
                let boxed = self.elab_exp_rec(boxed, handler)?;
                let program_ty = if matches!(
                    program_ty.as_ref(),
                    SExp::Meta {
                        kind: SurfaceMeta::Implicit,
                        ..
                    }
                ) {
                    let boxed_ty = handler.infer(&mut self.typing_binds, boxed)?;
                    let boxed_ty = type_head_normal(handler.env(), boxed_ty);
                    let ExpNode::BoxType { program_ty } = handler.arena().get(boxed_ty) else {
                        return Err(
                            "cannot infer \\squash type: argument is not boxed Program code".into(),
                        );
                    };
                    program_ty
                } else {
                    handler.elaborate_boxed_computation_type(program_ty)?
                };
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

            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                let ty = self.elab_exp_rec(
                    &SExp::AccessPath {
                        access: access.clone(),
                        parameters: parameters.clone(),
                    },
                    handler,
                )?;
                self.elab_structure_literal(ty, fields, handler)
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
                let var = handler.intern_name(var);
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
                        return Err(ElaborationError::Message(
                            "Elaboration of multiple named binds in Exists is not implemented"
                                .to_string(),
                        ));
                    }
                    let ty_elab = self.elab_exp_rec(&rightbind.ty, handler)?;
                    Ok(handler.arena().alloc(ExpNode::Exists { set: ty_elab }))
                }
                Bind::SubsetWithProof { .. } => Err(ElaborationError::Message(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string(),
                )),
                Bind::Subset { var, ty, predicate } => {
                    let ty_elab = self.elab_exp_rec(ty, handler)?;
                    let var = handler.intern_name(var);
                    self.push_binded_var(var, ty_elab);
                    let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                    self.pop_binded_var();

                    let subset_as_exp = handler.arena().alloc(ExpNode::SubSet {
                        var,
                        set: ty_elab,
                        predicate: predicate_elab,
                    });
                    let set = handler.arena().alloc(ExpNode::TypeLift {
                        superset: ty_elab,
                        subset: subset_as_exp,
                    });
                    Ok(handler.arena().alloc(ExpNode::Exists { set }))
                }
            },
            SExp::Choice {
                set,
                existence,
                uniqueness,
            } => {
                let set = self.elab_exp_rec(set, handler)?;
                let existence = self.elab_exp_rec(existence, handler)?;
                let uniqueness = self.elab_exp_rec(uniqueness, handler)?;
                Ok(handler.arena().alloc(ExpNode::Choice {
                    set,
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
                let subset = self.elab_subset(subset, handler)?;
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
                let var = handler.intern_name(var);
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
            SExp::ChoiceEq {
                set,
                element,
                existence,
                uniqueness,
            } => {
                let set = self.elab_exp_rec(set, handler)?;
                let element = self.elab_exp_rec(element, handler)?;
                let existence = self.elab_exp_rec(existence, handler)?;
                let uniqueness = self.elab_exp_rec(uniqueness, handler)?;
                Ok(handler.arena().alloc(ExpNode::Prove(Prove::ChoiceEq {
                    set,
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
            | SExp::ProgramCase { .. }
            | SExp::ProgramStepMatch { .. } => {
                Err("Program syntax cannot be elaborated as a Set/Prop expression".into())
            }
            SExp::Block(block) => {
                let term = block.as_term()?;
                match expected {
                    Some(expected) => self.elab_with_expected(&term, expected, handler),
                    None => self.elab_exp_rec(&term, handler),
                }
            }
            SExp::Program(_) => {
                Err("Program block syntax cannot be elaborated as a Set/Prop expression".into())
            }
        }
    }
}
