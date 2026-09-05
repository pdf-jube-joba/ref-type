use crate::{
    elaborator::module_manager::ModuleManager,
    syntax::{Bind, Identifier, LocalAccess, MacroExp, MacroSeqAtom, SExp, Statement},
};
use kernel::{
    calculus::{exp_subst_map, remap_all_global_ids},
    environment::CrateEnv,
    exp::Exp,
    ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId},
};
use std::collections::{HashMap, HashSet};

pub const MAX_MACRO_EXPANSION_DEPTH: u16 = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroKind {
    Math,
    Named,
}

#[derive(Debug, Clone)]
pub struct MacroDefinition {
    pub name: Identifier,
    pub kind: MacroKind,
    pub pattern: Vec<MacroSeqAtom>,
    pub template: SExp,
    pub declaration_order: u64,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct ModuleMacroScope {
    pub declared: Vec<MacroDefinition>,
    pub used: Vec<MacroDefinition>,
}

pub(crate) struct MacroInstantiation<'a> {
    pub module_ids: &'a HashMap<ModuleId, ModuleId>,
    pub substitutions: &'a [(ModuleParamId, Exp)],
    pub definition_ids: &'a HashMap<DefId, DefId>,
    pub inductive_ids: &'a HashMap<InductiveId, InductiveId>,
    pub program_inductive_ids: &'a HashMap<ProgramInductiveId, ProgramInductiveId>,
}

fn pattern_captures(
    atoms: &[MacroSeqAtom],
    captures: &mut HashSet<String>,
    fixed: &mut usize,
) -> Result<(), String> {
    for atom in atoms {
        match atom {
            MacroSeqAtom::Capture(name) => {
                if !captures.insert(name.0.clone()) {
                    return Err(format!(
                        "Macro capture '${}' is declared more than once",
                        name.0
                    ));
                }
            }
            MacroSeqAtom::Tok(token) => {
                if matches!(
                    token.0.as_str(),
                    "->" | "=>" | ":=" | "|" | ":" | ";" | "." | "," | "=" | "!" | "::"
                ) {
                    return Err(format!(
                        "Macro token '{}' conflicts with reserved syntax",
                        token.0
                    ));
                }
                *fixed += 1;
            }
            MacroSeqAtom::Quoted(_) => *fixed += 1,
            MacroSeqAtom::Seq(inner) => pattern_captures(inner, captures, fixed)?,
        }
    }
    Ok(())
}

fn first_fixed_position(atoms: &[MacroSeqAtom]) -> usize {
    fn visit(atoms: &[MacroSeqAtom], position: &mut usize) -> Option<usize> {
        for atom in atoms {
            match atom {
                MacroSeqAtom::Capture(_) => *position += 1,
                MacroSeqAtom::Tok(_) | MacroSeqAtom::Quoted(_) => return Some(*position),
                MacroSeqAtom::Seq(inner) => {
                    if let Some(found) = visit(inner, position) {
                        return Some(found);
                    }
                }
            }
        }
        None
    }
    visit(atoms, &mut 0).unwrap_or(usize::MAX)
}

fn match_pattern(
    pattern: &[MacroSeqAtom],
    input: &[MacroExp],
    captures: &mut HashMap<String, SExp>,
) -> bool {
    if pattern.len() != input.len() {
        return false;
    }
    pattern
        .iter()
        .zip(input)
        .all(|(pattern, input)| match (pattern, input) {
            (MacroSeqAtom::Capture(name), MacroExp::Exp(exp)) => {
                captures.insert(name.0.clone(), exp.clone());
                true
            }
            (MacroSeqAtom::Tok(left), MacroExp::Tok(right)) => left == right,
            (MacroSeqAtom::Quoted(left), MacroExp::Quoted(right)) => left == right,
            (MacroSeqAtom::Seq(left), MacroExp::Seq(right)) => match_pattern(left, right, captures),
            _ => false,
        })
}

fn rename_template_binders(exp: &mut SExp, declaration_order: u64) {
    alpha_rename(exp, declaration_order, &mut 0, &mut Vec::new());
}

fn fresh_binder(
    identifier: &mut Identifier,
    declaration_order: u64,
    counter: &mut usize,
) -> (String, String) {
    let original = identifier.0.clone();
    let fresh = format!("<macro:{declaration_order}:{}>", *counter);
    *counter += 1;
    identifier.0.clone_from(&fresh);
    (original, fresh)
}

fn rename_access(access: &mut LocalAccess, scopes: &[HashMap<String, String>]) {
    let LocalAccess::Current { access } = access else {
        return;
    };
    if let Some(fresh) = scopes
        .iter()
        .rev()
        .find_map(|scope| scope.get(access.as_str()))
    {
        access.0.clone_from(fresh);
    }
}

fn alpha_macro_exps(
    tokens: &mut [MacroExp],
    order: u64,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, String>>,
) {
    for token in tokens {
        match token {
            MacroExp::Exp(exp) => alpha_rename(exp, order, counter, scopes),
            MacroExp::Seq(tokens) => alpha_macro_exps(tokens, order, counter, scopes),
            MacroExp::Tok(_) | MacroExp::Quoted(_) => {}
        }
    }
}

fn alpha_bind_type(
    bind: &mut Bind,
    order: u64,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, String>>,
) -> HashMap<String, String> {
    match bind {
        Bind::Named(bind) => {
            alpha_rename(&mut bind.ty, order, counter, scopes);
            bind.vars
                .iter_mut()
                .map(|var| fresh_binder(var, order, counter))
                .collect()
        }
        Bind::Subset { var, ty, predicate } => {
            alpha_rename(ty, order, counter, scopes);
            let binding = fresh_binder(var, order, counter);
            let scope = HashMap::from([binding.clone()]);
            scopes.push(scope.clone());
            alpha_rename(predicate, order, counter, scopes);
            scopes.pop();
            scope
        }
        Bind::SubsetWithProof {
            var,
            ty,
            predicate,
            proof_var,
        } => {
            alpha_rename(ty, order, counter, scopes);
            let value = fresh_binder(var, order, counter);
            let value_scope = HashMap::from([value.clone()]);
            scopes.push(value_scope);
            alpha_rename(predicate, order, counter, scopes);
            scopes.pop();
            let proof = fresh_binder(proof_var, order, counter);
            HashMap::from([value, proof])
        }
    }
}

fn alpha_many<const N: usize>(
    exps: [&mut Box<SExp>; N],
    order: u64,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, String>>,
) {
    for exp in exps {
        alpha_rename(exp, order, counter, scopes);
    }
}

fn alpha_rename(
    exp: &mut SExp,
    order: u64,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, String>>,
) {
    match exp {
        SExp::Meta { .. }
        | SExp::Sort(_)
        | SExp::ValueType
        | SExp::MacroParameter(_)
        | SExp::ResolvedExp(_) => {}
        SExp::AccessPath { access, parameters } => {
            rename_access(access, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
        }
        SExp::AssociatedAccess { base, .. }
        | SExp::ThunkType {
            computation_ty: base,
        }
        | SExp::ReturnType { value_ty: base }
        | SExp::Thunk { computation: base }
        | SExp::Return { value: base }
        | SExp::Force { value: base }
        | SExp::PowerSet { set: base }
        | SExp::RfType { compute_ty: base }
        | SExp::Proof { proposition: base }
        | SExp::BoxType { program_ty: base }
        | SExp::IdRefl { element: base } => alpha_rename(base, order, counter, scopes),
        SExp::MathMacro { tokens, .. } | SExp::NamedMacro { tokens, .. } => {
            alpha_macro_exps(tokens, order, counter, scopes)
        }
        SExp::Where { exp, clauses } => {
            let mut local = HashMap::new();
            for (name, ty, body) in clauses {
                alpha_rename(ty, order, counter, scopes);
                alpha_rename(body, order, counter, scopes);
                let binding = fresh_binder(name, order, counter);
                local.insert(binding.0, binding.1);
                scopes.push(local.clone());
            }
            alpha_rename(exp, order, counter, scopes);
            for _ in 0..local.len() {
                scopes.pop();
            }
        }
        SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
            let local = alpha_bind_type(bind, order, counter, scopes);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
        }
        SExp::App { func, arg, .. }
        | SExp::ComputationFunction {
            domain: func,
            codomain: arg,
        }
        | SExp::ComputationApp {
            computation: func,
            value: arg,
        }
        | SExp::Equal {
            left: func,
            right: arg,
        }
        | SExp::ExistsIntro {
            element: func,
            set: arg,
        }
        | SExp::BoxProgram {
            program_ty: func,
            program: arg,
        }
        | SExp::ForceBox {
            program_ty: func,
            boxed: arg,
        }
        | SExp::BoxApp {
            function: func,
            argument: arg,
        } => alpha_many([func, arg], order, counter, scopes),
        SExp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => alpha_many([superset, subset, element, proof], order, counter, scopes),
        SExp::IndElim {
            path,
            elim,
            return_type,
            cases,
        } => {
            rename_access(path, scopes);
            alpha_rename(elim, order, counter, scopes);
            alpha_rename(return_type, order, counter, scopes);
            for (_, case) in cases {
                alpha_rename(case, order, counter, scopes);
            }
        }
        SExp::IndElimPrim {
            path, parameters, ..
        } => {
            rename_access(path, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
        }
        SExp::ComputationLam {
            var,
            value_ty,
            body,
        } => {
            alpha_rename(value_ty, order, counter, scopes);
            let local = HashMap::from([fresh_binder(var, order, counter)]);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
        }
        SExp::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            alpha_rename(computation, order, counter, scopes);
            alpha_rename(value_ty, order, counter, scopes);
            let local = HashMap::from([fresh_binder(var, order, counter)]);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
        }
        SExp::ValueLet { var, value, body } => {
            alpha_rename(value, order, counter, scopes);
            let local = HashMap::from([fresh_binder(var, order, counter)]);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
        }
        SExp::ProgramCase {
            path,
            scrutinee,
            branches,
        } => {
            rename_access(path, scopes);
            alpha_rename(scrutinee, order, counter, scopes);
            for (_, binders, body) in branches {
                let local = binders
                    .iter_mut()
                    .map(|binder| fresh_binder(binder, order, counter))
                    .collect();
                scopes.push(local);
                alpha_rename(body, order, counter, scopes);
                scopes.pop();
            }
        }
        SExp::SubSet {
            var,
            set,
            predicate,
        } => {
            alpha_rename(set, order, counter, scopes);
            let local = HashMap::from([fresh_binder(var, order, counter)]);
            scopes.push(local);
            alpha_rename(predicate, order, counter, scopes);
            scopes.pop();
        }
        SExp::Exists { bind } => {
            alpha_bind_type(bind, order, counter, scopes);
        }
        SExp::TakeSet {
            bind,
            body,
            existence,
            uniqueness,
        } => {
            let local = alpha_bind_type(bind, order, counter, scopes);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
            alpha_rename(existence, order, counter, scopes);
            alpha_rename(uniqueness, order, counter, scopes);
        }
        SExp::TakeProp {
            bind,
            body,
            existence,
        } => {
            let local = alpha_bind_type(bind, order, counter, scopes);
            scopes.push(local);
            alpha_rename(body, order, counter, scopes);
            scopes.pop();
            alpha_rename(existence, order, counter, scopes);
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
            alpha_rename(left, order, counter, scopes);
            alpha_rename(right, order, counter, scopes);
            alpha_rename(ty, order, counter, scopes);
            let local = HashMap::from([fresh_binder(var, order, counter)]);
            scopes.push(local);
            alpha_rename(predicate, order, counter, scopes);
            scopes.pop();
            alpha_rename(base, order, counter, scopes);
            alpha_rename(equality, order, counter, scopes);
        }
        SExp::RecordTypeCtor {
            access,
            parameters,
            fields,
        } => {
            rename_access(access, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
            for (_, field) in fields {
                alpha_rename(field, order, counter, scopes);
            }
        }
        SExp::Block(block) => {
            let mut pushed = 0;
            for statement in &mut block.statements {
                match statement {
                    Statement::Fix(binds) => {
                        for bind in binds {
                            alpha_rename(&mut bind.ty, order, counter, scopes);
                            let local = bind
                                .vars
                                .iter_mut()
                                .map(|var| fresh_binder(var, order, counter))
                                .collect();
                            scopes.push(local);
                            pushed += 1;
                        }
                    }
                    Statement::Let { var, ty, body } => {
                        alpha_rename(ty, order, counter, scopes);
                        alpha_rename(body, order, counter, scopes);
                        scopes.push(HashMap::from([fresh_binder(var, order, counter)]));
                        pushed += 1;
                    }
                    Statement::TakeSet {
                        bind,
                        existence,
                        uniqueness,
                    } => {
                        let local = alpha_bind_type(bind, order, counter, scopes);
                        alpha_rename(existence, order, counter, scopes);
                        alpha_rename(uniqueness, order, counter, scopes);
                        scopes.push(local);
                        pushed += 1;
                    }
                    Statement::TakeProp {
                        bind, existence, ..
                    } => {
                        let local = alpha_bind_type(bind, order, counter, scopes);
                        alpha_rename(existence, order, counter, scopes);
                        scopes.push(local);
                        pushed += 1;
                    }
                    Statement::Sufficient { map, map_ty } => {
                        alpha_rename(map, order, counter, scopes);
                        alpha_rename(map_ty, order, counter, scopes);
                    }
                }
            }
            alpha_rename(&mut block.result, order, counter, scopes);
            for _ in 0..pushed {
                scopes.pop();
            }
        }
        SExp::RunStep {
            state_ty,
            result_ty,
        }
        | SExp::RfTerm {
            compute_ty: state_ty,
            term: result_ty,
        }
        | SExp::TypeLift {
            superset: state_ty,
            subset: result_ty,
        }
        | SExp::AxiomFunExt {
            left: state_ty,
            right: result_ty,
            pointwise: _,
        } => {
            alpha_rename(state_ty, order, counter, scopes);
            alpha_rename(result_ty, order, counter, scopes);
            if let SExp::AxiomFunExt { pointwise, .. } = exp {
                alpha_rename(pointwise, order, counter, scopes);
            }
        }
        SExp::Continue {
            state_ty,
            result_ty,
            next,
        }
        | SExp::Finish {
            state_ty,
            result_ty,
            output: next,
        }
        | SExp::Pred {
            superset: state_ty,
            subset: result_ty,
            element: next,
        }
        | SExp::SubsetElim {
            element: state_ty,
            subset: result_ty,
            superset: next,
        } => alpha_many([state_ty, result_ty, next], order, counter, scopes),
        SExp::Acc {
            state_ty,
            result_ty,
            step,
            state,
        }
        | SExp::AxiomSetExt {
            left: state_ty,
            right: result_ty,
            left_to_right: step,
            right_to_left: state,
        } => alpha_many([state_ty, result_ty, step, state], order, counter, scopes),
        SExp::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => alpha_many([state_ty, result_ty, step, initial], order, counter, scopes),
        SExp::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => alpha_many(
            [state_ty, result_ty, step, state, predecessors],
            order,
            counter,
            scopes,
        ),
        SExp::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => alpha_many(
            [state_ty, result_ty, step, initial, transition],
            order,
            counter,
            scopes,
        ),
        SExp::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => alpha_many(
            [
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            ],
            order,
            counter,
            scopes,
        ),
        SExp::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => alpha_many(
            [
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            ],
            order,
            counter,
            scopes,
        ),
        SExp::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => alpha_many([domain, family, inhabited], order, counter, scopes),
        SExp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => alpha_many(
            [func, domain, codomain, element, existence, uniqueness],
            order,
            counter,
            scopes,
        ),
    }
}

fn resolve_access(
    env: &CrateEnv,
    from: ModuleId,
    access: &LocalAccess,
) -> Result<(ModuleId, Identifier), String> {
    match access {
        LocalAccess::Resolved { module, access } => Ok((*module, access.clone())),
        LocalAccess::Named { access, child } => {
            let instance = env
                .module(from)
                .import(access.as_str())
                .ok_or_else(|| format!("Module import '{}' was not found", access.as_str()))?;
            let module = env.instance(instance).materialized;
            env.module(module).item(child.as_str()).ok_or_else(|| {
                format!(
                    "Item '{}.{}' was not found",
                    access.as_str(),
                    child.as_str()
                )
            })?;
            Ok((module, child.clone()))
        }
        LocalAccess::Current { access } => {
            let mut module = from;
            loop {
                if env.module(module).item(access.as_str()).is_some()
                    || env
                        .module(module)
                        .parameters()
                        .iter()
                        .any(|parameter| env.symbol(parameter.name) == access.as_str())
                {
                    return Ok((module, access.clone()));
                }
                module = env.module(module).parent().ok_or_else(|| {
                    format!(
                        "Free name '{}' in macro template was not found in its definition environment",
                        access.as_str()
                    )
                })?;
            }
        }
    }
}

fn prepare_template(
    mut template: SExp,
    env: &CrateEnv,
    module: ModuleId,
    captures: &HashSet<String>,
    declaration_order: u64,
) -> Result<SExp, String> {
    rename_template_binders(&mut template, declaration_order);
    let mut error = None;
    walk_sexp_mut(&mut template, &mut |node| {
        if error.is_some() {
            return;
        }
        match node {
            SExp::MacroParameter(name) if !captures.contains(name.as_str()) => {
                error = Some(format!(
                    "Macro template references undeclared capture '${}'",
                    name.as_str()
                ));
            }
            SExp::MathMacro {
                scope, max_order, ..
            }
            | SExp::NamedMacro {
                scope, max_order, ..
            } => {
                *scope = Some(module);
                *max_order = Some(declaration_order);
            }
            SExp::AccessPath { access, parameters } => {
                let LocalAccess::Current { access: name } = access else {
                    match resolve_access(env, module, access) {
                        Ok((resolved, name)) => {
                            *access = LocalAccess::Resolved {
                                module: resolved,
                                access: name,
                            };
                        }
                        Err(message) => error = Some(message),
                    }
                    return;
                };
                if name.as_str().starts_with("<macro:") {
                    return;
                }
                match resolve_access(env, module, access) {
                    Ok((resolved, name)) => {
                        if let Some((position, _)) = env
                            .module(resolved)
                            .parameters()
                            .iter()
                            .enumerate()
                            .find(|(_, parameter)| env.symbol(parameter.name) == name.as_str())
                        {
                            if !parameters.is_empty() {
                                error = Some(format!(
                                    "Module parameter '{}' cannot take module arguments",
                                    name.as_str()
                                ));
                                return;
                            }
                            *node = SExp::ResolvedExp(env.arena().module_param(ModuleParamId {
                                module: resolved,
                                position: position as u32,
                            }));
                        } else {
                            *access = LocalAccess::Resolved {
                                module: resolved,
                                access: name,
                            };
                        }
                    }
                    Err(message) => error = Some(message),
                }
            }
            SExp::IndElim { path, .. }
            | SExp::IndElimPrim { path, .. }
            | SExp::ProgramCase { path, .. }
            | SExp::RecordTypeCtor { access: path, .. } => {
                match resolve_access(env, module, path) {
                    Ok((resolved, name)) => {
                        *path = LocalAccess::Resolved {
                            module: resolved,
                            access: name,
                        };
                    }
                    Err(message) => error = Some(message),
                }
            }
            _ => {}
        }
    });
    error.map_or(Ok(template), Err)
}

impl ModuleManager {
    pub(crate) fn materialize_macros(
        &mut self,
        env: &CrateEnv,
        source: ModuleId,
        materialized: ModuleId,
        remapping: &MacroInstantiation<'_>,
    ) {
        let Some(source_scope) = self.macro_scopes.get(&source).cloned() else {
            return;
        };
        let remap = |mut definition: MacroDefinition| {
            walk_sexp_mut(&mut definition.template, &mut |node| match node {
                SExp::AccessPath {
                    access: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::IndElim {
                    path: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::IndElimPrim {
                    path: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::ProgramCase {
                    path: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::RecordTypeCtor {
                    access: LocalAccess::Resolved { module, .. },
                    ..
                } => {
                    if let Some(remapped) = remapping.module_ids.get(module) {
                        *module = *remapped;
                    }
                }
                SExp::MathMacro { scope, .. } | SExp::NamedMacro { scope, .. } => {
                    if let Some(module) = scope
                        && let Some(remapped) = remapping.module_ids.get(module)
                    {
                        *module = *remapped;
                    }
                }
                SExp::ResolvedExp(exp) => {
                    let substituted = exp_subst_map(env.arena(), *exp, remapping.substitutions);
                    *exp = remap_all_global_ids(
                        env.arena(),
                        substituted,
                        remapping.definition_ids,
                        remapping.inductive_ids,
                        remapping.program_inductive_ids,
                    );
                }
                _ => {}
            });
            definition
        };
        let declared = source_scope.declared.into_iter().map(&remap).collect();
        let used = source_scope.used.into_iter().map(remap).collect();
        self.macro_scopes
            .insert(materialized, ModuleMacroScope { declared, used });
    }

    pub fn register_macro(
        &mut self,
        env: &CrateEnv,
        name: Identifier,
        kind: MacroKind,
        pattern: Vec<MacroSeqAtom>,
        template: SExp,
    ) -> Result<(), String> {
        if self
            .visible_macros(env, self.current())
            .iter()
            .any(|definition| definition.name == name)
        {
            return Err(format!("Macro '{}' is already visible", name.as_str()));
        }
        let mut captures = HashSet::new();
        let mut fixed = 0;
        pattern_captures(&pattern, &mut captures, &mut fixed)?;
        if kind == MacroKind::Math && fixed == 0 {
            return Err(format!(
                "Math macro '{}' must contain at least one fixed token",
                name.as_str()
            ));
        }
        let order = self.next_macro_order;
        self.next_macro_order += 1;
        let mut template = prepare_template(template, env, self.current(), &captures, order)?;
        let visible_named = self
            .visible_macros(env, self.current())
            .into_iter()
            .filter(|definition| definition.kind == MacroKind::Named)
            .map(|definition| definition.name.0.clone())
            .collect::<HashSet<_>>();
        let mut nested_error = None;
        walk_sexp_mut(&mut template, &mut |node| {
            if let SExp::NamedMacro { name, .. } = node
                && !visible_named.contains(name.as_str())
            {
                nested_error = Some(format!(
                    "Named macro '{}' is not visible at template declaration",
                    name.as_str()
                ));
            }
        });
        if let Some(error) = nested_error {
            return Err(error);
        }
        let current = self.current();
        self.macro_scopes
            .entry(current)
            .or_default()
            .declared
            .push(MacroDefinition {
                name,
                kind,
                pattern,
                template,
                declaration_order: order,
            });
        Ok(())
    }

    pub fn use_macro(
        &mut self,
        env: &CrateEnv,
        import_name: &Identifier,
        macro_name: &Identifier,
    ) -> Result<(), String> {
        let instance = env
            .module(self.current())
            .import(import_name.as_str())
            .ok_or_else(|| format!("Module import '{}' was not found", import_name.as_str()))?;
        let materialized = env.instance(instance).materialized;
        let definition = self
            .macro_scopes
            .get(&materialized)
            .and_then(|macros| {
                macros
                    .declared
                    .iter()
                    .find(|definition| definition.name == *macro_name)
            })
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Macro '{}.{}' was not found",
                    import_name.as_str(),
                    macro_name.as_str()
                )
            })?;
        if self
            .visible_macros(env, self.current())
            .iter()
            .any(|visible| visible.name == definition.name)
        {
            return Err(format!(
                "Macro '{}' is already visible",
                macro_name.as_str()
            ));
        }
        self.macro_scopes
            .entry(self.current())
            .or_default()
            .used
            .push(definition);
        Ok(())
    }

    pub fn visible_macros<'a>(
        &'a self,
        env: &CrateEnv,
        module: ModuleId,
    ) -> Vec<&'a MacroDefinition> {
        let mut output = Vec::new();
        let mut current = Some(module);
        while let Some(module) = current {
            if let Some(macros) = self.macro_scopes.get(&module) {
                output.extend(&macros.declared);
                output.extend(&macros.used);
            }
            current = env.module(module).parent();
        }
        output
    }

    pub fn expand_math_macro(
        &self,
        env: &CrateEnv,
        module: ModuleId,
        tokens: &[MacroExp],
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        if depth >= MAX_MACRO_EXPANSION_DEPTH {
            return Err(format!(
                "Macro expansion exceeded depth {}",
                MAX_MACRO_EXPANSION_DEPTH
            ));
        }
        let tokens = tokens
            .iter()
            .map(|token| match token {
                MacroExp::Seq(inner) => self
                    .expand_math_macro(env, module, inner, depth + 1, max_order)
                    .map(MacroExp::Exp),
                other => Ok(other.clone()),
            })
            .collect::<Result<Vec<_>, String>>()?;
        if let [MacroExp::Exp(exp)] = tokens.as_slice() {
            return Ok(exp.clone());
        }
        let mut matches = self
            .visible_macros(env, module)
            .into_iter()
            .filter(|definition| max_order.is_none_or(|max| definition.declaration_order < max))
            .filter(|definition| definition.kind == MacroKind::Math)
            .filter_map(|definition| {
                let mut captures = HashMap::new();
                match_pattern(&definition.pattern, &tokens, &mut captures).then_some((
                    first_fixed_position(&definition.pattern),
                    definition.declaration_order,
                    definition,
                    captures,
                ))
            })
            .collect::<Vec<_>>();
        matches.sort_by_key(|(position, order, _, _)| (*position, *order));
        let Some((_, _, definition, captures)) = matches.into_iter().next() else {
            return Err("No visible math macro matches the complete token sequence".into());
        };
        instantiate_template(definition, &captures, depth)
    }

    pub fn expand_named_macro(
        &self,
        env: &CrateEnv,
        module: ModuleId,
        name: &Identifier,
        tokens: &[MacroExp],
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        if depth >= MAX_MACRO_EXPANSION_DEPTH {
            return Err(format!(
                "Macro expansion exceeded depth {} while expanding '{}'",
                MAX_MACRO_EXPANSION_DEPTH,
                name.as_str()
            ));
        }
        let definition = self
            .visible_macros(env, module)
            .into_iter()
            .filter(|definition| max_order.is_none_or(|max| definition.declaration_order < max))
            .find(|definition| definition.kind == MacroKind::Named && definition.name == *name)
            .ok_or_else(|| format!("Named macro '{}' is not visible", name.as_str()))?;
        let mut captures = HashMap::new();
        if !match_pattern(&definition.pattern, tokens, &mut captures) {
            return Err(format!(
                "Input does not match the complete pattern of macro '{}'",
                name.as_str()
            ));
        }
        instantiate_template(definition, &captures, depth)
    }
}

fn instantiate_template(
    definition: &MacroDefinition,
    captures: &HashMap<String, SExp>,
    depth: u16,
) -> Result<SExp, String> {
    let mut result = definition.template.clone();
    let mut error = None;
    walk_sexp_mut(&mut result, &mut |node| match node {
        SExp::MacroParameter(name) => match captures.get(name.as_str()) {
            Some(replacement) => *node = replacement.clone(),
            None => error = Some(format!("Capture '${}' has no matched value", name.as_str())),
        },
        SExp::MathMacro { depth: nested, .. } | SExp::NamedMacro { depth: nested, .. } => {
            *nested = depth + 1;
        }
        _ => {}
    });
    error.map_or(Ok(result), Err)
}

pub(crate) fn walk_sexp_mut(exp: &mut SExp, action: &mut impl FnMut(&mut SExp)) {
    action(exp);
    match exp {
        SExp::Meta { .. }
        | SExp::Sort(_)
        | SExp::ValueType
        | SExp::MacroParameter(_)
        | SExp::ResolvedExp(_) => {}
        SExp::AccessPath { parameters, .. } | SExp::IndElimPrim { parameters, .. } => {
            for parameter in parameters {
                walk_sexp_mut(parameter, action);
            }
        }
        SExp::AssociatedAccess { base, .. }
        | SExp::ThunkType {
            computation_ty: base,
        }
        | SExp::ReturnType { value_ty: base }
        | SExp::Thunk { computation: base }
        | SExp::Return { value: base }
        | SExp::Force { value: base }
        | SExp::PowerSet { set: base }
        | SExp::RfType { compute_ty: base }
        | SExp::Proof { proposition: base }
        | SExp::BoxType { program_ty: base }
        | SExp::IdRefl { element: base } => walk_sexp_mut(base, action),
        SExp::MathMacro { tokens, .. } | SExp::NamedMacro { tokens, .. } => {
            walk_macro_exps_mut(tokens, action);
        }
        SExp::Where { exp, clauses } => {
            walk_sexp_mut(exp, action);
            for (_, ty, body) in clauses {
                walk_sexp_mut(ty, action);
                walk_sexp_mut(body, action);
            }
        }
        SExp::Prod { bind, body }
        | SExp::Lam { bind, body }
        | SExp::TakeProp {
            bind,
            body,
            existence: _,
        } => {
            walk_bind_mut(bind, action);
            walk_sexp_mut(body, action);
            if let SExp::TakeProp { existence, .. } = exp {
                walk_sexp_mut(existence, action);
            }
        }
        SExp::Exists { bind } => walk_bind_mut(bind, action),
        SExp::App { func, arg, .. }
        | SExp::ComputationFunction {
            domain: func,
            codomain: arg,
        }
        | SExp::ComputationApp {
            computation: func,
            value: arg,
        }
        | SExp::ValueLet {
            value: func,
            body: arg,
            ..
        }
        | SExp::Equal {
            left: func,
            right: arg,
        }
        | SExp::ExistsIntro {
            element: func,
            set: arg,
        }
        | SExp::BoxProgram {
            program_ty: func,
            program: arg,
        }
        | SExp::ForceBox {
            program_ty: func,
            boxed: arg,
        }
        | SExp::BoxApp {
            function: func,
            argument: arg,
        } => {
            walk_sexp_mut(func, action);
            walk_sexp_mut(arg, action);
        }
        SExp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => walk_many_mut([superset, subset, element, proof], action),
        SExp::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            walk_sexp_mut(elim, action);
            walk_sexp_mut(return_type, action);
            for (_, case) in cases {
                walk_sexp_mut(case, action);
            }
        }
        SExp::ComputationLam { value_ty, body, .. } => {
            walk_sexp_mut(value_ty, action);
            walk_sexp_mut(body, action);
        }
        SExp::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => walk_many_mut([computation, value_ty, body], action),
        SExp::ProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            walk_sexp_mut(scrutinee, action);
            for (_, _, body) in branches {
                walk_sexp_mut(body, action);
            }
        }
        SExp::RunStep {
            state_ty,
            result_ty,
        }
        | SExp::Pred {
            superset: state_ty,
            subset: result_ty,
            element: _,
        }
        | SExp::TypeLift {
            superset: state_ty,
            subset: result_ty,
        }
        | SExp::SubsetElim {
            element: state_ty,
            subset: result_ty,
            superset: _,
        } => {
            walk_sexp_mut(state_ty, action);
            walk_sexp_mut(result_ty, action);
            match exp {
                SExp::Pred { element, .. } => walk_sexp_mut(element, action),
                SExp::SubsetElim { superset, .. } => walk_sexp_mut(superset, action),
                _ => {}
            }
        }
        SExp::Continue {
            state_ty,
            result_ty,
            next,
        }
        | SExp::Finish {
            state_ty,
            result_ty,
            output: next,
        } => walk_many_mut([state_ty, result_ty, next], action),
        SExp::RfTerm { compute_ty, term } => walk_many_mut([compute_ty, term], action),
        SExp::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => walk_many_mut([state_ty, result_ty, step, state], action),
        SExp::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => walk_many_mut([state_ty, result_ty, step, initial], action),
        SExp::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => walk_many_mut([state_ty, result_ty, step, initial, transition], action),
        SExp::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => walk_many_mut(
            [
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            ],
            action,
        ),
        SExp::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => walk_many_mut([state_ty, result_ty, step, state, predecessors], action),
        SExp::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => walk_many_mut(
            [
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            ],
            action,
        ),
        SExp::RecordTypeCtor {
            parameters, fields, ..
        } => {
            for parameter in parameters {
                walk_sexp_mut(parameter, action);
            }
            for (_, field) in fields {
                walk_sexp_mut(field, action);
            }
        }
        SExp::SubSet { set, predicate, .. } => {
            walk_sexp_mut(set, action);
            walk_sexp_mut(predicate, action);
        }
        SExp::TakeSet {
            bind,
            body,
            existence,
            uniqueness,
        } => {
            walk_bind_mut(bind, action);
            walk_many_mut([body, existence, uniqueness], action);
        }
        SExp::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => walk_many_mut([left, right, ty, predicate, base, equality], action),
        SExp::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => walk_many_mut([left, right, left_to_right, right_to_left], action),
        SExp::AxiomFunExt {
            left,
            right,
            pointwise,
        } => walk_many_mut([left, right, pointwise], action),
        SExp::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => walk_many_mut([domain, family, inhabited], action),
        SExp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => walk_many_mut(
            [func, domain, codomain, element, existence, uniqueness],
            action,
        ),
        SExp::Block(block) => {
            for statement in &mut block.statements {
                walk_statement_mut(statement, action);
            }
            walk_sexp_mut(&mut block.result, action);
        }
    }
}

fn walk_many_mut<const N: usize>(exps: [&mut Box<SExp>; N], action: &mut impl FnMut(&mut SExp)) {
    for exp in exps {
        walk_sexp_mut(exp, action);
    }
}

fn walk_macro_exps_mut(tokens: &mut [MacroExp], action: &mut impl FnMut(&mut SExp)) {
    for token in tokens {
        match token {
            MacroExp::Exp(exp) => walk_sexp_mut(exp, action),
            MacroExp::Seq(tokens) => walk_macro_exps_mut(tokens, action),
            MacroExp::Tok(_) | MacroExp::Quoted(_) => {}
        }
    }
}

fn walk_bind_mut(bind: &mut Bind, action: &mut impl FnMut(&mut SExp)) {
    match bind {
        Bind::Named(bind) => walk_sexp_mut(&mut bind.ty, action),
        Bind::Subset { ty, predicate, .. } | Bind::SubsetWithProof { ty, predicate, .. } => {
            walk_sexp_mut(ty, action);
            walk_sexp_mut(predicate, action);
        }
    }
}

fn walk_statement_mut(statement: &mut Statement, action: &mut impl FnMut(&mut SExp)) {
    match statement {
        Statement::Fix(binds) => {
            for bind in binds {
                walk_sexp_mut(&mut bind.ty, action);
            }
        }
        Statement::Let { ty, body, .. } => {
            walk_sexp_mut(ty, action);
            walk_sexp_mut(body, action);
        }
        Statement::TakeSet {
            bind,
            existence,
            uniqueness,
        } => {
            walk_bind_mut(bind, action);
            walk_sexp_mut(existence, action);
            walk_sexp_mut(uniqueness, action);
        }
        Statement::TakeProp {
            bind, existence, ..
        } => {
            walk_bind_mut(bind, action);
            walk_sexp_mut(existence, action);
        }
        Statement::Sufficient { map, map_ty } => {
            walk_sexp_mut(map, action);
            walk_sexp_mut(map_ty, action);
        }
    }
}
