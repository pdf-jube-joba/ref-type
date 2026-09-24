use crate::elaborator::module_manager::{ItemAccessResult, ModuleManager};
use elab::{
    calculus::{exp_subst_map, remap_all_global_ids},
    environment::CrateEnv,
    exp::Exp,
    ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId},
};
use hir::visit::{walk_sexp_control, walk_sexp_mut};
use hir::{
    Bind, Identifier, LocalAccess, MacroExp, MacroSeqAtom, SExp, Statement, TokenMatchPattern,
};
use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet},
    sync::atomic::{AtomicU64, Ordering},
};

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

#[derive(Debug, Clone)]
pub(crate) struct OwnedMacroInstantiation {
    module_ids: HashMap<ModuleId, ModuleId>,
    substitutions: Vec<(ModuleParamId, Exp)>,
    definition_ids: HashMap<DefId, DefId>,
    inductive_ids: HashMap<InductiveId, InductiveId>,
    program_inductive_ids: HashMap<ProgramInductiveId, ProgramInductiveId>,
}

impl From<&MacroInstantiation<'_>> for OwnedMacroInstantiation {
    fn from(value: &MacroInstantiation<'_>) -> Self {
        Self {
            module_ids: value.module_ids.clone(),
            substitutions: value.substitutions.to_vec(),
            definition_ids: value.definition_ids.clone(),
            inductive_ids: value.inductive_ids.clone(),
            program_inductive_ids: value.program_inductive_ids.clone(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct LazyModuleMacroScope {
    source: ModuleId,
    remapping: OwnedMacroInstantiation,
    materialized: OnceCell<ModuleMacroScope>,
}

impl ModuleManager {
    pub(crate) fn retained_raw_roots(&self) -> Vec<Exp> {
        let mut roots = Vec::new();
        let mut scopes = self.macro_scopes.values().collect::<Vec<_>>();
        for lazy in self.lazy_macro_scopes.values() {
            roots.extend(lazy.remapping.substitutions.iter().map(|(_, term)| *term));
            if let Some(scope) = lazy.materialized.get() {
                scopes.push(scope);
            }
        }
        for scope in scopes {
            for definition in scope.declared.iter().chain(&scope.used) {
                walk_sexp_control(&mut definition.template.clone(), &mut |node| {
                    if let SExp::Captured(id) = node {
                        roots.push(self.captured_expression(*id));
                    }
                    true
                });
            }
        }
        roots
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CaptureKind {
    Expression,
    Token,
    Sequence,
}

#[derive(Debug, Clone)]
enum CaptureValue {
    Expression(SExp),
    Token(MacroExp),
    Sequence(Vec<MacroExp>),
}

type CaptureKinds = HashMap<String, CaptureKind>;
type Captures = HashMap<String, CaptureValue>;

fn pattern_captures(
    atoms: &[MacroSeqAtom],
    captures: &mut CaptureKinds,
    fixed: &mut usize,
    kind: MacroKind,
) -> Result<(), String> {
    for (position, atom) in atoms.iter().enumerate() {
        match atom {
            MacroSeqAtom::Capture(name)
            | MacroSeqAtom::TokenCapture(name)
            | MacroSeqAtom::Rest(name) => {
                let capture_kind = match atom {
                    MacroSeqAtom::Capture(_) => CaptureKind::Expression,
                    MacroSeqAtom::TokenCapture(_) => CaptureKind::Token,
                    _ => CaptureKind::Sequence,
                };
                if kind == MacroKind::Math && capture_kind != CaptureKind::Expression {
                    return Err("Token and rest captures are only valid in named macros".into());
                }
                if capture_kind == CaptureKind::Sequence && position + 1 != atoms.len() {
                    return Err(
                        "Rest capture must be the last element of its pattern sequence".into(),
                    );
                }
                if captures.insert(name.0.clone(), capture_kind).is_some() {
                    return Err(format!(
                        "Macro capture '${}' is declared more than once",
                        name.0
                    ));
                }
            }
            MacroSeqAtom::Tok(token) => {
                if matches!(
                    token.0.as_str(),
                    "~>" | "<-"
                        | "->"
                        | "=>"
                        | ":="
                        | "|"
                        | ":"
                        | ";"
                        | "."
                        | ","
                        | "="
                        | "!"
                        | "::"
                        | "^"
                ) {
                    return Err(format!(
                        "Macro token '{}' conflicts with reserved syntax",
                        token.0
                    ));
                }
                *fixed += 1;
            }
            MacroSeqAtom::Quoted(_) => *fixed += 1,
            MacroSeqAtom::Seq(inner) => pattern_captures(inner, captures, fixed, kind)?,
        }
    }
    Ok(())
}

fn first_fixed_position(atoms: &[MacroSeqAtom]) -> usize {
    fn visit(atoms: &[MacroSeqAtom], position: &mut usize) -> Option<usize> {
        for atom in atoms {
            match atom {
                MacroSeqAtom::Capture(_)
                | MacroSeqAtom::TokenCapture(_)
                | MacroSeqAtom::Rest(_) => *position += 1,
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

fn match_pattern(pattern: &[MacroSeqAtom], input: &[MacroExp], captures: &mut Captures) -> bool {
    let has_rest = matches!(pattern.last(), Some(MacroSeqAtom::Rest(_)));
    let prefix_len = pattern.len() - usize::from(has_rest);
    if input.len() < prefix_len || (!has_rest && input.len() != prefix_len) {
        return false;
    }
    for (pattern, input) in pattern[..prefix_len].iter().zip(input) {
        let matched = match (pattern, input) {
            (MacroSeqAtom::Capture(name), MacroExp::RawExp(exp)) => {
                captures.insert(name.0.clone(), CaptureValue::Expression(exp.clone()));
                true
            }
            (
                MacroSeqAtom::TokenCapture(name),
                token @ (MacroExp::Tok(_) | MacroExp::Quoted(_)),
            ) => {
                captures.insert(name.0.clone(), CaptureValue::Token(token.clone()));
                true
            }
            (MacroSeqAtom::Tok(left), MacroExp::Tok(right)) => left == right,
            (MacroSeqAtom::Quoted(left), MacroExp::Quoted(right)) => left == right,
            (MacroSeqAtom::Seq(left), MacroExp::Seq(right)) => match_pattern(left, right, captures),
            _ => false,
        };
        if !matched {
            return false;
        }
    }
    if let Some(MacroSeqAtom::Rest(name)) = pattern.last() {
        captures.insert(
            name.0.clone(),
            CaptureValue::Sequence(input[prefix_len..].to_vec()),
        );
    }
    true
}

fn rename_template_binders(exp: &mut SExp) {
    // Both preparation and each instantiation need distinct binder identities.
    static NEXT_BINDER_SCOPE: AtomicU64 = AtomicU64::new(0);
    let identity = NEXT_BINDER_SCOPE.fetch_add(1, Ordering::Relaxed);
    alpha_rename(exp, identity, &mut 0, &mut Vec::new());
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
            MacroExp::RawExp(exp) => alpha_rename(exp, order, counter, scopes),
            MacroExp::Seq(tokens) => alpha_macro_exps(tokens, order, counter, scopes),
            MacroExp::Tok(_)
            | MacroExp::Quoted(_)
            | MacroExp::TemplateName(_)
            | MacroExp::TokenParameter(_)
            | MacroExp::Splice(_) => {}
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
            let scope = HashMap::from([binding]);
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
        | SExp::Captured(_) => {}
        SExp::AccessPath { access, parameters } => {
            rename_access(access, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
        }
        SExp::AssociatedAccess { base, .. }
        | SExp::InferredProjection { value: base, .. }
        | SExp::ThunkType {
            computation_ty: base,
        }
        | SExp::ReturnType { value_ty: base }
        | SExp::Thunk { computation: base }
        | SExp::Return { value: base }
        | SExp::Force { value: base }
        | SExp::PowerSet { set: base }
        | SExp::BoxType { program_ty: base }
        | SExp::IdRefl { element: base } => alpha_rename(base, order, counter, scopes),
        SExp::MathMacro { tokens, .. } | SExp::NamedMacro { tokens, .. } => {
            alpha_macro_exps(tokens, order, counter, scopes)
        }
        SExp::TokenMatch { branches, .. } => {
            for (_, body) in branches {
                alpha_rename(body, order, counter, scopes);
            }
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
        SExp::App { func, arg }
        | SExp::ComputationFunction {
            domain: func,
            codomain: arg,
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
        SExp::IndCase {
            path,
            scrutinee,
            return_type,
            branches,
        } => {
            rename_access(path, scopes);
            alpha_rename(scrutinee, order, counter, scopes);
            alpha_rename(return_type, order, counter, scopes);
            for (_, branch) in branches {
                alpha_rename(branch, order, counter, scopes);
            }
        }
        SExp::Induction {
            binder,
            return_type,
            cases,
        } => {
            alpha_rename(&mut binder.ty, order, counter, scopes);
            let local = binder
                .vars
                .iter_mut()
                .map(|var| fresh_binder(var, order, counter))
                .collect();
            scopes.push(local);
            alpha_rename(return_type, order, counter, scopes);
            scopes.pop();
            for (_, case) in cases {
                alpha_rename(case, order, counter, scopes);
            }
        }
        SExp::IndElimPrim {
            path,
            parameters,
            motive,
        } => {
            rename_access(path, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
            alpha_rename(motive, order, counter, scopes);
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
        SExp::ValueLet {
            var,
            value_ty,
            value,
            body,
        } => {
            alpha_rename(value_ty, order, counter, scopes);
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
        SExp::Block(block) | SExp::Program(block) => {
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
                    Statement::Bind {
                        var,
                        ty,
                        computation,
                    } => {
                        alpha_rename(ty, order, counter, scopes);
                        alpha_rename(computation, order, counter, scopes);
                        scopes.push(HashMap::from([fresh_binder(var, order, counter)]));
                        pushed += 1;
                    }
                    Statement::Sufficient { map, map_ty } => {
                        alpha_rename(map, order, counter, scopes);
                        alpha_rename(map_ty, order, counter, scopes);
                    }
                    Statement::TakeFrom { var, ty, existence } => {
                        alpha_rename(ty, order, counter, scopes);
                        alpha_rename(existence, order, counter, scopes);
                        scopes.push(HashMap::from([fresh_binder(var, order, counter)]));
                        pushed += 1;
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
            accessibility,
        } => alpha_many(
            [state_ty, result_ty, step, initial, accessibility],
            order,
            counter,
            scopes,
        ),
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
            accessibility,
            transition_equality,
        } => alpha_many(
            [
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            ],
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
) -> Result<(LocalAccess, ItemAccessResult), String> {
    let (module, item) = crate::elaborator::module_manager::resolve_access(env, from, access)
        .ok_or_else(|| {
            format!(
                "Free name {access:?} in macro template was not found in its definition environment"
            )
        })?;
    let name = match access {
        LocalAccess::Current { access } | LocalAccess::Resolved { access, .. } => access,
        LocalAccess::Named { child, .. } => child,
    };
    Ok((
        LocalAccess::Resolved {
            scope: hir::ScopeId(module.0),
            access: name.clone(),
        },
        item,
    ))
}

fn require_capture(
    kinds: &CaptureKinds,
    name: &Identifier,
    expected: CaptureKind,
) -> Result<(), String> {
    match kinds.get(name.as_str()) {
        Some(actual) if *actual == expected => Ok(()),
        Some(actual) => Err(format!(
            "Macro capture '{}' has kind {actual:?}, expected {expected:?}",
            name.as_str()
        )),
        None => Err(format!(
            "Macro template references undeclared capture '${}'",
            name.as_str()
        )),
    }
}

fn validate_macro_tokens(tokens: &mut [MacroExp], kinds: &CaptureKinds) -> Result<(), String> {
    for token in tokens {
        match token {
            MacroExp::TemplateName(name) => {
                *token = if kinds.get(name.as_str()) == Some(&CaptureKind::Token) {
                    MacroExp::TokenParameter(name.clone())
                } else {
                    MacroExp::RawExp(SExp::AccessPath {
                        access: LocalAccess::Current {
                            access: name.clone(),
                        },
                        parameters: Vec::new(),
                    })
                };
            }
            MacroExp::RawExp(exp) => validate_template(exp, kinds)?,
            MacroExp::Seq(inner) => validate_macro_tokens(inner, kinds)?,
            MacroExp::Splice(name) => require_capture(kinds, name, CaptureKind::Sequence)?,
            MacroExp::TokenParameter(name) => require_capture(kinds, name, CaptureKind::Token)?,
            MacroExp::Tok(_) | MacroExp::Quoted(_) => {}
        }
    }
    Ok(())
}

fn validate_template(template: &mut SExp, kinds: &CaptureKinds) -> Result<(), String> {
    let mut result = Ok(());
    walk_sexp_control(template, &mut |node| {
        if result.is_err() {
            return false;
        }
        match node {
            SExp::MacroParameter(name) => {
                result = require_capture(kinds, name, CaptureKind::Expression);
                false
            }
            SExp::NamedMacro { tokens, .. } | SExp::MathMacro { tokens, .. } => {
                result = validate_macro_tokens(tokens, kinds);
                false
            }
            SExp::TokenMatch { target, branches } => {
                result = (|| {
                    let target_kind = kinds.get(target.as_str()).ok_or_else(|| {
                        format!(
                            "Token match references undeclared capture '{}'",
                            target.as_str()
                        )
                    })?;
                    if *target_kind == CaptureKind::Expression {
                        return Err("Token match requires a token or sequence capture".into());
                    }
                    for (pattern, body) in branches {
                        let mut local = kinds.clone();
                        match pattern {
                            TokenMatchPattern::Default => {}
                            TokenMatchPattern::Token(atom) => {
                                require_capture(kinds, target, CaptureKind::Token)?;
                                pattern_captures(
                                    std::slice::from_ref(atom),
                                    &mut local,
                                    &mut 0,
                                    MacroKind::Named,
                                )?;
                            }
                            TokenMatchPattern::Sequence(atoms) => {
                                require_capture(kinds, target, CaptureKind::Sequence)?;
                                pattern_captures(atoms, &mut local, &mut 0, MacroKind::Named)?;
                            }
                        }
                        validate_template(body, &local)?;
                    }
                    Ok(())
                })();
                false
            }
            _ => true,
        }
    });
    result
}

fn prepare_template(
    mut template: SExp,
    manager: &ModuleManager,
    env: &CrateEnv,
    module: ModuleId,
    captures: &CaptureKinds,
    declaration_order: u64,
) -> Result<SExp, String> {
    validate_template(&mut template, captures)?;
    rename_template_binders(&mut template);
    let mut error = None;
    walk_sexp_mut(&mut template, &mut |node| {
        if error.is_some() {
            return;
        }
        match node {
            SExp::Meta { kind, .. } => kind.origin = hir::MetaOrigin::Template,
            SExp::MathMacro {
                scope, max_order, ..
            }
            | SExp::NamedMacro {
                scope, max_order, ..
            } => {
                *scope = Some(hir::ScopeId(module.0));
                *max_order = Some(declaration_order);
            }
            SExp::AccessPath { access, parameters } => {
                if matches!(access, LocalAccess::Current { access: name } if name.as_str().starts_with("<macro:"))
                {
                    return;
                }
                match resolve_access(env, module, access) {
                    Ok((_, ItemAccessResult::Expression(exp))) => {
                        if !parameters.is_empty() {
                            error = Some("Module parameter cannot take module arguments".into());
                            return;
                        }
                        *node = SExp::Captured(manager.capture_expression(exp));
                    }
                    Ok((resolved, _)) => *access = resolved,
                    Err(message) => error = Some(message),
                }
            }
            SExp::IndCase { path, .. }
            | SExp::IndElimPrim { path, .. }
            | SExp::ProgramCase { path, .. }
            | SExp::RecordTypeCtor { access: path, .. } => {
                match resolve_access(env, module, path) {
                    Ok((resolved, _)) => *path = resolved,
                    Err(message) => error = Some(message),
                }
            }
            _ => {}
        }
    });
    error.map_or(Ok(template), Err)
}

impl ModuleManager {
    fn macro_scope<'a>(&'a self, env: &CrateEnv, module: ModuleId) -> Option<&'a ModuleMacroScope> {
        if let Some(scope) = self.macro_scopes.get(&module) {
            return Some(scope);
        }
        let lazy = self.lazy_macro_scopes.get(&module)?;
        Some(lazy.materialized.get_or_init(|| {
            let source = self
                .macro_scope(env, lazy.source)
                .cloned()
                .unwrap_or_default();
            self.materialized_macro_scopes
                .set(self.materialized_macro_scopes.get() + 1);
            remap_macro_scope(source, self, env, &lazy.remapping)
        }))
    }

    pub(crate) fn materialize_macros(
        &mut self,
        _env: &CrateEnv,
        source: ModuleId,
        materialized: ModuleId,
        remapping: &MacroInstantiation<'_>,
    ) {
        if !self.macro_scopes.contains_key(&source) && !self.lazy_macro_scopes.contains_key(&source)
        {
            return;
        }
        self.lazy_macro_scopes.insert(
            materialized,
            LazyModuleMacroScope {
                source,
                remapping: remapping.into(),
                materialized: OnceCell::new(),
            },
        );
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
        let mut captures = HashMap::new();
        let mut fixed = 0;
        pattern_captures(&pattern, &mut captures, &mut fixed, kind)?;
        if kind == MacroKind::Math && fixed == 0 {
            return Err(format!(
                "Math macro '{}' must contain at least one fixed token",
                name.as_str()
            ));
        }
        if kind == MacroKind::Math {
            let mut has_match = false;
            let mut template_check = template.clone();
            walk_sexp_mut(&mut template_check, &mut |node| {
                has_match |= matches!(node, SExp::TokenMatch { .. });
            });
            if has_match {
                return Err("Token matching is only valid in named macros".into());
            }
        }
        let order = self.next_macro_order;
        self.next_macro_order += 1;
        let mut template = prepare_template(template, self, env, self.current(), &captures, order)?;
        let visible_named = self
            .visible_macros(env, self.current())
            .into_iter()
            .filter(|definition| definition.kind == MacroKind::Named)
            .map(|definition| definition.name.0.clone())
            .collect::<HashSet<_>>();
        let self_name = name.clone();
        let mut nested_error = None;
        walk_sexp_mut(&mut template, &mut |node| {
            if let SExp::NamedMacro { name, .. } = node
                && !visible_named.contains(name.as_str())
                && !(kind == MacroKind::Named && *name == self_name)
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
        let binding = env
            .resolve_import(self.current(), import_name.as_str())
            .ok_or_else(|| format!("Module import '{}' was not found", import_name.as_str()))?;
        let materialized = env.binding(binding).materialized;
        if env.unavailable(materialized, macro_name.as_str()) {
            return Err("macro requires an unavailable declaration".into());
        }
        let definition = self
            .macro_scope(env, materialized)
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
            if let Some(macros) = self.macro_scope(env, module) {
                output.extend(&macros.declared);
                output.extend(&macros.used);
            }
            current = env.module(module).parent();
        }
        output
    }

    #[cfg(test)]
    pub(crate) fn materialized_macro_scope_count(&self) -> usize {
        self.materialized_macro_scopes.get()
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
                    .map(MacroExp::RawExp),
                other => Ok(other.clone()),
            })
            .collect::<Result<Vec<_>, String>>()?;
        if let [MacroExp::RawExp(exp)] = tokens.as_slice() {
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
        let mut ancestor = Some(module);
        while let Some(scope) = ancestor {
            if env.unavailable(scope, name.as_str()) {
                return Err("macro requires an unavailable declaration".into());
            }
            ancestor = env.module(scope).parent();
        }
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
            .filter(|definition| max_order.is_none_or(|max| definition.declaration_order <= max))
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

fn remap_macro_scope(
    source: ModuleMacroScope,
    manager: &ModuleManager,
    env: &CrateEnv,
    remapping: &OwnedMacroInstantiation,
) -> ModuleMacroScope {
    let remap = |mut definition: MacroDefinition| {
        walk_sexp_mut(&mut definition.template, &mut |node| match node {
            SExp::AccessPath {
                access: LocalAccess::Resolved { scope, .. },
                ..
            }
            | SExp::IndCase {
                path: LocalAccess::Resolved { scope, .. },
                ..
            }
            | SExp::IndElimPrim {
                path: LocalAccess::Resolved { scope, .. },
                ..
            }
            | SExp::ProgramCase {
                path: LocalAccess::Resolved { scope, .. },
                ..
            }
            | SExp::RecordTypeCtor {
                access: LocalAccess::Resolved { scope, .. },
                ..
            } => {
                if let Some(remapped) = remapping.module_ids.get(&ModuleId(scope.0)) {
                    *scope = hir::ScopeId(remapped.0);
                }
            }
            SExp::MathMacro { scope, .. } | SExp::NamedMacro { scope, .. } => {
                if let Some(scope) = scope
                    && let Some(remapped) = remapping.module_ids.get(&ModuleId(scope.0))
                {
                    *scope = hir::ScopeId(remapped.0);
                }
            }
            SExp::Captured(id) => {
                let renamed = remap_all_global_ids(
                    env.arena(),
                    manager.captured_expression(*id),
                    &remapping.definition_ids,
                    &remapping.inductive_ids,
                    &remapping.program_inductive_ids,
                );
                *id = manager.capture_expression(exp_subst_map(
                    env.arena(),
                    renamed,
                    &remapping.substitutions,
                ));
            }
            _ => {}
        });
        definition
    };
    ModuleMacroScope {
        declared: source.declared.into_iter().map(&remap).collect(),
        used: source.used.into_iter().map(remap).collect(),
    }
}

fn instantiate_template(
    definition: &MacroDefinition,
    captures: &Captures,
    depth: u16,
) -> Result<SExp, String> {
    let mut result = definition.template.clone();
    rename_template_binders(&mut result);
    instantiate_exp(&mut result, captures, depth)?;
    Ok(result)
}

fn instantiate_tokens(
    tokens: &mut Vec<MacroExp>,
    captures: &Captures,
    depth: u16,
) -> Result<(), String> {
    let mut output = Vec::new();
    for token in std::mem::take(tokens) {
        match token {
            MacroExp::Splice(name) => match captures.get(name.as_str()) {
                Some(CaptureValue::Sequence(items)) => output.extend(items.clone()),
                _ => {
                    return Err(format!(
                        "Rest capture '{}' has no matched sequence",
                        name.as_str()
                    ));
                }
            },
            MacroExp::TokenParameter(name) => match captures.get(name.as_str()) {
                Some(CaptureValue::Token(token)) => output.push(token.clone()),
                _ => {
                    return Err(format!(
                        "Token capture '{}' has no matched token",
                        name.as_str()
                    ));
                }
            },
            MacroExp::RawExp(mut exp) => {
                instantiate_exp(&mut exp, captures, depth)?;
                output.push(MacroExp::RawExp(exp));
            }
            MacroExp::Seq(mut items) => {
                instantiate_tokens(&mut items, captures, depth)?;
                output.push(MacroExp::Seq(items));
            }
            other => output.push(other),
        }
    }
    *tokens = output;
    Ok(())
}

fn instantiate_exp(exp: &mut SExp, captures: &Captures, depth: u16) -> Result<(), String> {
    let mut result = Ok(());
    walk_sexp_control(exp, &mut |node| {
        if result.is_err() {
            return false;
        }
        match node {
            SExp::MacroParameter(name) => {
                match captures.get(name.as_str()) {
                    Some(CaptureValue::Expression(replacement)) => *node = replacement.clone(),
                    _ => {
                        result = Err(format!(
                            "Capture '${}' has no matched expression",
                            name.as_str()
                        ))
                    }
                }
                // Caller syntax is opaque: never substitute into an inserted expression.
                false
            }
            SExp::MathMacro {
                tokens,
                depth: nested,
                ..
            }
            | SExp::NamedMacro {
                tokens,
                depth: nested,
                ..
            } => {
                *nested = depth + 1;
                result = instantiate_tokens(tokens, captures, depth);
                false
            }
            SExp::TokenMatch { target, branches } => {
                let selected = (|| {
                    let value = captures.get(target.as_str()).ok_or_else(|| {
                        format!(
                            "Token match capture '{}' has no matched value",
                            target.as_str()
                        )
                    })?;
                    for (pattern, body) in branches {
                        let mut local = captures.clone();
                        let matches = match (pattern, value) {
                            (TokenMatchPattern::Default, _) => true,
                            (TokenMatchPattern::Token(atom), CaptureValue::Token(token)) => {
                                match_pattern(
                                    std::slice::from_ref(atom),
                                    std::slice::from_ref(token),
                                    &mut local,
                                )
                            }
                            (TokenMatchPattern::Sequence(atoms), CaptureValue::Sequence(items)) => {
                                match_pattern(atoms, items, &mut local)
                            }
                            _ => false,
                        };
                        if matches {
                            let mut selected = body.clone();
                            instantiate_exp(&mut selected, &local, depth)?;
                            return Ok(selected);
                        }
                    }
                    Err(format!(
                        "No token match branch matches capture '{}'",
                        target.as_str()
                    ))
                })();
                match selected {
                    Ok(selected) => *node = selected,
                    Err(error) => result = Err(error),
                }
                false
            }
            _ => true,
        }
    });
    result
}
