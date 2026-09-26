use crate::hir::*;
use std::collections::HashMap;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CaptureKind {
    Expression,
    Token,
    Sequence,
}

#[derive(Debug, Clone)]
pub(crate) enum CaptureValue {
    Expression(SExp),
    Token(MacroExp),
    Sequence(Vec<MacroExp>),
}

pub(crate) type CaptureKinds = HashMap<String, CaptureKind>;
pub(crate) type Captures = HashMap<String, CaptureValue>;

pub(crate) fn pattern_captures(
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

pub(crate) fn first_fixed_position(atoms: &[MacroSeqAtom]) -> usize {
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

pub(crate) fn match_pattern(
    pattern: &[MacroSeqAtom],
    input: &[MacroExp],
    captures: &mut Captures,
) -> bool {
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

pub(crate) fn rename_template_binders(exp: &mut SExp, identity: u64) {
    crate::bindings::alpha_rename(
        exp,
        crate::bindings::Mode::Hygienic(identity),
        &mut 0,
        &mut Vec::new(),
    );
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
                            span: Default::default(),
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

pub(crate) fn validate_template(template: &mut SExp, kinds: &CaptureKinds) -> Result<(), String> {
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

pub(crate) fn instantiate_template(
    definition: &MacroDefinition,
    captures: &Captures,
    depth: u16,
    identity: u64,
) -> Result<SExp, String> {
    let mut result = definition.template.clone();
    rename_template_binders(&mut result, identity);
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

pub fn walk_sexp_mut(exp: &mut SExp, action: &mut impl FnMut(&mut SExp)) {
    walk_sexp_control(exp, &mut |node| {
        action(node);
        true
    });
}

/// Visit a node before its children; returning false skips that subtree.
pub fn walk_sexp_control(exp: &mut SExp, action: &mut impl FnMut(&mut SExp) -> bool) {
    if !action(exp) {
        return;
    }
    match exp {
        SExp::Meta { .. } | SExp::Sort(_) | SExp::ValueType | SExp::MacroParameter(_) => {}
        SExp::AccessPath { parameters, .. } => {
            for parameter in parameters {
                walk_sexp_control(parameter, action);
            }
        }
        SExp::IndElimPrim {
            parameters, motive, ..
        } => {
            for parameter in parameters {
                walk_sexp_control(parameter, action);
            }
            walk_sexp_control(motive, action);
        }
        SExp::Reflect {
            expression: base, ..
        }
        | SExp::AssociatedAccess { base, .. }
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
        | SExp::IdRefl { element: base } => walk_sexp_control(base, action),
        SExp::MathMacro { tokens, .. } | SExp::NamedMacro { tokens, .. } => {
            walk_macro_exps_mut(tokens, action);
        }
        SExp::TokenMatch { branches, .. } => {
            for (_, body) in branches {
                walk_sexp_control(body, action);
            }
        }
        SExp::Where { exp, clauses } => {
            walk_sexp_control(exp, action);
            for (_, ty, body) in clauses {
                walk_sexp_control(ty, action);
                walk_sexp_control(body, action);
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
            walk_sexp_control(body, action);
            if let SExp::TakeProp { existence, .. } = exp {
                walk_sexp_control(existence, action);
            }
        }
        SExp::Exists { bind } => walk_bind_mut(bind, action),
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
        } => {
            walk_sexp_control(func, action);
            walk_sexp_control(arg, action);
        }
        SExp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => walk_many_mut([superset, subset, element, proof], action),
        SExp::IndCase {
            scrutinee,
            return_type,
            branches,
            ..
        } => {
            walk_sexp_control(scrutinee, action);
            walk_sexp_control(return_type, action);
            for (_, branch) in branches {
                walk_sexp_control(branch, action);
            }
        }
        SExp::Induction {
            binder,
            return_type,
            cases,
        } => {
            walk_sexp_control(&mut binder.ty, action);
            walk_sexp_control(return_type, action);
            for (_, case) in cases {
                walk_sexp_control(case, action);
            }
        }
        SExp::ValueLet {
            value_ty,
            value,
            body,
            ..
        } => {
            walk_many_mut([value_ty, value, body], action);
        }
        SExp::ComputationLam { value_ty, body, .. } => {
            walk_sexp_control(value_ty, action);
            walk_sexp_control(body, action);
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
            walk_sexp_control(scrutinee, action);
            for (_, _, body) in branches {
                walk_sexp_control(body, action);
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
            walk_sexp_control(state_ty, action);
            walk_sexp_control(result_ty, action);
            match exp {
                SExp::Pred { element, .. } => walk_sexp_control(element, action),
                SExp::SubsetElim { superset, .. } => walk_sexp_control(superset, action),
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
            accessibility,
        } => walk_many_mut([state_ty, result_ty, step, initial, accessibility], action),
        SExp::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => walk_many_mut(
            [
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            ],
            action,
        ),
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
                walk_sexp_control(parameter, action);
            }
            for (_, field) in fields {
                walk_sexp_control(field, action);
            }
        }
        SExp::SubSet { set, predicate, .. } => {
            walk_sexp_control(set, action);
            walk_sexp_control(predicate, action);
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
        SExp::Block(block) | SExp::Program(block) => {
            for statement in &mut block.statements {
                walk_statement_mut(statement, action);
            }
            walk_sexp_control(&mut block.result, action);
        }
    }
}

fn walk_many_mut<const N: usize>(
    exps: [&mut Box<SExp>; N],
    action: &mut impl FnMut(&mut SExp) -> bool,
) {
    for exp in exps {
        walk_sexp_control(exp, action);
    }
}

fn walk_macro_exps_mut(tokens: &mut [MacroExp], action: &mut impl FnMut(&mut SExp) -> bool) {
    for token in tokens {
        match token {
            MacroExp::RawExp(exp) => walk_sexp_control(exp, action),
            MacroExp::Seq(tokens) => walk_macro_exps_mut(tokens, action),
            MacroExp::Tok(_)
            | MacroExp::Quoted(_)
            | MacroExp::TemplateName(_)
            | MacroExp::TokenParameter(_)
            | MacroExp::Splice(_) => {}
        }
    }
}

fn walk_bind_mut(bind: &mut Bind, action: &mut impl FnMut(&mut SExp) -> bool) {
    match bind {
        Bind::Named(bind) => walk_sexp_control(&mut bind.ty, action),
        Bind::Subset { ty, predicate, .. } | Bind::SubsetWithProof { ty, predicate, .. } => {
            walk_sexp_control(ty, action);
            walk_sexp_control(predicate, action);
        }
    }
}

fn walk_statement_mut(statement: &mut Statement, action: &mut impl FnMut(&mut SExp) -> bool) {
    match statement {
        Statement::Fix(binds) => {
            for bind in binds {
                walk_sexp_control(&mut bind.ty, action);
            }
        }
        Statement::Let { ty, body, .. } => {
            walk_sexp_control(ty, action);
            walk_sexp_control(body, action);
        }
        Statement::Bind {
            ty, computation, ..
        } => {
            walk_sexp_control(ty, action);
            walk_sexp_control(computation, action);
        }
        Statement::Sufficient { map, map_ty } => {
            walk_sexp_control(map, action);
            walk_sexp_control(map_ty, action);
        }
        Statement::TakeFrom { ty, existence, .. } => {
            walk_sexp_control(ty, action);
            walk_sexp_control(existence, action);
        }
    }
}
