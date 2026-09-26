use crate::hir::*;
use std::collections::HashMap;
#[derive(Clone, Copy)]
pub(crate) enum Mode {
    Hygienic(u64),
    Resolved(u64),
}

fn spelling(name: &str) -> &str {
    name.strip_prefix("<macro:")
        .and_then(|name| name.splitn(3, ':').nth(2))
        .and_then(|name| name.strip_suffix('>'))
        .unwrap_or(name)
}

fn fresh_binder(
    identifier: &mut Identifier,
    mode: Mode,
    counter: &mut usize,
) -> (String, Identifier) {
    let original = identifier.0.clone();
    match mode {
        Mode::Hygienic(order) => {
            identifier.0 = format!("<macro:{order}:{}:{}>", *counter, spelling(&identifier.0));
            identifier.1 = None;
        }
        Mode::Resolved(order) => {
            identifier.0 = spelling(&identifier.0).to_owned();
            identifier.1 = Some(BindingId((1u64 << 63) | (order << 32) | *counter as u64));
        }
    }
    *counter += 1;
    (original, identifier.clone())
}

fn rename_access(access: &mut LocalAccess, scopes: &[HashMap<String, Identifier>]) {
    let LocalAccess::Current { access, .. } = access else {
        return;
    };
    if let Some(fresh) = scopes
        .iter()
        .rev()
        .find_map(|scope| scope.get(access.as_str()))
    {
        *access = fresh.clone();
    }
}

fn alpha_macro_exps(
    tokens: &mut [MacroExp],
    order: Mode,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, Identifier>>,
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

pub(crate) fn alpha_bind_type(
    bind: &mut Bind,
    order: Mode,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, Identifier>>,
) -> HashMap<String, Identifier> {
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
    order: Mode,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, Identifier>>,
) {
    for exp in exps {
        alpha_rename(exp, order, counter, scopes);
    }
}

pub(crate) fn alpha_rename(
    exp: &mut SExp,
    order: Mode,
    counter: &mut usize,
    scopes: &mut Vec<HashMap<String, Identifier>>,
) {
    match exp {
        SExp::Meta { .. } | SExp::Sort(_) | SExp::ValueType | SExp::MacroParameter(_) => {}
        SExp::AccessPath { access, parameters } => {
            rename_access(access, scopes);
            for parameter in parameters {
                alpha_rename(parameter, order, counter, scopes);
            }
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
            let depth = scopes.len();
            for (name, ty, body) in clauses {
                alpha_rename(ty, order, counter, scopes);
                alpha_rename(body, order, counter, scopes);
                scopes.push(HashMap::from([fresh_binder(name, order, counter)]));
            }
            alpha_rename(exp, order, counter, scopes);
            scopes.truncate(depth);
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
