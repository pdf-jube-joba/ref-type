use crate::*;

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
        SExp::Meta { .. }
        | SExp::Sort(_)
        | SExp::ValueType
        | SExp::MacroParameter(_)
        | SExp::Captured(_) => {}
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
