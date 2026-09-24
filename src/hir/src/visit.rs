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
    match &mut exp.kind {
        SExpKind::Meta { .. }
        | SExpKind::Sort(_)
        | SExpKind::ValueType
        | SExpKind::MacroParameter(_)
        | SExpKind::Captured(_) => {}
        SExpKind::AccessPath { parameters, .. } => {
            for parameter in parameters {
                walk_sexp_control(parameter, action);
            }
        }
        SExpKind::IndElimPrim {
            parameters, motive, ..
        } => {
            for parameter in parameters {
                walk_sexp_control(parameter, action);
            }
            walk_sexp_control(motive, action);
        }
        SExpKind::AssociatedAccess { base, .. }
        | SExpKind::InferredProjection { value: base, .. }
        | SExpKind::ThunkType {
            computation_ty: base,
        }
        | SExpKind::ReturnType { value_ty: base }
        | SExpKind::Thunk { computation: base }
        | SExpKind::Return { value: base }
        | SExpKind::Force { value: base }
        | SExpKind::PowerSet { set: base }
        | SExpKind::BoxType { program_ty: base }
        | SExpKind::IdRefl { element: base } => walk_sexp_control(base, action),
        SExpKind::MathMacro { tokens, .. } | SExpKind::NamedMacro { tokens, .. } => {
            walk_macro_exps_mut(tokens, action);
        }
        SExpKind::TokenMatch { branches, .. } => {
            for (_, body) in branches {
                walk_sexp_control(body, action);
            }
        }
        SExpKind::Where { exp, clauses } => {
            walk_sexp_control(exp, action);
            for (_, ty, body) in clauses {
                walk_sexp_control(ty, action);
                walk_sexp_control(body, action);
            }
        }
        SExpKind::Prod { bind, body }
        | SExpKind::Lam { bind, body }
        | SExpKind::TakeProp {
            bind,
            body,
            existence: _,
        } => {
            walk_bind_mut(bind, action);
            walk_sexp_control(body, action);
            if let SExp {
                kind: SExpKind::TakeProp { existence, .. },
                ..
            } = exp
            {
                walk_sexp_control(existence, action);
            }
        }
        SExpKind::Exists { bind } => walk_bind_mut(bind, action),
        SExpKind::App { func, arg }
        | SExpKind::ComputationFunction {
            domain: func,
            codomain: arg,
        }
        | SExpKind::Equal {
            left: func,
            right: arg,
        }
        | SExpKind::ExistsIntro {
            element: func,
            set: arg,
        }
        | SExpKind::BoxProgram {
            program_ty: func,
            program: arg,
        }
        | SExpKind::ForceBox {
            program_ty: func,
            boxed: arg,
        }
        | SExpKind::BoxApp {
            function: func,
            argument: arg,
        } => {
            walk_sexp_control(func, action);
            walk_sexp_control(arg, action);
        }
        SExpKind::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => walk_many_mut([superset, subset, element, proof], action),
        SExpKind::IndCase {
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
        SExpKind::Induction {
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
        SExpKind::ValueLet {
            value_ty,
            value,
            body,
            ..
        } => {
            walk_many_mut([value_ty, value, body], action);
        }
        SExpKind::ComputationLam { value_ty, body, .. } => {
            walk_sexp_control(value_ty, action);
            walk_sexp_control(body, action);
        }
        SExpKind::Sequence {
            computation,
            value_ty,
            body,
            ..
        } => walk_many_mut([computation, value_ty, body], action),
        SExpKind::ProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            walk_sexp_control(scrutinee, action);
            for (_, _, body) in branches {
                walk_sexp_control(body, action);
            }
        }
        SExpKind::RunStep {
            state_ty,
            result_ty,
        }
        | SExpKind::Pred {
            superset: state_ty,
            subset: result_ty,
            element: _,
        }
        | SExpKind::TypeLift {
            superset: state_ty,
            subset: result_ty,
        }
        | SExpKind::SubsetElim {
            element: state_ty,
            subset: result_ty,
            superset: _,
        } => {
            walk_sexp_control(state_ty, action);
            walk_sexp_control(result_ty, action);
            match &mut exp.kind {
                SExpKind::Pred { element, .. } => walk_sexp_control(element, action),
                SExpKind::SubsetElim { superset, .. } => walk_sexp_control(superset, action),
                _ => {}
            }
        }
        SExpKind::Continue {
            state_ty,
            result_ty,
            next,
        }
        | SExpKind::Finish {
            state_ty,
            result_ty,
            output: next,
        } => walk_many_mut([state_ty, result_ty, next], action),
        SExpKind::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => walk_many_mut([state_ty, result_ty, step, state], action),
        SExpKind::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => walk_many_mut([state_ty, result_ty, step, initial, accessibility], action),
        SExpKind::RunCase {
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
        SExpKind::RunStepRec {
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
        SExpKind::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => walk_many_mut([state_ty, result_ty, step, state, predecessors], action),
        SExpKind::AccDescent {
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
        SExpKind::RecordTypeCtor {
            parameters, fields, ..
        } => {
            for parameter in parameters {
                walk_sexp_control(parameter, action);
            }
            for (_, field) in fields {
                walk_sexp_control(field, action);
            }
        }
        SExpKind::SubSet { set, predicate, .. } => {
            walk_sexp_control(set, action);
            walk_sexp_control(predicate, action);
        }
        SExpKind::TakeSet {
            bind,
            body,
            existence,
            uniqueness,
        } => {
            walk_bind_mut(bind, action);
            walk_many_mut([body, existence, uniqueness], action);
        }
        SExpKind::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => walk_many_mut([left, right, ty, predicate, base, equality], action),
        SExpKind::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => walk_many_mut([left, right, left_to_right, right_to_left], action),
        SExpKind::AxiomFunExt {
            left,
            right,
            pointwise,
        } => walk_many_mut([left, right, pointwise], action),
        SExpKind::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => walk_many_mut([domain, family, inhabited], action),
        SExpKind::TakeEq {
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
        SExpKind::Block(block) | SExpKind::Program(block) => {
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
