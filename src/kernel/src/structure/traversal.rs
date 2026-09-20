//! Traversal of named fields. Each family has its own stack frame.
use super::*;
use Traversal::{All, Evaluation, Head};

pub(crate) fn visit_children(
    arena: &Arena,
    e: Expression,
    mut visit: impl FnMut(Expression, usize),
) {
    match e {
        Expression::SetTerm(h) => visit_set_term(arena, h, &mut visit),
        Expression::SetType(h) => visit_set_type(arena, h, &mut visit),
        Expression::SetKind(h) => visit_set_kind(arena, h, &mut visit),
        Expression::PropTerm(h) => visit_prop_term(arena, h, &mut visit),
        Expression::PropType(h) => visit_prop_type(arena, h, &mut visit),
        Expression::PropKind(h) => visit_prop_kind(arena, h, &mut visit),
        Expression::ValueTerm(h) => visit_value_term(arena, h, &mut visit),
        Expression::ValueType(h) => visit_value_type(arena, h, &mut visit),
        Expression::ValueKind(h) => visit_value_kind(arena, h, &mut visit),
        Expression::ComputationTerm(h) => visit_computation_term(arena, h, &mut visit),
        Expression::ComputationType(h) => visit_computation_type(arena, h, &mut visit),
        Expression::ComputationKind(h) => visit_computation_kind(arena, h, &mut visit),
    }
}
fn visit_set_term(arena: &Arena, h: SetTerm, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        SetTermForm::Bound { .. } => {}
        SetTermForm::ModuleParam { .. } => {}
        SetTermForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        SetTermForm::ReflectedProgramParam { .. } => {}
        SetTermForm::LambdaTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTermForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTermForm::AppTerm {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTermForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTermForm::Subset { set, predicate, .. } => {
            visit(set.clone().into(), 0);
            visit(predicate.clone().into(), 1);
        }
        SetTermForm::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            visit(superset.clone().into(), 0);
            visit(subset.clone().into(), 0);
            visit(element.clone().into(), 0);
            visit(proof.clone().into(), 0);
        }
        SetTermForm::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(next.clone().into(), 0);
        }
        SetTermForm::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(output.clone().into(), 0);
        }
        SetTermForm::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(initial.clone().into(), 0);
            visit(accessibility.clone().into(), 0);
        }
        SetTermForm::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(initial.clone().into(), 0);
            visit(transition.clone().into(), 0);
            visit(accessibility.clone().into(), 0);
            visit(transition_equality.clone().into(), 0);
        }
        SetTermForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(motive.clone().into(), 1);
            visit(on_continue.clone().into(), 0);
            visit(on_finish.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
        }
        SetTermForm::BoxProgram {
            program_ty,
            program,
        } => {
            visit(program_ty.clone().into(), 0);
            visit(program.clone().into(), 0);
        }
        SetTermForm::ForceBox { program_ty, boxed } => {
            visit(program_ty.clone().into(), 0);
            visit(boxed.clone().into(), 0);
        }
        SetTermForm::BoxApp {
            domain,
            codomain,
            function,
            argument,
            ..
        } => {
            visit(domain.clone().into(), 0);
            visit(codomain.clone().into(), 0);
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTermForm::BoxTypeApp {
            domain,
            codomain,
            function,
            argument,
            ..
        } => {
            visit(domain.clone().into(), 0);
            visit(codomain.clone().into(), 1);
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTermForm::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => {
            visit(domain.clone().into(), 0);
            visit(codomain.clone().into(), 0);
            visit(map.clone().into(), 0);
            visit(existence.clone().into(), 0);
            visit(uniqueness.clone().into(), 0);
        }
        SetTermForm::IndCtor { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        SetTermForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in cases {
                visit(child.clone().into(), 0);
            }
        }
        SetTermForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in branches {
                visit(child.clone().into(), 0);
            }
        }
        SetTermForm::SetCase {
            binders,
            result_ty,
            scrutinee,
            branches,
            ..
        } => {
            visit(result_ty.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
            for (i, child) in branches.iter().enumerate() {
                visit(child.clone().into(), binders.get(i).map_or(0, Vec::len));
            }
        }
    }
}
fn visit_set_type(arena: &Arena, h: SetType, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        SetTypeForm::Bound { .. } => {}
        SetTypeForm::ModuleParam { .. } => {}
        SetTypeForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        SetTypeForm::ReflectedProgramParam { .. } => {}
        SetTypeForm::ProdTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTypeForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTypeForm::LambdaTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTypeForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetTypeForm::AppTerm {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTypeForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        SetTypeForm::PowerSet { set } => {
            visit(set.clone().into(), 0);
        }
        SetTypeForm::TypeLift { superset, subset } => {
            visit(superset.clone().into(), 0);
            visit(subset.clone().into(), 0);
        }
        SetTypeForm::RunStep {
            state_ty,
            result_ty,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
        }
        SetTypeForm::BoxType { program_ty } => {
            visit(program_ty.clone().into(), 0);
        }
        SetTypeForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(motive.clone().into(), 1);
            visit(on_continue.clone().into(), 0);
            visit(on_finish.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
        }
        SetTypeForm::IndType { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        SetTypeForm::IndCtor { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        SetTypeForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in cases {
                visit(child.clone().into(), 0);
            }
        }
        SetTypeForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in branches {
                visit(child.clone().into(), 0);
            }
        }
    }
}
fn visit_set_kind(arena: &Arena, h: SetKind, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        SetKindForm::Base => {}
        SetKindForm::ProdTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetKindForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        SetKindForm::IndType { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        SetKindForm::ModuleParam { .. } => {}
        SetKindForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
    }
}
fn visit_prop_term(arena: &Arena, h: PropTerm, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        PropTermForm::Bound { .. } => {}
        PropTermForm::ModuleParam { .. } => {}
        PropTermForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        PropTermForm::LambdaTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTermForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTermForm::AppTerm {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        PropTermForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        PropTermForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(motive.clone().into(), 1);
            visit(on_continue.clone().into(), 0);
            visit(on_finish.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
        }
        PropTermForm::IdRefl { element } => {
            visit(element.clone().into(), 0);
        }
        PropTermForm::ExistsIntro { element, set } => {
            visit(element.clone().into(), 0);
            visit(set.clone().into(), 0);
        }
        PropTermForm::SubsetElim {
            element,
            subset,
            superset,
        } => {
            visit(element.clone().into(), 0);
            visit(subset.clone().into(), 0);
            visit(superset.clone().into(), 0);
        }
        PropTermForm::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => {
            visit(left.clone().into(), 0);
            visit(right.clone().into(), 0);
            visit(ty.clone().into(), 0);
            visit(predicate.clone().into(), 1);
            visit(base.clone().into(), 0);
            visit(equality.clone().into(), 0);
        }
        PropTermForm::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => {
            visit(domain.clone().into(), 0);
            visit(proposition.clone().into(), 0);
            visit(map.clone().into(), 0);
            visit(existence.clone().into(), 0);
        }
        PropTermForm::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            visit(func.clone().into(), 0);
            visit(domain.clone().into(), 0);
            visit(codomain.clone().into(), 0);
            visit(element.clone().into(), 0);
            visit(existence.clone().into(), 0);
            visit(uniqueness.clone().into(), 0);
        }
        PropTermForm::SetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => {
            visit(left.clone().into(), 0);
            visit(right.clone().into(), 0);
            visit(left_to_right.clone().into(), 0);
            visit(right_to_left.clone().into(), 0);
        }
        PropTermForm::FunExt {
            left,
            right,
            pointwise,
        } => {
            visit(left.clone().into(), 0);
            visit(right.clone().into(), 0);
            visit(pointwise.clone().into(), 0);
        }
        PropTermForm::ClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            visit(domain.clone().into(), 0);
            visit(family.clone().into(), 0);
            visit(inhabited.clone().into(), 0);
        }
        PropTermForm::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(state.clone().into(), 0);
            visit(predecessors.clone().into(), 0);
        }
        PropTermForm::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(from.clone().into(), 0);
            visit(to.clone().into(), 0);
            visit(accessibility.clone().into(), 0);
            visit(transition.clone().into(), 0);
        }
        PropTermForm::IndCtor { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        PropTermForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in cases {
                visit(child.clone().into(), 0);
            }
        }
        PropTermForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in branches {
                visit(child.clone().into(), 0);
            }
        }
    }
}
fn visit_prop_type(arena: &Arena, h: PropType, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        PropTypeForm::Bound { .. } => {}
        PropTypeForm::ModuleParam { .. } => {}
        PropTypeForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        PropTypeForm::ProdTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTypeForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTypeForm::LambdaTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTypeForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropTypeForm::AppTerm {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        PropTypeForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        PropTypeForm::Pred {
            superset,
            subset,
            element,
        } => {
            visit(superset.clone().into(), 0);
            visit(subset.clone().into(), 0);
            visit(element.clone().into(), 0);
        }
        PropTypeForm::Equal { left, right } => {
            visit(left.clone().into(), 0);
            visit(right.clone().into(), 0);
        }
        PropTypeForm::Exists { set } => {
            visit(set.clone().into(), 0);
        }
        PropTypeForm::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(state.clone().into(), 0);
        }
        PropTypeForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(motive.clone().into(), 1);
            visit(on_continue.clone().into(), 0);
            visit(on_finish.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
        }
        PropTypeForm::IndType { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        PropTypeForm::IndCtor { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        PropTypeForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in cases {
                visit(child.clone().into(), 0);
            }
        }
        PropTypeForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            visit(scrutinee.clone().into(), 0);
            for (i, child) in motive_domains.iter().enumerate() {
                visit(child.clone().into(), i);
            }
            visit(motive_body.clone().into(), motive_vars.len());
            for child in branches {
                visit(child.clone().into(), 0);
            }
        }
    }
}
fn visit_prop_kind(arena: &Arena, h: PropKind, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        PropKindForm::Base => {}
        PropKindForm::ProdTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropKindForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        PropKindForm::IndType { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        PropKindForm::ModuleParam { .. } => {}
        PropKindForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
    }
}
fn visit_value_term(arena: &Arena, h: ValueTerm, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        ValueTermForm::Bound { .. } => {}
        ValueTermForm::ModuleParam { .. } => {}
        ValueTermForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        ValueTermForm::ThunkValue { computation } => {
            visit(computation.clone().into(), 0);
        }
        ValueTermForm::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(next.clone().into(), 0);
        }
        ValueTermForm::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(output.clone().into(), 0);
        }
        ValueTermForm::InductiveConstructor {
            parameters, fields, ..
        } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
            for child in fields {
                visit(child.clone().into(), 0);
            }
        }
    }
}
fn visit_value_type(arena: &Arena, h: ValueType, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        ValueTypeForm::Bound { .. } => {}
        ValueTypeForm::ModuleParam { .. } => {}
        ValueTypeForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        ValueTypeForm::Thunk { computation_ty } => {
            visit(computation_ty.clone().into(), 0);
        }
        ValueTypeForm::RunStep {
            state_ty,
            result_ty,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
        }
        ValueTypeForm::Inductive { parameters, .. } => {
            for child in parameters {
                visit(child.clone().into(), 0);
            }
        }
        ValueTypeForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ValueTypeForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
    }
}
fn visit_value_kind(arena: &Arena, h: ValueKind, visit: &mut dyn FnMut(Expression, usize)) {
    let node = arena.read(h.clone());
    match &node.form {
        ValueKindForm::Base => {}
        ValueKindForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
    }
}
fn visit_computation_term(
    arena: &Arena,
    h: ComputationTerm,
    visit: &mut dyn FnMut(Expression, usize),
) {
    let node = arena.read(h.clone());
    match &node.form {
        ComputationTermForm::ModuleParam { .. } => {}
        ComputationTermForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        ComputationTermForm::Return { value } => {
            visit(value.clone().into(), 0);
        }
        ComputationTermForm::Force { value } => {
            visit(value.clone().into(), 0);
        }
        ComputationTermForm::LambdaTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTermForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTermForm::AppTerm {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        ComputationTermForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
        ComputationTermForm::Sequence {
            value_ty,
            computation,
            body,
            ..
        } => {
            visit(value_ty.clone().into(), 0);
            visit(computation.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTermForm::ValueLet {
            value_ty,
            value,
            body,
            ..
        } => {
            visit(value_ty.clone().into(), 0);
            visit(value.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTermForm::Case {
            binders,
            result_ty,
            scrutinee,
            branches,
            ..
        } => {
            visit(result_ty.clone().into(), 0);
            visit(scrutinee.clone().into(), 0);
            for (i, child) in branches.iter().enumerate() {
                visit(child.clone().into(), binders.get(i).map_or(0, Vec::len));
            }
        }
        ComputationTermForm::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(initial.clone().into(), 0);
            visit(accessibility.clone().into(), 0);
        }
        ComputationTermForm::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => {
            visit(state_ty.clone().into(), 0);
            visit(result_ty.clone().into(), 0);
            visit(step.clone().into(), 0);
            visit(initial.clone().into(), 0);
            visit(transition.clone().into(), 0);
            visit(accessibility.clone().into(), 0);
            visit(transition_equality.clone().into(), 0);
        }
    }
}
fn visit_computation_type(
    arena: &Arena,
    h: ComputationType,
    visit: &mut dyn FnMut(Expression, usize),
) {
    let node = arena.read(h.clone());
    match &node.form {
        ComputationTypeForm::Bound { .. } => {}
        ComputationTypeForm::ModuleParam { .. } => {}
        ComputationTypeForm::Annotated { body, classifier } => {
            visit(body.clone().into(), 0);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                visit(ty.clone(), 0);
            }
        }
        ComputationTypeForm::ReturnType { value_ty } => {
            visit(value_ty.clone().into(), 0);
        }
        ComputationTypeForm::ProdTerm { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTypeForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTypeForm::LambdaType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
        ComputationTypeForm::AppType {
            function, argument, ..
        } => {
            visit(function.clone().into(), 0);
            visit(argument.clone().into(), 0);
        }
    }
}
fn visit_computation_kind(
    arena: &Arena,
    h: ComputationKind,
    visit: &mut dyn FnMut(Expression, usize),
) {
    let node = arena.read(h.clone());
    match &node.form {
        ComputationKindForm::Base => {}
        ComputationKindForm::ProdType { domain, body, .. } => {
            visit(domain.clone().into(), 0);
            visit(body.clone().into(), 1);
        }
    }
}

pub(crate) fn map_children(
    arena: &Arena,
    e: Expression,
    traversal: Traversal,
    mut map: impl FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    match e {
        Expression::SetTerm(h) => map_set_term(arena, h, traversal, &mut map),
        Expression::SetType(h) => map_set_type(arena, h, traversal, &mut map),
        Expression::SetKind(h) => map_set_kind(arena, h, traversal, &mut map),
        Expression::PropTerm(h) => map_prop_term(arena, h, traversal, &mut map),
        Expression::PropType(h) => map_prop_type(arena, h, traversal, &mut map),
        Expression::PropKind(h) => map_prop_kind(arena, h, traversal, &mut map),
        Expression::ValueTerm(h) => map_value_term(arena, h, traversal, &mut map),
        Expression::ValueType(h) => map_value_type(arena, h, traversal, &mut map),
        Expression::ValueKind(h) => map_value_kind(arena, h, traversal, &mut map),
        Expression::ComputationTerm(h) => map_computation_term(arena, h, traversal, &mut map),
        Expression::ComputationType(h) => map_computation_type(arena, h, traversal, &mut map),
        Expression::ComputationKind(h) => map_computation_kind(arena, h, traversal, &mut map),
    }
}

// This macro only updates a typed field. The match arms explicitly list each
// field's binder depth and the traversals that may enter it.
macro_rules! child {
    ($arena:ident, $map:ident, $traversal:ident, $program:expr; $slot:expr, $depth:expr, $($mode:pat_param)|+) => {
        if matches!($traversal,$($mode)|+) {
            let before:Expression=$slot.clone().into();
            if !matches!($traversal,Evaluation) || $program || !$arena.sort(before.clone()).is_program() {
                let after=$map(before.clone(),$depth)?;
                if before.family()!=after.family() || $arena.sort(before)!=$arena.sort(after.clone()) {
                    return Err("transformation changed syntax family or sort index".into());
                }
                *$slot=after.try_into().map_err(|error| format!("{error}"))?;
            }
        }
    };
}
fn map_set_term(
    arena: &Arena,
    h: SetTerm,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        SetTermForm::Bound { .. } => {}
        SetTermForm::ModuleParam { .. } => {}
        SetTermForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        SetTermForm::ReflectedProgramParam { .. } => {}
        SetTermForm::LambdaTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTermForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTermForm::AppTerm {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        SetTermForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        SetTermForm::Subset { set, predicate, .. } => {
            field!(set, 0, All | Evaluation);
            field!(predicate, 1, All | Evaluation);
        }
        SetTermForm::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            field!(superset, 0, All | Evaluation);
            field!(subset, 0, All | Evaluation);
            field!(element, 0, All | Evaluation);
            field!(proof, 0, All | Evaluation);
        }
        SetTermForm::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(next, 0, All | Evaluation);
        }
        SetTermForm::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(output, 0, All | Evaluation);
        }
        SetTermForm::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(step, 0, All | Evaluation);
            field!(initial, 0, All | Evaluation);
            field!(accessibility, 0, All);
        }
        SetTermForm::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(step, 0, All | Evaluation);
            field!(initial, 0, All | Evaluation);
            field!(transition, 0, All | Head | Evaluation);
            field!(accessibility, 0, All);
            field!(transition_equality, 0, All);
        }
        SetTermForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(motive, 1, All | Evaluation);
            field!(on_continue, 0, All | Evaluation);
            field!(on_finish, 0, All | Evaluation);
            field!(scrutinee, 0, All | Head | Evaluation);
        }
        SetTermForm::BoxProgram {
            program_ty,
            program,
        } => {
            field!(program_ty, 0, All | Evaluation);
            field!(program, 0, All | Evaluation);
        }
        SetTermForm::ForceBox { program_ty, boxed } => {
            field!(program_ty, 0, All | Evaluation);
            field!(boxed, 0, All | Head | Evaluation);
        }
        SetTermForm::BoxApp {
            domain,
            codomain,
            function,
            argument,
            ..
        } => {
            field!(domain, 0, All | Evaluation);
            field!(codomain, 0, All | Evaluation);
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Head | Evaluation);
        }
        SetTermForm::BoxTypeApp {
            domain,
            codomain,
            function,
            argument,
            ..
        } => {
            field!(domain, 0, All | Evaluation);
            field!(codomain, 1, All | Evaluation);
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        SetTermForm::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => {
            field!(domain, 0, All | Evaluation);
            field!(codomain, 0, All | Evaluation);
            field!(map, 0, All | Evaluation);
            field!(existence, 0, All | Evaluation);
            field!(uniqueness, 0, All | Evaluation);
        }
        SetTermForm::IndCtor { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTermForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in cases {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTermForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in branches {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTermForm::SetCase {
            binders,
            result_ty,
            scrutinee,
            branches,
            ..
        } => {
            field!(result_ty, 0, All | Evaluation);
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in branches.iter_mut().enumerate() {
                field!(child, binders.get(i).map_or(0, Vec::len), All | Evaluation);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_set_type(
    arena: &Arena,
    h: SetType,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        SetTypeForm::Bound { .. } => {}
        SetTypeForm::ModuleParam { .. } => {}
        SetTypeForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        SetTypeForm::ReflectedProgramParam { .. } => {}
        SetTypeForm::ProdTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTypeForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTypeForm::LambdaTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTypeForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetTypeForm::AppTerm {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        SetTypeForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        SetTypeForm::PowerSet { set } => {
            field!(set, 0, All | Evaluation);
        }
        SetTypeForm::TypeLift { superset, subset } => {
            field!(superset, 0, All | Evaluation);
            field!(subset, 0, All | Evaluation);
        }
        SetTypeForm::RunStep {
            state_ty,
            result_ty,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
        }
        SetTypeForm::BoxType { program_ty } => {
            field!(program_ty, 0, All | Evaluation);
        }
        SetTypeForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(motive, 1, All | Evaluation);
            field!(on_continue, 0, All | Evaluation);
            field!(on_finish, 0, All | Evaluation);
            field!(scrutinee, 0, All | Head | Evaluation);
        }
        SetTypeForm::IndType { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTypeForm::IndCtor { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTypeForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in cases {
                field!(child, 0, All | Evaluation);
            }
        }
        SetTypeForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in branches {
                field!(child, 0, All | Evaluation);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_set_kind(
    arena: &Arena,
    h: SetKind,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        SetKindForm::Base => {}
        SetKindForm::ProdTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetKindForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        SetKindForm::IndType { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        SetKindForm::ModuleParam { .. } => {}
        SetKindForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_prop_term(
    arena: &Arena,
    h: PropTerm,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        PropTermForm::Bound { .. } => {}
        PropTermForm::ModuleParam { .. } => {}
        PropTermForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        PropTermForm::LambdaTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTermForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTermForm::AppTerm {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        PropTermForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        PropTermForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(motive, 1, All | Evaluation);
            field!(on_continue, 0, All | Evaluation);
            field!(on_finish, 0, All | Evaluation);
            field!(scrutinee, 0, All | Head | Evaluation);
        }
        PropTermForm::IdRefl { element } => {
            field!(element, 0, All | Evaluation);
        }
        PropTermForm::ExistsIntro { element, set } => {
            field!(element, 0, All | Evaluation);
            field!(set, 0, All | Evaluation);
        }
        PropTermForm::SubsetElim {
            element,
            subset,
            superset,
        } => {
            field!(element, 0, All | Evaluation);
            field!(subset, 0, All | Evaluation);
            field!(superset, 0, All | Evaluation);
        }
        PropTermForm::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => {
            field!(left, 0, All | Evaluation);
            field!(right, 0, All | Evaluation);
            field!(ty, 0, All | Evaluation);
            field!(predicate, 1, All | Evaluation);
            field!(base, 0, All | Evaluation);
            field!(equality, 0, All | Evaluation);
        }
        PropTermForm::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => {
            field!(domain, 0, All | Evaluation);
            field!(proposition, 0, All | Evaluation);
            field!(map, 0, All | Evaluation);
            field!(existence, 0, All | Evaluation);
        }
        PropTermForm::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            field!(func, 0, All | Evaluation);
            field!(domain, 0, All | Evaluation);
            field!(codomain, 0, All | Evaluation);
            field!(element, 0, All | Evaluation);
            field!(existence, 0, All | Evaluation);
            field!(uniqueness, 0, All | Evaluation);
        }
        PropTermForm::SetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => {
            field!(left, 0, All | Evaluation);
            field!(right, 0, All | Evaluation);
            field!(left_to_right, 0, All | Evaluation);
            field!(right_to_left, 0, All | Evaluation);
        }
        PropTermForm::FunExt {
            left,
            right,
            pointwise,
        } => {
            field!(left, 0, All | Evaluation);
            field!(right, 0, All | Evaluation);
            field!(pointwise, 0, All | Evaluation);
        }
        PropTermForm::ClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => {
            field!(domain, 0, All | Evaluation);
            field!(family, 0, All | Evaluation);
            field!(inhabited, 0, All | Evaluation);
        }
        PropTermForm::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(step, 0, All | Evaluation);
            field!(state, 0, All | Evaluation);
            field!(predecessors, 0, All | Evaluation);
        }
        PropTermForm::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(step, 0, All | Evaluation);
            field!(from, 0, All | Evaluation);
            field!(to, 0, All | Evaluation);
            field!(accessibility, 0, All | Evaluation);
            field!(transition, 0, All | Evaluation);
        }
        PropTermForm::IndCtor { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        PropTermForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in cases {
                field!(child, 0, All | Evaluation);
            }
        }
        PropTermForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in branches {
                field!(child, 0, All | Evaluation);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_prop_type(
    arena: &Arena,
    h: PropType,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        PropTypeForm::Bound { .. } => {}
        PropTypeForm::ModuleParam { .. } => {}
        PropTypeForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        PropTypeForm::ProdTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTypeForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTypeForm::LambdaTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTypeForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropTypeForm::AppTerm {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        PropTypeForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
        PropTypeForm::Pred {
            superset,
            subset,
            element,
        } => {
            field!(superset, 0, All | Evaluation);
            field!(subset, 0, All | Head | Evaluation);
            field!(element, 0, All | Evaluation);
        }
        PropTypeForm::Equal { left, right } => {
            field!(left, 0, All | Evaluation);
            field!(right, 0, All | Evaluation);
        }
        PropTypeForm::Exists { set } => {
            field!(set, 0, All | Evaluation);
        }
        PropTypeForm::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(step, 0, All | Evaluation);
            field!(state, 0, All | Evaluation);
        }
        PropTypeForm::Recursor {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
            field!(motive, 1, All | Evaluation);
            field!(on_continue, 0, All | Evaluation);
            field!(on_finish, 0, All | Evaluation);
            field!(scrutinee, 0, All | Head | Evaluation);
        }
        PropTypeForm::IndType { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        PropTypeForm::IndCtor { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        PropTypeForm::IndElim {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in cases {
                field!(child, 0, All | Evaluation);
            }
        }
        PropTypeForm::Case {
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            ..
        } => {
            field!(scrutinee, 0, All | Head | Evaluation);
            for (i, child) in motive_domains.iter_mut().enumerate() {
                field!(child, i, All | Evaluation);
            }
            field!(motive_body, motive_vars.len(), All | Evaluation);
            for child in branches {
                field!(child, 0, All | Evaluation);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_prop_kind(
    arena: &Arena,
    h: PropKind,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,false;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        PropKindForm::Base => {}
        PropKindForm::ProdTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropKindForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        PropKindForm::IndType { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        PropKindForm::ModuleParam { .. } => {}
        PropKindForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_value_term(
    arena: &Arena,
    h: ValueTerm,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ValueTermForm::Bound { .. } => {}
        ValueTermForm::ModuleParam { .. } => {}
        ValueTermForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        ValueTermForm::ThunkValue { computation } => {
            field!(computation, 0, All);
        }
        ValueTermForm::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            field!(state_ty, 0, All);
            field!(result_ty, 0, All);
            field!(next, 0, All);
        }
        ValueTermForm::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            field!(state_ty, 0, All);
            field!(result_ty, 0, All);
            field!(output, 0, All);
        }
        ValueTermForm::InductiveConstructor {
            parameters, fields, ..
        } => {
            for child in parameters {
                field!(child, 0, All);
            }
            for child in fields {
                field!(child, 0, All);
            }
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_value_type(
    arena: &Arena,
    h: ValueType,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ValueTypeForm::Bound { .. } => {}
        ValueTypeForm::ModuleParam { .. } => {}
        ValueTypeForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        ValueTypeForm::Thunk { computation_ty } => {
            field!(computation_ty, 0, All | Evaluation);
        }
        ValueTypeForm::RunStep {
            state_ty,
            result_ty,
        } => {
            field!(state_ty, 0, All | Evaluation);
            field!(result_ty, 0, All | Evaluation);
        }
        ValueTypeForm::Inductive { parameters, .. } => {
            for child in parameters {
                field!(child, 0, All | Evaluation);
            }
        }
        ValueTypeForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        ValueTypeForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_value_kind(
    arena: &Arena,
    h: ValueKind,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ValueKindForm::Base => {}
        ValueKindForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_computation_term(
    arena: &Arena,
    h: ComputationTerm,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ComputationTermForm::ModuleParam { .. } => {}
        ComputationTermForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        ComputationTermForm::Return { value } => {
            field!(value, 0, All);
        }
        ComputationTermForm::Force { value } => {
            field!(value, 0, All);
        }
        ComputationTermForm::LambdaTerm { domain, body, .. } => {
            field!(domain, 0, All);
            field!(body, 1, All);
        }
        ComputationTermForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All);
            field!(body, 1, All);
        }
        ComputationTermForm::AppTerm {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All);
        }
        ComputationTermForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All);
        }
        ComputationTermForm::Sequence {
            value_ty,
            computation,
            body,
            ..
        } => {
            field!(value_ty, 0, All);
            field!(computation, 0, All | Head | Evaluation);
            field!(body, 1, All);
        }
        ComputationTermForm::ValueLet {
            value_ty,
            value,
            body,
            ..
        } => {
            field!(value_ty, 0, All);
            field!(value, 0, All);
            field!(body, 1, All);
        }
        ComputationTermForm::Case {
            binders,
            result_ty,
            scrutinee,
            branches,
            ..
        } => {
            field!(result_ty, 0, All);
            field!(scrutinee, 0, All | Head);
            for (i, child) in branches.iter_mut().enumerate() {
                field!(child, binders.get(i).map_or(0, Vec::len), All);
            }
        }
        ComputationTermForm::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            field!(state_ty, 0, All);
            field!(result_ty, 0, All);
            field!(step, 0, All);
            field!(initial, 0, All);
            field!(accessibility, 0, All);
        }
        ComputationTermForm::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => {
            field!(state_ty, 0, All);
            field!(result_ty, 0, All);
            field!(step, 0, All);
            field!(initial, 0, All);
            field!(transition, 0, All | Head | Evaluation);
            field!(accessibility, 0, All);
            field!(transition_equality, 0, All);
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_computation_type(
    arena: &Arena,
    h: ComputationType,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ComputationTypeForm::Bound { .. } => {}
        ComputationTypeForm::ModuleParam { .. } => {}
        ComputationTypeForm::Annotated { body, classifier } => {
            field!(body, 0, All | Head | Evaluation);
            if let super::super::environment::Classifier::Expression(ty) = classifier {
                field!(ty, 0, All);
            }
        }
        ComputationTypeForm::ReturnType { value_ty } => {
            field!(value_ty, 0, All | Evaluation);
        }
        ComputationTypeForm::ProdTerm { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        ComputationTypeForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        ComputationTypeForm::LambdaType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
        ComputationTypeForm::AppType {
            function, argument, ..
        } => {
            field!(function, 0, All | Head | Evaluation);
            field!(argument, 0, All | Evaluation);
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
fn map_computation_kind(
    arena: &Arena,
    h: ComputationKind,
    traversal: Traversal,
    map: &mut dyn FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.read(h.clone());
    let mut node = (*original).clone();
    macro_rules! field { ($slot:expr,$depth:expr,$($mode:pat_param)|+) => { child!(arena,map,traversal,true;$slot,$depth,$($mode)|+); }; }
    match &mut node.form {
        ComputationKindForm::Base => {}
        ComputationKindForm::ProdType { domain, body, .. } => {
            field!(domain, 0, All | Evaluation);
            field!(body, 1, All | Evaluation);
        }
    }
    if *original == node {
        Ok(h.into())
    } else {
        Ok(arena.alloc(node).into())
    }
}
