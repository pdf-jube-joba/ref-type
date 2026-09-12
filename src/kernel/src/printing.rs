//! Bounded diagnostic rendering includes syntax family, sort, and rule labels.
use super::{environment::Environment, structure, syntax::*};
pub fn format_expression(env: &Environment, e: impl Into<Expression>) -> String {
    fn render(arena: &Arena, e: Expression, depth: usize, remaining: &mut usize) -> String {
        if *remaining == 0 {
            return "…".into();
        }
        *remaining -= 1;
        if depth == 0 {
            return format!("{:?}@{:?}", e.family(), arena.sort(e));
        }
        let mut children = vec![];
        structure::visit_children(arena, e, |child, _| {
            children.push(render(arena, child, depth - 1, remaining))
        });
        format!(
            "{}@{:?}({})",
            label(arena, e),
            arena.sort(e),
            children.join("; ")
        )
    }
    render(&env.arena, e.into(), 6, &mut 128)
}
fn label(arena: &Arena, e: Expression) -> String {
    match e {
        Expression::SetTerm(h) => match &arena.read(h).form {
            SetTermForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            SetTermForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            SetTermForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            SetTermForm::ReflectedProgramParam { parameter } => {
                format!("ReflectedProgramParam {{ parameter: {parameter:?} }}")
            }
            SetTermForm::LambdaTerm { rule, var, .. } => {
                format!("LambdaTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTermForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTermForm::AppTerm { rule, .. } => format!("AppTerm {{ rule: {rule:?} }}"),
            SetTermForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
            SetTermForm::Subset { var, .. } => format!("Subset {{ var: {var:?} }}"),
            SetTermForm::SubsetIntro { .. } => "SubsetIntro".into(),
            SetTermForm::Continue { .. } => "Continue".into(),
            SetTermForm::Finish { .. } => "Finish".into(),
            SetTermForm::SetRun { .. } => "SetRun".into(),
            SetTermForm::SetRunCase { .. } => "SetRunCase".into(),
            SetTermForm::Recursor { rule, var, .. } => {
                format!("Recursor {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTermForm::BoxProgram { .. } => "BoxProgram".into(),
            SetTermForm::ForceBox { .. } => "ForceBox".into(),
            SetTermForm::BoxApp { rule, .. } => format!("BoxApp {{ rule: {rule:?} }}"),
            SetTermForm::BoxTypeApp { rule, var, .. } => {
                format!("BoxTypeApp {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTermForm::TakeSet { .. } => "TakeSet".into(),
            SetTermForm::IndCtor {
                inductive,
                constructor,
                ..
            } => format!("IndCtor {{ inductive: {inductive:?}, constructor: {constructor:?} }}"),
            SetTermForm::IndElim {
                inductive,
                motive_vars,
                ..
            } => format!("IndElim {{ inductive: {inductive:?}, motive_vars: {motive_vars:?} }}"),
            SetTermForm::SetCase {
                inductive, binders, ..
            } => format!("SetCase {{ inductive: {inductive:?}, binders: {binders:?} }}"),
        },
        Expression::SetType(h) => match &arena.read(h).form {
            SetTypeForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            SetTypeForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            SetTypeForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            SetTypeForm::ReflectedProgramParam { parameter } => {
                format!("ReflectedProgramParam {{ parameter: {parameter:?} }}")
            }
            SetTypeForm::ProdTerm { rule, var, .. } => {
                format!("ProdTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTypeForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTypeForm::LambdaTerm { rule, var, .. } => {
                format!("LambdaTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTypeForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTypeForm::AppTerm { rule, .. } => format!("AppTerm {{ rule: {rule:?} }}"),
            SetTypeForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
            SetTypeForm::PowerSet { .. } => "PowerSet".into(),
            SetTypeForm::TypeLift { .. } => "TypeLift".into(),
            SetTypeForm::RunStep { .. } => "RunStep".into(),
            SetTypeForm::BoxType { .. } => "BoxType".into(),
            SetTypeForm::Recursor { rule, var, .. } => {
                format!("Recursor {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetTypeForm::IndType { inductive, .. } => {
                format!("IndType {{ inductive: {inductive:?} }}")
            }
            SetTypeForm::IndCtor {
                inductive,
                constructor,
                ..
            } => format!("IndCtor {{ inductive: {inductive:?}, constructor: {constructor:?} }}"),
            SetTypeForm::IndElim {
                inductive,
                motive_vars,
                ..
            } => format!("IndElim {{ inductive: {inductive:?}, motive_vars: {motive_vars:?} }}"),
        },
        Expression::SetKind(h) => match &arena.read(h).form {
            SetKindForm::Base => "Base".into(),
            SetKindForm::ProdTerm { rule, var, .. } => {
                format!("ProdTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetKindForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
            SetKindForm::IndType { inductive, .. } => {
                format!("IndType {{ inductive: {inductive:?} }}")
            }
            SetKindForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            SetKindForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
        },
        Expression::PropTerm(h) => match &arena.read(h).form {
            PropTermForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            PropTermForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            PropTermForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            PropTermForm::LambdaTerm { rule, var, .. } => {
                format!("LambdaTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTermForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTermForm::AppTerm { rule, .. } => format!("AppTerm {{ rule: {rule:?} }}"),
            PropTermForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
            PropTermForm::Recursor { rule, var, .. } => {
                format!("Recursor {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTermForm::IdRefl { .. } => "IdRefl".into(),
            PropTermForm::ExistsIntro { .. } => "ExistsIntro".into(),
            PropTermForm::SubsetElim { .. } => "SubsetElim".into(),
            PropTermForm::IdElim { var, .. } => format!("IdElim {{ var: {var:?} }}"),
            PropTermForm::TakeProp { .. } => "TakeProp".into(),
            PropTermForm::TakeEq { .. } => "TakeEq".into(),
            PropTermForm::SetExt { .. } => "SetExt".into(),
            PropTermForm::FunExt { .. } => "FunExt".into(),
            PropTermForm::ClassicalIndefiniteChoice { .. } => "ClassicalIndefiniteChoice".into(),
            PropTermForm::AccIntro { .. } => "AccIntro".into(),
            PropTermForm::AccDescent { .. } => "AccDescent".into(),
            PropTermForm::IndCtor {
                inductive,
                constructor,
                ..
            } => format!("IndCtor {{ inductive: {inductive:?}, constructor: {constructor:?} }}"),
            PropTermForm::IndElim {
                inductive,
                motive_vars,
                ..
            } => format!("IndElim {{ inductive: {inductive:?}, motive_vars: {motive_vars:?} }}"),
        },
        Expression::PropType(h) => match &arena.read(h).form {
            PropTypeForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            PropTypeForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            PropTypeForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            PropTypeForm::ProdTerm { rule, var, .. } => {
                format!("ProdTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTypeForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTypeForm::LambdaTerm { rule, var, .. } => {
                format!("LambdaTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTypeForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTypeForm::AppTerm { rule, .. } => format!("AppTerm {{ rule: {rule:?} }}"),
            PropTypeForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
            PropTypeForm::Pred { .. } => "Pred".into(),
            PropTypeForm::Equal { .. } => "Equal".into(),
            PropTypeForm::Exists { .. } => "Exists".into(),
            PropTypeForm::Acc { .. } => "Acc".into(),
            PropTypeForm::Recursor { rule, var, .. } => {
                format!("Recursor {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropTypeForm::IndType { inductive, .. } => {
                format!("IndType {{ inductive: {inductive:?} }}")
            }
            PropTypeForm::IndCtor {
                inductive,
                constructor,
                ..
            } => format!("IndCtor {{ inductive: {inductive:?}, constructor: {constructor:?} }}"),
            PropTypeForm::IndElim {
                inductive,
                motive_vars,
                ..
            } => format!("IndElim {{ inductive: {inductive:?}, motive_vars: {motive_vars:?} }}"),
        },
        Expression::PropKind(h) => match &arena.read(h).form {
            PropKindForm::Base => "Base".into(),
            PropKindForm::ProdTerm { rule, var, .. } => {
                format!("ProdTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropKindForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
            PropKindForm::IndType { inductive, .. } => {
                format!("IndType {{ inductive: {inductive:?} }}")
            }
            PropKindForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            PropKindForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
        },
        Expression::ValueTerm(h) => match &arena.read(h).form {
            ValueTermForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            ValueTermForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            ValueTermForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            ValueTermForm::ThunkValue { .. } => "ThunkValue".into(),
            ValueTermForm::Continue { .. } => "Continue".into(),
            ValueTermForm::Finish { .. } => "Finish".into(),
            ValueTermForm::InductiveConstructor {
                inductive,
                constructor,
                ..
            } => format!(
                "InductiveConstructor {{ inductive: {inductive:?}, constructor: {constructor:?} }}"
            ),
        },
        Expression::ValueType(h) => match &arena.read(h).form {
            ValueTypeForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            ValueTypeForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            ValueTypeForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            ValueTypeForm::Thunk { .. } => "Thunk".into(),
            ValueTypeForm::RunStep { .. } => "RunStep".into(),
            ValueTypeForm::Inductive { inductive, .. } => {
                format!("Inductive {{ inductive: {inductive:?} }}")
            }
            ValueTypeForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            ValueTypeForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
        },
        Expression::ValueKind(h) => match &arena.read(h).form {
            ValueKindForm::Base => "Base".into(),
            ValueKindForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
        },
        Expression::ComputationTerm(h) => match &arena.read(h).form {
            ComputationTermForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            ComputationTermForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            ComputationTermForm::Return { .. } => "Return".into(),
            ComputationTermForm::Force { .. } => "Force".into(),
            ComputationTermForm::LambdaTerm { rule, var, .. } => {
                format!("LambdaTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            ComputationTermForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            ComputationTermForm::AppTerm { rule, .. } => format!("AppTerm {{ rule: {rule:?} }}"),
            ComputationTermForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
            ComputationTermForm::Sequence { var, .. } => format!("Sequence {{ var: {var:?} }}"),
            ComputationTermForm::ValueLet { var, .. } => format!("ValueLet {{ var: {var:?} }}"),
            ComputationTermForm::Case {
                inductive, binders, ..
            } => format!("Case {{ inductive: {inductive:?}, binders: {binders:?} }}"),
            ComputationTermForm::Run { .. } => "Run".into(),
            ComputationTermForm::RunCase { .. } => "RunCase".into(),
        },
        Expression::ComputationType(h) => match &arena.read(h).form {
            ComputationTypeForm::Bound { index } => format!("Bound {{ index: {index:?} }}"),
            ComputationTypeForm::ModuleParam { parameter } => {
                format!("ModuleParam {{ parameter: {parameter:?} }}")
            }
            ComputationTypeForm::Constant { definition } => {
                format!("Constant {{ definition: {definition:?} }}")
            }
            ComputationTypeForm::ReturnType { .. } => "ReturnType".into(),
            ComputationTypeForm::ProdTerm { rule, var, .. } => {
                format!("ProdTerm {{ rule: {rule:?}, var: {var:?} }}")
            }
            ComputationTypeForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
            ComputationTypeForm::LambdaType { rule, var, .. } => {
                format!("LambdaType {{ rule: {rule:?}, var: {var:?} }}")
            }
            ComputationTypeForm::AppType { rule, .. } => format!("AppType {{ rule: {rule:?} }}"),
        },
        Expression::ComputationKind(h) => match &arena.read(h).form {
            ComputationKindForm::Base => "Base".into(),
            ComputationKindForm::ProdType { rule, var, .. } => {
                format!("ProdType {{ rule: {rule:?}, var: {var:?} }}")
            }
        },
    }
}
