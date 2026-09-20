//! Views of rule operands shared by several typed syntax families.
use super::*;
#[derive(Clone)]
pub(crate) struct Product {
    pub rule: ProductRule,
    pub var: SymbolId,
    pub domain: Expression,
    pub body: Expression,
}
#[derive(Clone)]
pub(crate) struct Application {
    pub function: Expression,
    pub argument: Expression,
}
pub(crate) fn bound_index(arena: &Arena, e: Expression) -> Option<usize> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::ValueTerm(h) => match arena.get(h.clone()).form {
            ValueTermForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::ValueType(h) => match arena.get(h.clone()).form {
            ValueTypeForm::Bound { index } => Some(index),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::Bound { index } => Some(index),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn annotation(
    arena: &Arena,
    e: Expression,
) -> Option<(Expression, super::super::environment::Classifier)> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::SetKind(h) => match arena.get(h.clone()).form {
            SetKindForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::PropKind(h) => match arena.get(h.clone()).form {
            PropKindForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::ValueTerm(h) => match arena.get(h.clone()).form {
            ValueTermForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::ValueType(h) => match arena.get(h.clone()).form {
            ValueTypeForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::ComputationTerm(h) => match arena.get(h.clone()).form {
            ComputationTermForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::Annotated { body, classifier } => Some((body.into(), classifier)),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn module_parameter(arena: &Arena, e: Expression) -> Option<ModuleParamId> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::SetKind(h) => match arena.get(h.clone()).form {
            SetKindForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::PropKind(h) => match arena.get(h.clone()).form {
            PropKindForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::ValueTerm(h) => match arena.get(h.clone()).form {
            ValueTermForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::ValueType(h) => match arena.get(h.clone()).form {
            ValueTypeForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::ComputationTerm(h) => match arena.get(h.clone()).form {
            ComputationTermForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::ModuleParam { parameter } => Some(parameter),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn reflected_parameter(arena: &Arena, e: Expression) -> Option<ModuleParamId> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::ReflectedProgramParam { parameter } => Some(parameter),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::ReflectedProgramParam { parameter } => Some(parameter),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn inductive_id(arena: &Arena, e: Expression) -> Option<InductiveId> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::IndCtor { inductive, .. } => Some(inductive),
            SetTermForm::IndElim { inductive, .. } | SetTermForm::Case { inductive, .. } => {
                Some(inductive)
            }
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::IndType { inductive, .. } => Some(inductive),
            SetTypeForm::IndCtor { inductive, .. } => Some(inductive),
            SetTypeForm::IndElim { inductive, .. } | SetTypeForm::Case { inductive, .. } => {
                Some(inductive)
            }
            _ => None,
        },
        Expression::SetKind(h) => match arena.get(h.clone()).form {
            SetKindForm::IndType { inductive, .. } => Some(inductive),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::IndCtor { inductive, .. } => Some(inductive),
            PropTermForm::IndElim { inductive, .. } | PropTermForm::Case { inductive, .. } => {
                Some(inductive)
            }
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::IndType { inductive, .. } => Some(inductive),
            PropTypeForm::IndCtor { inductive, .. } => Some(inductive),
            PropTypeForm::IndElim { inductive, .. } | PropTypeForm::Case { inductive, .. } => {
                Some(inductive)
            }
            _ => None,
        },
        Expression::PropKind(h) => match arena.get(h.clone()).form {
            PropKindForm::IndType { inductive, .. } => Some(inductive),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn inductive_type(
    arena: &Arena,
    e: Expression,
) -> Option<(InductiveId, Vec<LogicalArgument>)> {
    match e {
        Expression::SetType(h) => match &arena.read(h.clone()).form {
            SetTypeForm::IndType {
                inductive,
                parameters,
            } => Some((*inductive, parameters.clone())),
            _ => None,
        },
        Expression::SetKind(h) => match &arena.read(h.clone()).form {
            SetKindForm::IndType {
                inductive,
                parameters,
            } => Some((*inductive, parameters.clone())),
            _ => None,
        },
        Expression::PropType(h) => match &arena.read(h.clone()).form {
            PropTypeForm::IndType {
                inductive,
                parameters,
            } => Some((*inductive, parameters.clone())),
            _ => None,
        },
        Expression::PropKind(h) => match &arena.read(h.clone()).form {
            PropKindForm::IndType {
                inductive,
                parameters,
            } => Some((*inductive, parameters.clone())),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn inductive_constructor(
    arena: &Arena,
    e: Expression,
) -> Option<(InductiveId, usize, Vec<LogicalArgument>)> {
    match e {
        Expression::SetTerm(h) => match &arena.read(h.clone()).form {
            SetTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => Some((*inductive, *constructor, parameters.clone())),
            _ => None,
        },
        Expression::SetType(h) => match &arena.read(h.clone()).form {
            SetTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => Some((*inductive, *constructor, parameters.clone())),
            _ => None,
        },
        Expression::PropTerm(h) => match &arena.read(h.clone()).form {
            PropTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => Some((*inductive, *constructor, parameters.clone())),
            _ => None,
        },
        Expression::PropType(h) => match &arena.read(h.clone()).form {
            PropTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => Some((*inductive, *constructor, parameters.clone())),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn product(arena: &Arena, e: Expression) -> Option<Product> {
    match e {
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            SetTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::SetKind(h) => match arena.get(h.clone()).form {
            SetKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            SetKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            PropTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::PropKind(h) => match arena.get(h.clone()).form {
            PropKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            PropKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ValueKind(h) => match arena.get(h.clone()).form {
            ValueKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            ComputationTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ComputationKind(h) => match arena.get(h.clone()).form {
            ComputationKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn lambda(arena: &Arena, e: Expression) -> Option<Product> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            SetTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            SetTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            PropTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            PropTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ValueType(h) => match arena.get(h.clone()).form {
            ValueTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ComputationTerm(h) => match arena.get(h.clone()).form {
            ComputationTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            ComputationTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => Some(Product {
                rule,
                var,
                domain: domain.into(),
                body: body.into(),
            }),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn application(arena: &Arena, e: Expression) -> Option<Application> {
    match e {
        Expression::SetTerm(h) => match arena.get(h.clone()).form {
            SetTermForm::AppTerm {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            SetTermForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::AppTerm {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            SetTypeForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::PropTerm(h) => match arena.get(h.clone()).form {
            PropTermForm::AppTerm {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            PropTermForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::PropType(h) => match arena.get(h.clone()).form {
            PropTypeForm::AppTerm {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            PropTypeForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::ValueType(h) => match arena.get(h.clone()).form {
            ValueTypeForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::ComputationTerm(h) => match arena.get(h.clone()).form {
            ComputationTermForm::AppTerm {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            ComputationTermForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        Expression::ComputationType(h) => match arena.get(h.clone()).form {
            ComputationTypeForm::AppType {
                function, argument, ..
            } => Some(Application {
                function: function.into(),
                argument: argument.into(),
            }),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn lifted_superset(arena: &Arena, e: Expression) -> Option<SetType> {
    match e {
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::TypeLift { superset, .. } => Some(superset),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn power_set(arena: &Arena, e: Expression) -> Option<SetType> {
    match e {
        Expression::SetType(h) => match arena.get(h.clone()).form {
            SetTypeForm::PowerSet { set } => Some(set),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn program_inductive(
    arena: &Arena,
    e: Expression,
) -> Option<(ProgramInductiveId, Vec<ProgramType>)> {
    match e {
        Expression::ValueType(h) => match &arena.read(h.clone()).form {
            ValueTypeForm::Inductive {
                inductive,
                parameters,
            } => Some((*inductive, parameters.clone())),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn is_base(arena: &Arena, e: Expression) -> bool {
    match e {
        Expression::SetKind(h) => matches!(arena.read(h.clone()).form, SetKindForm::Base),
        Expression::PropKind(h) => matches!(arena.read(h.clone()).form, PropKindForm::Base),
        Expression::ValueKind(h) => matches!(arena.read(h.clone()).form, ValueKindForm::Base),
        Expression::ComputationKind(h) => {
            matches!(arena.read(h.clone()).form, ComputationKindForm::Base)
        }
        _ => false,
    }
}
pub(crate) fn remap_references(
    arena: &Arena,
    e: Expression,
    inductives: &std::collections::HashMap<InductiveId, InductiveId>,
    datatypes: &std::collections::HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Expression {
    match e {
        Expression::SetTerm(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            match &mut node.form {
                SetTermForm::IndCtor { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                SetTermForm::IndElim { inductive, .. } | SetTermForm::Case { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                SetTermForm::SetCase { inductive, .. } => {
                    *inductive = datatypes.get(inductive).cloned().unwrap_or(*inductive)
                }
                _ => {}
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::SetType(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            match &mut node.form {
                SetTypeForm::IndType { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                SetTypeForm::IndCtor { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                SetTypeForm::IndElim { inductive, .. } | SetTypeForm::Case { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                _ => {}
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::SetKind(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            if let SetKindForm::IndType { inductive, .. } = &mut node.form {
                *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::PropTerm(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            match &mut node.form {
                PropTermForm::IndCtor { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                PropTermForm::IndElim { inductive, .. } | PropTermForm::Case { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                _ => {}
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::PropType(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            match &mut node.form {
                PropTypeForm::IndType { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                PropTypeForm::IndCtor { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                PropTypeForm::IndElim { inductive, .. } | PropTypeForm::Case { inductive, .. } => {
                    *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
                }
                _ => {}
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::PropKind(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            if let PropKindForm::IndType { inductive, .. } = &mut node.form {
                *inductive = inductives.get(inductive).cloned().unwrap_or(*inductive)
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::ValueTerm(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            if let ValueTermForm::InductiveConstructor { inductive, .. } = &mut node.form {
                *inductive = datatypes.get(inductive).cloned().unwrap_or(*inductive)
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::ValueType(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            if let ValueTypeForm::Inductive { inductive, .. } = &mut node.form {
                *inductive = datatypes.get(inductive).cloned().unwrap_or(*inductive)
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::ValueKind(_) | Expression::ComputationKind(_) => e,
        Expression::ComputationTerm(h) => {
            let original = arena.read(h.clone());
            let mut node = (*original).clone();
            if let ComputationTermForm::Case { inductive, .. } = &mut node.form {
                *inductive = datatypes.get(inductive).cloned().unwrap_or(*inductive)
            }
            if *original == node {
                h.into()
            } else {
                arena.alloc(node).into()
            }
        }
        Expression::ComputationType(_) => e,
    }
}
