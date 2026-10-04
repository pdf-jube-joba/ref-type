//! Declaration sugar expressed using ordinary declarations and lexical scopes.
use crate::hir::*;
use syntax::sort::Sort;

fn internal_name(name: &Identifier, field: &str) -> Identifier {
    Identifier(format!("<structure:{}:{field}>", name.0))
}
fn access(name: Identifier, parameters: Vec<SExp>) -> SExp {
    SExp::AccessPath {
        access: LocalAccess::Current {
            span: SourceSpan::default(),
            access: name,
        },
        parameters,
    }
}
fn bind(name: Identifier, ty: SExp) -> RightBind {
    RightBind {
        vars: vec![name],
        ty: Box::new(ty),
    }
}

pub(super) fn structure(
    name: Identifier,
    parameters: Vec<RightBind>,
    sort: Sort,
    fields: Vec<(Identifier, SExp)>,
    laws: Vec<(Identifier, SExp)>,
) -> Vec<ModuleItem> {
    let arguments: Vec<_> = parameters
        .iter()
        .flat_map(|b| &b.vars)
        .map(|v| access(v.clone(), vec![]))
        .collect();
    let raw = access(internal_name(&name, "data"), arguments.clone());
    let r = Identifier("<structure-record>".into());
    let value = access(r.clone(), vec![]);
    let mut law_arguments = arguments.clone();
    law_arguments.push(value.clone());
    let law = access(internal_name(&name, "laws"), law_arguments);
    // Bind data field names to projections in each law's type. The resolver
    // then handles ordinary shadowing and dependencies on earlier law fields.
    let clauses: Vec<_> = fields
        .iter()
        .map(|(field, ty)| {
            (
                field.clone(),
                ty.clone(),
                SExp::InferredProjection {
                    value: Box::new(value.clone()),
                    field: Identifier(field.0.clone()),
                    span: SourceSpan::default(),
                },
            )
        })
        .collect();
    let laws = laws
        .into_iter()
        .map(|(field, ty)| {
            (
                field,
                SExp::Where {
                    exp: Box::new(ty),
                    clauses: clauses.clone(),
                    span: None,
                },
            )
        })
        .collect();
    let mut law_parameters = parameters.clone();
    law_parameters.push(bind(r.clone(), raw.clone()));
    vec![
        ModuleItem::Record {
            type_name: internal_name(&name, "data"),
            parameters: parameters.clone(),
            kind: InductiveKind::Pts(sort),
            fields,
        },
        ModuleItem::Record {
            type_name: internal_name(&name, "laws"),
            parameters: law_parameters,
            kind: InductiveKind::Pts(Sort::Prop),
            fields: laws,
        },
        ModuleItem::Definition {
            owner: None,
            name,
            binders: parameters,
            ty: SExp::Sort(sort),
            body: SExp::TypeLift {
                superset: Box::new(raw.clone()),
                subset: Box::new(SExp::SubSet {
                    var: r,
                    set: Box::new(raw),
                    predicate: Box::new(law),
                }),
            },
        },
    ]
}
