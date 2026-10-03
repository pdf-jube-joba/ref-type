//! Declaration sugar expressed using ordinary declarations and lexical scopes.
use crate::hir::*;
use syntax::sort::Sort;

pub(crate) fn member(name: &Identifier, field: &str) -> Identifier {
    Identifier(format!("{}::[{field}]", name.0))
}
pub(crate) fn access(name: Identifier, parameters: Vec<SExp>) -> SExp {
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

pub(crate) fn structure(
    name: Identifier,
    parameters: Vec<RightBind>,
    sort: Sort,
    fields: Vec<(Identifier, SExp)>,
    laws: Vec<(Identifier, SExp)>,
) -> ModuleItem {
    let arguments: Vec<_> = parameters
        .iter()
        .flat_map(|b| &b.vars)
        .map(|v| access(v.clone(), vec![]))
        .collect();
    let raw = access(member(&name, "Raw"), arguments.clone());
    let subset = access(member(&name, "Predicate"), arguments.clone());
    let data_names = fields.iter().map(|(name, _)| name.clone()).collect();
    let law_names = laws.iter().map(|(name, _)| name.clone()).collect();
    let set = SExp::TypeLift {
        superset: Box::new(raw.clone()),
        subset: Box::new(subset.clone()),
    };
    let r = Identifier("<structure-record>".into());
    let value = access(r.clone(), vec![]);
    let mut law_arguments = arguments.clone();
    law_arguments.push(value.clone());
    let law = access(member(&name, "Law"), law_arguments);
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
                    field: field.clone(),
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
    let declaration = |name, ty, body| ModuleItem::Definition {
        owner: None,
        name,
        binders: parameters.clone(),
        ty,
        body,
    };
    let mut items = vec![
        ModuleItem::Record {
            type_name: member(&name, "Raw"),
            parameters: parameters.clone(),
            kind: InductiveKind::Pts(sort),
            fields,
        },
        ModuleItem::Record {
            type_name: member(&name, "Law"),
            parameters: law_parameters,
            kind: InductiveKind::Pts(Sort::Prop),
            fields: laws,
        },
        declaration(
            member(&name, "Predicate"),
            SExp::PowerSet {
                set: Box::new(raw.clone()),
            },
            SExp::SubSet {
                var: r.clone(),
                set: Box::new(raw.clone()),
                predicate: Box::new(law.clone()),
            },
        ),
        declaration(name.clone(), SExp::Sort(sort), set.clone()),
        declaration(member(&name, "Set"), SExp::Sort(sort), set.clone()),
        declaration(
            member(&name, "raw"),
            SExp::Prod {
                bind: Bind::Named(bind(r.clone(), set.clone())),
                body: Box::new(raw.clone()),
            },
            SExp::Lam {
                bind: Bind::Named(bind(r.clone(), set.clone())),
                body: Box::new(value.clone()),
            },
        ),
        declaration(
            member(&name, "law"),
            SExp::Prod {
                bind: Bind::Named(bind(r.clone(), set.clone())),
                body: Box::new(law),
            },
            SExp::Lam {
                bind: Bind::Named(bind(r, set)),
                body: Box::new(SExp::SubsetElim {
                    element: Box::new(value),
                    subset: Box::new(subset),
                    superset: Box::new(raw),
                }),
            },
        ),
    ];
    items.push(ModuleItem::Refinement {
        name: name.clone(),
        fields: data_names,
        laws: law_names,
    });
    let mut exports: Vec<_> = ["Raw", "Law", "Set", "raw", "law", "Predicate"]
        .into_iter()
        .map(|field| member(&name, field))
        .collect();
    exports.push(name);
    ModuleItem::Scoped { exports, items }
}
