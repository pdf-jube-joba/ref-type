//! Declaration sugar expressed using ordinary declarations and lexical scopes.
use crate::{sort::Sort, syntax::*};

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
fn at(name: &Identifier, field: &str) -> SExp {
    access(member(name, field), vec![])
}
fn reflected(name: &Identifier, field: &str) -> SExp {
    let mut name = member(name, field);
    name.0.push('^');
    access(name, vec![])
}
fn bind(name: Identifier, ty: SExp) -> RightBind {
    RightBind {
        vars: vec![name],
        ty: Box::new(ty),
    }
}
fn definition(name: Identifier, ty: SExp, body: SExp) -> ModuleItem {
    ModuleItem::Definition {
        owner: None,
        name,
        binders: vec![],
        ty,
        body,
    }
}
fn template(name: Identifier, body: SExp) -> ModuleItem {
    ModuleItem::UserMacro {
        name,
        before: vec![],
        after: body,
    }
}
fn app(func: SExp, arg: SExp) -> SExp {
    SExp::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

pub(crate) fn correspondence_type(name: &Identifier, ty: SExp) -> ModuleItem {
    template(member(name, "Type"), ty)
}
pub(crate) fn correspondence_field(name: &Identifier, field: &str, body: SExp) -> ModuleItem {
    let ty = match field {
        "program" => at(name, "Type"),
        "set" => reflected(name, "Type"),
        "coherence" => SExp::Equal {
            left: Box::new(reflected(name, "program")),
            right: Box::new(at(name, "set")),
        },
        _ => unreachable!(),
    };
    definition(member(name, field), ty, body)
}
pub(crate) fn machine_field(name: &Identifier, field: &str, body: SExp) -> ModuleItem {
    let ty = match field {
        "State" | "Output" => return template(member(name, field), body),
        "step" => SExp::ThunkType {
            computation_ty: Box::new(SExp::ComputationFunction {
                domain: Box::new(at(name, "State")),
                codomain: Box::new(SExp::ReturnType {
                    value_ty: Box::new(SExp::RunStep {
                        state_ty: Box::new(at(name, "State")),
                        result_ty: Box::new(at(name, "Output")),
                    }),
                }),
            }),
        },
        "terminates" => {
            let x = Identifier("<machine-state>".into());
            SExp::Prod {
                bind: Bind::Named(bind(x.clone(), reflected(name, "State"))),
                body: Box::new(termination(
                    reflected(name, "State"),
                    reflected(name, "Output"),
                    reflected(name, "step"),
                    access(x, vec![]),
                )),
            }
        }
        _ => unreachable!(),
    };
    definition(member(name, field), ty, body)
}
pub(crate) fn machine_runs(name: &Identifier) -> Vec<ModuleItem> {
    let x = Identifier("<machine-state>".into());
    let state = access(x.clone(), vec![]);
    let ty = SExp::ComputationFunction {
        domain: Box::new(at(name, "State")),
        codomain: Box::new(SExp::ReturnType {
            value_ty: Box::new(at(name, "Output")),
        }),
    };
    vec![
        definition(
            member(name, "run"),
            ty.clone(),
            SExp::ComputationLam {
                var: x,
                value_ty: Box::new(at(name, "State")),
                body: Box::new(SExp::Run {
                    state_ty: Box::new(at(name, "State")),
                    result_ty: Box::new(at(name, "Output")),
                    step: Box::new(at(name, "step")),
                    initial: Box::new(state.clone()),
                    accessibility: Box::new(app(at(name, "terminates"), state)),
                }),
            },
        ),
        definition(
            member(name, "runbox"),
            SExp::BoxType {
                program_ty: Box::new(ty.clone()),
            },
            SExp::BoxProgram {
                program_ty: Box::new(ty),
                program: Box::new(at(name, "run")),
            },
        ),
    ]
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
    let subset = access(name.clone(), arguments.clone());
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
    // Parameterized aliases are necessary for bracket application. Monomorphic
    // expressions remain ordinary checked definitions.
    let declaration = |name, ty, body| {
        if parameters.is_empty() {
            definition(name, ty, body)
        } else {
            ModuleItem::Alias {
                name,
                parameters: parameters.clone(),
                ty,
                body,
            }
        }
    };
    let items = vec![
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
            name.clone(),
            SExp::PowerSet {
                set: Box::new(raw.clone()),
            },
            SExp::SubSet {
                var: r.clone(),
                set: Box::new(raw.clone()),
                predicate: Box::new(law.clone()),
            },
        ),
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
    let mut exports: Vec<_> = ["Raw", "Law", "Set", "raw", "law"]
        .into_iter()
        .map(|field| member(&name, field))
        .collect();
    exports.push(name);
    ModuleItem::Scoped { exports, items }
}

pub(crate) fn structure_literal(
    access: LocalAccess,
    parameters: Vec<SExp>,
    fields: Vec<(Identifier, SExp)>,
    laws: Vec<(Identifier, SExp)>,
) -> SExp {
    let member_access = |field: &str| match &access {
        LocalAccess::Current { span, access } => LocalAccess::Current {
            span: *span,
            access: member(access, field),
        },
        LocalAccess::Named {
            span,
            access,
            child,
        } => LocalAccess::Named {
            span: *span,
            access: access.clone(),
            child: member(child, field),
        },
    };
    let raw_access = member_access("Raw");
    let law_access = member_access("Law");
    let raw = SExp::AccessPath {
        access: raw_access.clone(),
        parameters: parameters.clone(),
    };
    let r = Identifier("<structure-literal>".into());
    let value = self::access(r.clone(), vec![]);
    let mut law_arguments = parameters.clone();
    law_arguments.push(value.clone());
    SExp::Where {
        clauses: vec![(
            r,
            raw.clone(),
            SExp::RecordTypeCtor {
                access: raw_access,
                parameters: parameters.clone(),
                fields,
            },
        )],
        exp: Box::new(SExp::SubsetIntro {
            superset: Box::new(raw),
            subset: Box::new(SExp::AccessPath { access, parameters }),
            element: Box::new(value),
            proof: Box::new(SExp::RecordTypeCtor {
                access: law_access,
                parameters: law_arguments,
                fields: laws,
            }),
        }),
        span: None,
    }
}

// Expand the logical termination condition without introducing a syntax node.
fn termination(state_ty: SExp, result_ty: SExp, step: SExp, state: SExp) -> SExp {
    fn pi(name: &str, ty: SExp, body: SExp) -> SExp {
        SExp::Prod {
            bind: Bind::Named(bind(Identifier(name.into()), ty)),
            body: Box::new(body),
        }
    }
    fn lam(name: &str, ty: SExp, body: SExp) -> SExp {
        SExp::Lam {
            bind: Bind::Named(bind(Identifier(name.into()), ty)),
            body: Box::new(body),
        }
    }
    fn var(name: &str) -> SExp {
        access(Identifier(name.into()), vec![])
    }
    let prop = SExp::Sort(Sort::Prop);
    let truth = pi(
        "<truth>",
        prop.clone(),
        pi("<proof>", var("<truth>"), var("<truth>")),
    );
    let ready = SExp::SetStepMatch {
        state_ty: Box::new(state_ty.clone()),
        result_ty: Box::new(result_ty.clone()),
        motive: Box::new(lam(
            "<transition>",
            SExp::RunStep {
                state_ty: Box::new(state_ty.clone()),
                result_ty: Box::new(result_ty.clone()),
            },
            prop.clone(),
        )),
        on_continue: Box::new(lam(
            "<next-state>",
            state_ty.clone(),
            app(var("<predicate>"), var("<next-state>")),
        )),
        on_finish: Box::new(lam("<output>", result_ty, truth)),
    };
    pi(
        "<predicate>",
        pi("<domain>", state_ty.clone(), prop),
        pi(
            "<closed>",
            pi(
                "<state>",
                state_ty,
                pi(
                    "<next>",
                    app(ready, app(step, var("<state>"))),
                    app(var("<predicate>"), var("<state>")),
                ),
            ),
            app(var("<predicate>"), state),
        ),
    )
}
