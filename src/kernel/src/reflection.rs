//! Structural Program-to-Set reflection, preserving family and level.
use super::{calculus::*, construction as build, environment::*, sort::*, structure, syntax::*};

pub fn reflect_kind(env: &Environment, k: ProgramKind) -> Result<SetKind, String> {
    reflect(env, k.into())?.try_into()
}

pub fn reflect_type(env: &Environment, k: ProgramType) -> Result<SetType, String> {
    reflect(env, k.into())?.try_into()
}

pub fn reflect_term(env: &Environment, k: ProgramTerm) -> Result<SetTerm, String> {
    reflect(env, k.into())?.try_into()
}

pub fn reflect_context(env: &Environment, c: &Context) -> Result<Context, String> {
    c.iter()
        .map(|b| {
            Ok(Binding {
                var: b.var,
                classifier: reflect(env, b.classifier)?,
            })
        })
        .collect()
}

pub fn reflect(env: &Environment, e: Expression) -> Result<Expression, String> {
    let a = &env.arena;
    Ok(match e {
        Expression::ValueTerm(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ValueTermForm::Bound { index } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::Bound { index },
                    })
                    .into(),
                ValueTermForm::ModuleParam { parameter } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::ReflectedProgramParam { parameter },
                    })
                    .into(),
                ValueTermForm::Constant { definition } => {
                    let definition = env
                        .definition(definition)
                        .ok_or("unknown Program definition")?;
                    if let Some(certificate) = definition.certified_reflection {
                        certificate.into()
                    } else {
                        reflect(env, definition.body)?
                    }
                }
                ValueTermForm::ThunkValue { computation } => reflect(env, computation.into())?,
                ValueTermForm::Continue {
                    state_ty,
                    result_ty,
                    next,
                } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::Continue {
                            state_ty: reflect(env, state_ty.into())?.try_into()?,
                            result_ty: reflect(env, result_ty.into())?.try_into()?,
                            next: reflect(env, next.into())?.try_into()?,
                        },
                    })
                    .into(),
                ValueTermForm::Finish {
                    state_ty,
                    result_ty,
                    output,
                } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::Finish {
                            state_ty: reflect(env, state_ty.into())?.try_into()?,
                            result_ty: reflect(env, result_ty.into())?.try_into()?,
                            output: reflect(env, output.into())?.try_into()?,
                        },
                    })
                    .into(),
                ValueTermForm::InductiveConstructor {
                    inductive,
                    constructor,
                    parameters,
                    fields,
                } => {
                    let spec = env.datatype(inductive).ok_or("unknown datatype")?;
                    let parameters = parameters
                        .into_iter()
                        .map(|p| reflect(env, p.into())?.try_into())
                        .collect::<Result<Vec<LogicalArgument>, String>>()?;
                    let mut result = build::inductive_constructor(
                        a,
                        BaseSort::Set(level),
                        Stage::Term,
                        spec.reflected,
                        constructor,
                        parameters,
                    )?;
                    for field in fields {
                        let field = reflect(env, field.into())?;
                        let rule = ProductRule::new(
                            Sort::Base(a.sort(field)),
                            Sort::Base(BaseSort::Set(level)),
                        )?;
                        result = build::apply(a, rule, result, field)?;
                    }
                    result
                }
            }
        }
        Expression::ValueType(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ValueTypeForm::Bound { index } => a
                    .alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::Bound { index },
                    })
                    .into(),
                ValueTypeForm::ModuleParam { parameter } => a
                    .alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::ReflectedProgramParam { parameter },
                    })
                    .into(),
                ValueTypeForm::Constant { definition } => {
                    let definition = env
                        .definition(definition)
                        .ok_or("unknown Program definition")?;
                    if let Some(certificate) = definition.certified_reflection {
                        certificate.into()
                    } else {
                        reflect(env, definition.body)?
                    }
                }
                ValueTypeForm::Thunk { computation_ty } => reflect(env, computation_ty.into())?,
                ValueTypeForm::RunStep {
                    state_ty,
                    result_ty,
                } => a
                    .alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::RunStep {
                            state_ty: reflect(env, state_ty.into())?.try_into()?,
                            result_ty: reflect(env, result_ty.into())?.try_into()?,
                        },
                    })
                    .into(),
                ValueTypeForm::Inductive {
                    inductive,
                    parameters,
                } => {
                    let inductive = env.datatype(inductive).ok_or("unknown datatype")?.reflected;
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::IndType {
                            inductive,
                            parameters: parameters
                                .into_iter()
                                .map(|child| reflect(env, child.into())?.try_into())
                                .collect::<Result<_, String>>()?,
                        },
                    })
                    .into()
                }
                ValueTypeForm::LambdaType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::LambdaType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ValueTypeForm::AppType {
                    rule,
                    function,
                    argument,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::AppType {
                            rule,
                            function: reflect(env, function.into())?.try_into()?,
                            argument: reflect(env, argument.into())?.try_into()?,
                        },
                    })
                    .into()
                }
            }
        }
        Expression::ValueKind(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ValueKindForm::Base => a
                    .alloc(SetKindNode {
                        level,
                        form: SetKindForm::Base,
                    })
                    .into(),
                ValueKindForm::ProdType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetKindNode {
                        level,
                        form: SetKindForm::ProdType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
            }
        }
        Expression::ComputationTerm(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ComputationTermForm::ModuleParam { parameter } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::ReflectedProgramParam { parameter },
                    })
                    .into(),
                ComputationTermForm::Constant { definition } => {
                    let definition = env
                        .definition(definition)
                        .ok_or("unknown Program definition")?;
                    if let Some(certificate) = definition.certified_reflection {
                        certificate.into()
                    } else {
                        reflect(env, definition.body)?
                    }
                }
                ComputationTermForm::Return { value } => reflect(env, value.into())?,
                ComputationTermForm::Force { value } => reflect(env, value.into())?,
                ComputationTermForm::LambdaTerm {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTermNode {
                        level,
                        form: SetTermForm::LambdaTerm {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTermForm::LambdaType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTermNode {
                        level,
                        form: SetTermForm::LambdaType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTermForm::AppTerm {
                    rule,
                    function,
                    argument,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTermNode {
                        level,
                        form: SetTermForm::AppTerm {
                            rule,
                            function: reflect(env, function.into())?.try_into()?,
                            argument: reflect(env, argument.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTermForm::AppType {
                    rule,
                    function,
                    argument,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTermNode {
                        level,
                        form: SetTermForm::AppType {
                            rule,
                            function: reflect(env, function.into())?.try_into()?,
                            argument: reflect(env, argument.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTermForm::Sequence {
                    var,
                    value_ty,
                    computation,
                    body,
                } => {
                    let domain = reflect(env, value_ty.into())?;
                    let argument = reflect(env, computation.into())?;
                    let body = reflect(env, body.into())?;
                    let rule =
                        ProductRule::new(Sort::Base(a.sort(domain)), Sort::Base(a.sort(body)))?;
                    let lambda = build::lambda(a, rule, var, domain, body)?;
                    build::apply(a, rule, lambda, argument)?
                }
                ComputationTermForm::ValueLet {
                    var,
                    value_ty,
                    value,
                    body,
                } => {
                    let domain = reflect(env, value_ty.into())?;
                    let argument = reflect(env, value.into())?;
                    let body = reflect(env, body.into())?;
                    let rule =
                        ProductRule::new(Sort::Base(a.sort(domain)), Sort::Base(a.sort(body)))?;
                    let lambda = build::lambda(a, rule, var, domain, body)?;
                    build::apply(a, rule, lambda, argument)?
                }
                ComputationTermForm::Case {
                    inductive,
                    binders,
                    result_ty,
                    scrutinee,
                    branches,
                } => a
                    .alloc(SetTermNode {
                        level,
                        form: SetTermForm::SetCase {
                            inductive,
                            binders,
                            result_ty: reflect(env, result_ty.into())?.try_into()?,
                            scrutinee: reflect(env, scrutinee.into())?.try_into()?,
                            branches: branches
                                .into_iter()
                                .map(|child| reflect(env, child.into())?.try_into())
                                .collect::<Result<_, String>>()?,
                        },
                    })
                    .into(),
                ComputationTermForm::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                } => {
                    let _ = (state_ty, result_ty, step, initial);
                    return Err("reflecting run requires an accessibility certificate".into());
                }
                ComputationTermForm::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                } => {
                    let _ = (state_ty, result_ty, step, initial, transition);
                    return Err("reflecting run requires an accessibility certificate".into());
                }
            }
        }
        Expression::ComputationType(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ComputationTypeForm::Bound { index } => a
                    .alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::Bound { index },
                    })
                    .into(),
                ComputationTypeForm::ModuleParam { parameter } => a
                    .alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::ReflectedProgramParam { parameter },
                    })
                    .into(),
                ComputationTypeForm::Constant { definition } => {
                    let definition = env
                        .definition(definition)
                        .ok_or("unknown Program definition")?;
                    if let Some(certificate) = definition.certified_reflection {
                        certificate.into()
                    } else {
                        reflect(env, definition.body)?
                    }
                }
                ComputationTypeForm::ReturnType { value_ty } => reflect(env, value_ty.into())?,
                ComputationTypeForm::ProdTerm {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::ProdTerm {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTypeForm::ProdType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::ProdType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTypeForm::LambdaType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::LambdaType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
                ComputationTypeForm::AppType {
                    rule,
                    function,
                    argument,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetTypeNode {
                        level,
                        form: SetTypeForm::AppType {
                            rule,
                            function: reflect(env, function.into())?.try_into()?,
                            argument: reflect(env, argument.into())?.try_into()?,
                        },
                    })
                    .into()
                }
            }
        }
        Expression::ComputationKind(h) => {
            let node = a.get(h);
            let level = node.level;
            match node.form {
                ComputationKindForm::Base => a
                    .alloc(SetKindNode {
                        level,
                        form: SetKindForm::Base,
                    })
                    .into(),
                ComputationKindForm::ProdType {
                    rule,
                    var,
                    domain,
                    body,
                } => {
                    let rule = rule.reflected();
                    a.alloc(SetKindNode {
                        level,
                        form: SetKindForm::ProdType {
                            rule,
                            var,
                            domain: reflect(env, domain.into())?.try_into()?,
                            body: reflect(env, body.into())?.try_into()?,
                        },
                    })
                    .into()
                }
            }
        }
        _ => return Err("reflection requires Program syntax".into()),
    })
}

/// Supply proof premises for partial Program syntax. Correspondence and Set
/// typing are separate checks; callers must also type-check the certificate.
pub fn reflect_with_certificate(
    env: &Environment,
    program: Expression,
    certificate: SetTerm,
) -> Result<SetTerm, String> {
    correspondence(env, program, certificate.into())?;
    Ok(certificate)
}
fn correspondence(env: &Environment, p: Expression, g: Expression) -> Result<(), String> {
    let a = &env.arena;
    if let Ok(expected) = reflect(env, p)
        && convertible(env, expected, g)?
    {
        return Ok(());
    }
    if !a.sort(p).is_program()
        || a.sort(g) != a.sort(p).reflected()
        || p.family().stage() != g.family().stage()
    {
        return Err("reflection certificate family mismatch".into());
    }
    match p {
        Expression::ValueTerm(h) => {
            let node = a.get(h);
            match node.form {
                ValueTermForm::Constant { definition } => {
                    return correspondence(
                        env,
                        env.definition(definition)
                            .ok_or("unknown Program definition")?
                            .body,
                        g,
                    );
                }
                ValueTermForm::ThunkValue { computation } => {
                    return correspondence(env, computation.into(), g);
                }
                ValueTermForm::InductiveConstructor {
                    inductive,
                    constructor,
                    parameters,
                    fields,
                } => {
                    let (head, args) = decompose_application(a, g);
                    let spec = env.datatype(inductive).ok_or("unknown datatype")?;
                    let Some((id, actual, guide_parameters)) =
                        structure::inductive_constructor(a, head)
                    else {
                        return Err("constructor reflection mismatch".into());
                    };
                    if id != spec.reflected
                        || actual != constructor
                        || args.len() != fields.len()
                        || guide_parameters.len() != parameters.len()
                    {
                        return Err("constructor reflection mismatch".into());
                    }
                    for (p, g) in parameters.into_iter().zip(guide_parameters) {
                        correspondence(env, p.into(), g.into())?;
                    }
                    for (p, g) in fields.into_iter().zip(args) {
                        correspondence(env, p.into(), g)?;
                    }
                    return Ok(());
                }
                _ => {}
            }
            let g: SetTerm = g.try_into()?;
            match (node.form, a.get(g).form) {
                (
                    ValueTermForm::Continue {
                        state_ty,
                        result_ty,
                        next,
                    },
                    SetTermForm::Continue {
                        state_ty: state_ty_guide,
                        result_ty: result_ty_guide,
                        next: next_guide,
                    },
                ) => {
                    correspondence(env, state_ty.into(), state_ty_guide.into())?;
                    correspondence(env, result_ty.into(), result_ty_guide.into())?;
                    correspondence(env, next.into(), next_guide.into())?;
                    Ok(())
                }
                (
                    ValueTermForm::Finish {
                        state_ty,
                        result_ty,
                        output,
                    },
                    SetTermForm::Finish {
                        state_ty: state_ty_guide,
                        result_ty: result_ty_guide,
                        output: output_guide,
                    },
                ) => {
                    correspondence(env, state_ty.into(), state_ty_guide.into())?;
                    correspondence(env, result_ty.into(), result_ty_guide.into())?;
                    correspondence(env, output.into(), output_guide.into())?;
                    Ok(())
                }
                _ => Err("reflection certificate shape mismatch".into()),
            }
        }
        Expression::ValueType(h) => {
            let node = a.get(h);
            match node.form {
                ValueTypeForm::Constant { definition } => {
                    return correspondence(
                        env,
                        env.definition(definition)
                            .ok_or("unknown Program definition")?
                            .body,
                        g,
                    );
                }
                ValueTypeForm::Thunk { computation_ty } => {
                    return correspondence(env, computation_ty.into(), g);
                }
                _ => {}
            }
            let g: SetType = g.try_into()?;
            match (node.form, a.get(g).form) {
                (
                    ValueTypeForm::LambdaType {
                        rule,
                        var,
                        domain,
                        body,
                    },
                    SetTypeForm::LambdaType {
                        rule: rule_guide,
                        var: var_guide,
                        domain: domain_guide,
                        body: body_guide,
                    },
                ) => {
                    let _ = (var, var_guide);
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, domain.into(), domain_guide.into())?;
                    correspondence(env, body.into(), body_guide.into())?;
                    Ok(())
                }
                (
                    ValueTypeForm::AppType {
                        rule,
                        function,
                        argument,
                    },
                    SetTypeForm::AppType {
                        rule: rule_guide,
                        function: function_guide,
                        argument: argument_guide,
                    },
                ) => {
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, function.into(), function_guide.into())?;
                    correspondence(env, argument.into(), argument_guide.into())?;
                    Ok(())
                }
                _ => Err("reflection certificate shape mismatch".into()),
            }
        }
        Expression::ValueKind(_) | Expression::ComputationKind(_) => {
            let _: SetKind = g.try_into()?;
            Err("reflection certificate shape mismatch".into())
        }
        Expression::ComputationTerm(h) => {
            let node = a.get(h);
            match node.form {
                ComputationTermForm::Constant { definition } => {
                    return correspondence(
                        env,
                        env.definition(definition)
                            .ok_or("unknown Program definition")?
                            .body,
                        g,
                    );
                }
                ComputationTermForm::Return { value } => {
                    return correspondence(env, value.into(), g);
                }
                ComputationTermForm::Force { value } => {
                    return correspondence(env, value.into(), g);
                }
                ComputationTermForm::Sequence {
                    var,
                    value_ty,
                    computation,
                    body,
                } => {
                    let _ = var;
                    let g: SetTerm = g.try_into()?;
                    let SetTermForm::AppTerm {
                        function, argument, ..
                    } = a.read(g).form
                    else {
                        return Err("sequence reflection must be a lambda application".into());
                    };
                    let SetTermForm::LambdaTerm {
                        domain,
                        body: guide_body,
                        ..
                    } = a.read(function).form
                    else {
                        return Err("sequence reflection requires a lambda".into());
                    };
                    correspondence(env, value_ty.into(), domain.into())?;
                    correspondence(env, computation.into(), argument.into())?;
                    return correspondence(env, body.into(), guide_body.into());
                }
                ComputationTermForm::ValueLet {
                    var,
                    value_ty,
                    value,
                    body,
                } => {
                    let _ = var;
                    let g: SetTerm = g.try_into()?;
                    let SetTermForm::AppTerm {
                        function, argument, ..
                    } = a.read(g).form
                    else {
                        return Err("sequence reflection must be a lambda application".into());
                    };
                    let SetTermForm::LambdaTerm {
                        domain,
                        body: guide_body,
                        ..
                    } = a.read(function).form
                    else {
                        return Err("sequence reflection requires a lambda".into());
                    };
                    correspondence(env, value_ty.into(), domain.into())?;
                    correspondence(env, value.into(), argument.into())?;
                    return correspondence(env, body.into(), guide_body.into());
                }
                _ => {}
            }
            let g: SetTerm = g.try_into()?;
            match (node.form, a.get(g).form) {
                (
                    ComputationTermForm::LambdaTerm {
                        rule,
                        var,
                        domain,
                        body,
                    },
                    SetTermForm::LambdaTerm {
                        rule: rule_guide,
                        var: var_guide,
                        domain: domain_guide,
                        body: body_guide,
                    },
                ) => {
                    let _ = (var, var_guide);
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, domain.into(), domain_guide.into())?;
                    correspondence(env, body.into(), body_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTermForm::LambdaType {
                        rule,
                        var,
                        domain,
                        body,
                    },
                    SetTermForm::LambdaType {
                        rule: rule_guide,
                        var: var_guide,
                        domain: domain_guide,
                        body: body_guide,
                    },
                ) => {
                    let _ = (var, var_guide);
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, domain.into(), domain_guide.into())?;
                    correspondence(env, body.into(), body_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTermForm::AppTerm {
                        rule,
                        function,
                        argument,
                    },
                    SetTermForm::AppTerm {
                        rule: rule_guide,
                        function: function_guide,
                        argument: argument_guide,
                    },
                ) => {
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, function.into(), function_guide.into())?;
                    correspondence(env, argument.into(), argument_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTermForm::AppType {
                        rule,
                        function,
                        argument,
                    },
                    SetTermForm::AppType {
                        rule: rule_guide,
                        function: function_guide,
                        argument: argument_guide,
                    },
                ) => {
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, function.into(), function_guide.into())?;
                    correspondence(env, argument.into(), argument_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTermForm::Case {
                        inductive,
                        binders,
                        result_ty,
                        scrutinee,
                        branches,
                    },
                    SetTermForm::SetCase {
                        inductive: inductive_guide,
                        binders: binders_guide,
                        result_ty: result_ty_guide,
                        scrutinee: scrutinee_guide,
                        branches: branches_guide,
                    },
                ) => {
                    if inductive != inductive_guide
                        || !binders
                            .iter()
                            .map(Vec::len)
                            .eq(binders_guide.iter().map(Vec::len))
                    {
                        return Err("reflection certificate branch count mismatch".into());
                    }
                    correspondence(env, result_ty.into(), result_ty_guide.into())?;
                    correspondence(env, scrutinee.into(), scrutinee_guide.into())?;
                    if branches.len() != branches_guide.len() {
                        return Err("reflection certificate branch count mismatch".into());
                    }
                    for (p, g) in branches.into_iter().zip(branches_guide) {
                        correspondence(env, p.into(), g.into())?;
                    }
                    Ok(())
                }
                (
                    ComputationTermForm::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                    },
                    SetTermForm::SetRun {
                        state_ty: state_ty_guide,
                        result_ty: result_ty_guide,
                        step: step_guide,
                        initial: initial_guide,
                        ..
                    },
                ) => {
                    correspondence(env, state_ty.into(), state_ty_guide.into())?;
                    correspondence(env, result_ty.into(), result_ty_guide.into())?;
                    correspondence(env, step.into(), step_guide.into())?;
                    correspondence(env, initial.into(), initial_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTermForm::RunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                    },
                    SetTermForm::SetRunCase {
                        state_ty: state_ty_guide,
                        result_ty: result_ty_guide,
                        step: step_guide,
                        initial: initial_guide,
                        transition: transition_guide,
                        ..
                    },
                ) => {
                    correspondence(env, state_ty.into(), state_ty_guide.into())?;
                    correspondence(env, result_ty.into(), result_ty_guide.into())?;
                    correspondence(env, step.into(), step_guide.into())?;
                    correspondence(env, initial.into(), initial_guide.into())?;
                    correspondence(env, transition.into(), transition_guide.into())?;
                    Ok(())
                }
                _ => Err("reflection certificate shape mismatch".into()),
            }
        }
        Expression::ComputationType(h) => {
            let node = a.get(h);
            match node.form {
                ComputationTypeForm::Constant { definition } => {
                    return correspondence(
                        env,
                        env.definition(definition)
                            .ok_or("unknown Program definition")?
                            .body,
                        g,
                    );
                }
                ComputationTypeForm::ReturnType { value_ty } => {
                    return correspondence(env, value_ty.into(), g);
                }
                _ => {}
            }
            let g: SetType = g.try_into()?;
            match (node.form, a.get(g).form) {
                (
                    ComputationTypeForm::LambdaType {
                        rule,
                        var,
                        domain,
                        body,
                    },
                    SetTypeForm::LambdaType {
                        rule: rule_guide,
                        var: var_guide,
                        domain: domain_guide,
                        body: body_guide,
                    },
                ) => {
                    let _ = (var, var_guide);
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, domain.into(), domain_guide.into())?;
                    correspondence(env, body.into(), body_guide.into())?;
                    Ok(())
                }
                (
                    ComputationTypeForm::AppType {
                        rule,
                        function,
                        argument,
                    },
                    SetTypeForm::AppType {
                        rule: rule_guide,
                        function: function_guide,
                        argument: argument_guide,
                    },
                ) => {
                    if rule.reflected() != rule_guide {
                        return Err("reflection certificate rule mismatch".into());
                    }
                    correspondence(env, function.into(), function_guide.into())?;
                    correspondence(env, argument.into(), argument_guide.into())?;
                    Ok(())
                }
                _ => Err("reflection certificate shape mismatch".into()),
            }
        }
        _ => Err("reflection requires Program syntax".into()),
    }
}
