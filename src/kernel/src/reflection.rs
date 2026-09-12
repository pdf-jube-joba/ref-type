//! Structural Program-to-Set reflection, preserving family and level.
use super::{calculus::*, construction as build, environment::*, sort::*, structure, syntax::*};

pub fn reflect_kind(env: &Environment, k: ProgramKind) -> Result<SetKind, String> {
    match k {
        ProgramKind::ValueKind(k) => reflect_value_kind(env, k),
        ProgramKind::ComputationKind(k) => reflect_computation_kind(env, k),
    }
}

pub fn reflect_type(env: &Environment, ty: ProgramType) -> Result<SetType, String> {
    match ty {
        ProgramType::ValueType(ty) => reflect_value_type(env, ty),
        ProgramType::ComputationType(ty) => reflect_computation_type(env, ty),
    }
}

pub fn reflect_term(env: &Environment, term: ProgramTerm) -> Result<SetTerm, String> {
    match term {
        ProgramTerm::ValueTerm(term) => reflect_value_term(env, term),
        ProgramTerm::ComputationTerm(term) => reflect_computation_term(env, term),
    }
}

pub fn reflect_context(env: &Environment, c: &Context) -> Result<Context, String> {
    c.iter()
        .map(|b| {
            Ok(Binding {
                var: b.var,
                classifier: reflect_program_expression(env, b.classifier)?,
            })
        })
        .collect()
}

pub(crate) fn reflect_program_expression(
    env: &Environment,
    e: Expression,
) -> Result<Expression, String> {
    match e {
        Expression::ValueTerm(h) => Ok(reflect_value_term(env, h)?.into()),
        Expression::ValueType(h) => Ok(reflect_value_type(env, h)?.into()),
        Expression::ValueKind(h) => Ok(reflect_value_kind(env, h)?.into()),
        Expression::ComputationTerm(h) => Ok(reflect_computation_term(env, h)?.into()),
        Expression::ComputationType(h) => Ok(reflect_computation_type(env, h)?.into()),
        Expression::ComputationKind(h) => Ok(reflect_computation_kind(env, h)?.into()),
        _ => Err("reflection requires Program syntax".into()),
    }
}

fn reflect_value_term(env: &Environment, h: ValueTerm) -> Result<SetTerm, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ValueTermForm::Bound { index } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::Bound { index },
        }),
        ValueTermForm::ModuleParam { parameter } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::ReflectedProgramParam { parameter },
        }),
        ValueTermForm::Constant { definition } => {
            let definition = env
                .definition(definition)
                .ok_or("unknown Program definition")?;
            if let Some(certificate) = definition.certified_reflection {
                certificate
            } else {
                reflect_term(env, definition.body.try_into()?)?
            }
        }
        ValueTermForm::ThunkValue { computation } => reflect_computation_term(env, computation)?,
        ValueTermForm::Continue {
            state_ty,
            result_ty,
            next,
        } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::Continue {
                state_ty: reflect_value_type(env, state_ty)?,
                result_ty: reflect_value_type(env, result_ty)?,
                next: reflect_value_term(env, next)?,
            },
        }),
        ValueTermForm::Finish {
            state_ty,
            result_ty,
            output,
        } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::Finish {
                state_ty: reflect_value_type(env, state_ty)?,
                result_ty: reflect_value_type(env, result_ty)?,
                output: reflect_value_term(env, output)?,
            },
        }),
        ValueTermForm::InductiveConstructor {
            inductive,
            constructor,
            parameters,
            fields,
        } => {
            let spec = env.datatype(inductive).ok_or("unknown datatype")?;
            let parameters = parameters
                .into_iter()
                .map(|p| Ok(LogicalArgument::from(reflect_type(env, p)?)))
                .collect::<Result<Vec<LogicalArgument>, String>>()?;
            let mut result: SetTerm = build::inductive_constructor(
                a,
                BaseSort::Set(level),
                Stage::Term,
                spec.reflected,
                constructor,
                parameters,
            )?
            .try_into()?;
            for field in fields {
                let field = reflect_value_term(env, field)?;
                let rule =
                    ProductRule::new(Sort::Base(a.sort(field)), Sort::Base(BaseSort::Set(level)))?;
                result = build::apply(a, rule, result.into(), field.into())?.try_into()?;
            }
            result
        }
    })
}

fn reflect_value_type(env: &Environment, h: ValueType) -> Result<SetType, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ValueTypeForm::Bound { index } => a.alloc(SetTypeNode {
            level,
            form: SetTypeForm::Bound { index },
        }),
        ValueTypeForm::ModuleParam { parameter } => a.alloc(SetTypeNode {
            level,
            form: SetTypeForm::ReflectedProgramParam { parameter },
        }),
        ValueTypeForm::Constant { definition } => {
            let definition = env
                .definition(definition)
                .ok_or("unknown Program definition")?;
            if let Some(certificate) = definition.certified_reflection {
                Expression::from(certificate).try_into()?
            } else {
                reflect_type(env, definition.body.try_into()?)?
            }
        }
        ValueTypeForm::Thunk { computation_ty } => reflect_computation_type(env, computation_ty)?,
        ValueTypeForm::RunStep {
            state_ty,
            result_ty,
        } => a.alloc(SetTypeNode {
            level,
            form: SetTypeForm::RunStep {
                state_ty: reflect_value_type(env, state_ty)?,
                result_ty: reflect_value_type(env, result_ty)?,
            },
        }),
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
                        .map(|child| Ok(LogicalArgument::from(reflect_type(env, child)?)))
                        .collect::<Result<_, String>>()?,
                },
            })
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_value_type(env, body)?,
                },
            })
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
                    function: reflect_value_type(env, function)?,
                    argument: reflect_type(env, argument)?,
                },
            })
        }
    })
}

fn reflect_value_kind(env: &Environment, h: ValueKind) -> Result<SetKind, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ValueKindForm::Base => a.alloc(SetKindNode {
            level,
            form: SetKindForm::Base,
        }),
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_value_kind(env, body)?,
                },
            })
        }
    })
}

fn reflect_computation_term(env: &Environment, h: ComputationTerm) -> Result<SetTerm, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ComputationTermForm::ModuleParam { parameter } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::ReflectedProgramParam { parameter },
        }),
        ComputationTermForm::Constant { definition } => {
            let definition = env
                .definition(definition)
                .ok_or("unknown Program definition")?;
            if let Some(certificate) = definition.certified_reflection {
                certificate
            } else {
                reflect_term(env, definition.body.try_into()?)?
            }
        }
        ComputationTermForm::Return { value } => reflect_value_term(env, value)?,
        ComputationTermForm::Force { value } => reflect_value_term(env, value)?,
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
                    domain: reflect_value_type(env, domain)?,
                    body: reflect_computation_term(env, body)?,
                },
            })
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_computation_term(env, body)?,
                },
            })
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
                    function: reflect_computation_term(env, function)?,
                    argument: reflect_value_term(env, argument)?,
                },
            })
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
                    function: reflect_computation_term(env, function)?,
                    argument: reflect_type(env, argument)?,
                },
            })
        }
        ComputationTermForm::Sequence {
            var,
            value_ty,
            computation,
            body,
        } => {
            let domain = reflect_value_type(env, value_ty)?;
            let argument = reflect_computation_term(env, computation)?;
            let body = reflect_computation_term(env, body)?;
            let rule = ProductRule::new(Sort::Base(a.sort(domain)), Sort::Base(a.sort(body)))?;
            let lambda = build::lambda(a, rule, var, domain.into(), body.into())?;
            build::apply(a, rule, lambda, argument.into())?.try_into()?
        }
        ComputationTermForm::ValueLet {
            var,
            value_ty,
            value,
            body,
        } => {
            let domain = reflect_value_type(env, value_ty)?;
            let argument = reflect_value_term(env, value)?;
            let body = reflect_computation_term(env, body)?;
            let rule = ProductRule::new(Sort::Base(a.sort(domain)), Sort::Base(a.sort(body)))?;
            let lambda = build::lambda(a, rule, var, domain.into(), body.into())?;
            build::apply(a, rule, lambda, argument.into())?.try_into()?
        }
        ComputationTermForm::Case {
            inductive,
            binders,
            result_ty,
            scrutinee,
            branches,
        } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::SetCase {
                inductive,
                binders,
                result_ty: reflect_computation_type(env, result_ty)?,
                scrutinee: reflect_value_term(env, scrutinee)?,
                branches: branches
                    .into_iter()
                    .map(|child| reflect_computation_term(env, child))
                    .collect::<Result<_, String>>()?,
            },
        }),
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
    })
}

fn reflect_computation_type(env: &Environment, h: ComputationType) -> Result<SetType, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ComputationTypeForm::Bound { index } => a.alloc(SetTypeNode {
            level,
            form: SetTypeForm::Bound { index },
        }),
        ComputationTypeForm::ModuleParam { parameter } => a.alloc(SetTypeNode {
            level,
            form: SetTypeForm::ReflectedProgramParam { parameter },
        }),
        ComputationTypeForm::Constant { definition } => {
            let definition = env
                .definition(definition)
                .ok_or("unknown Program definition")?;
            if let Some(certificate) = definition.certified_reflection {
                Expression::from(certificate).try_into()?
            } else {
                reflect_type(env, definition.body.try_into()?)?
            }
        }
        ComputationTypeForm::ReturnType { value_ty } => reflect_value_type(env, value_ty)?,
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
                    domain: reflect_value_type(env, domain)?,
                    body: reflect_computation_type(env, body)?,
                },
            })
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_computation_type(env, body)?,
                },
            })
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_computation_type(env, body)?,
                },
            })
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
                    function: reflect_computation_type(env, function)?,
                    argument: reflect_type(env, argument)?,
                },
            })
        }
    })
}

fn reflect_computation_kind(env: &Environment, h: ComputationKind) -> Result<SetKind, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ComputationKindForm::Base => a.alloc(SetKindNode {
            level,
            form: SetKindForm::Base,
        }),
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
                    domain: reflect_kind(env, domain)?,
                    body: reflect_computation_kind(env, body)?,
                },
            })
        }
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
    if let Ok(expected) = reflect_program_expression(env, p)
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
