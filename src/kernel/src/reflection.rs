//! Structural Program-to-Set reflection, preserving family and level.
use super::{construction as build, environment::*, sort::*, syntax::*};

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
        ValueTermForm::Ambient { level } => a.alloc(SetTermNode {
            level: node.level,
            form: SetTermForm::ReflectedAmbient { level },
        }),
        ValueTermForm::Annotated { body, classifier } => {
            reflect_annotation(env, body.into(), classifier)?.try_into()?
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
        ValueTypeForm::Ambient { level } => a.alloc(SetTypeNode {
            level: node.level,
            form: SetTypeForm::ReflectedAmbient { level },
        }),
        ValueTypeForm::Annotated { body, classifier } => {
            reflect_annotation(env, body.into(), classifier)?.try_into()?
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

pub(crate) fn reflect_computation_term(
    env: &Environment,
    h: ComputationTerm,
) -> Result<SetTerm, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ComputationTermForm::Ambient { level } => a.alloc(SetTermNode {
            level: node.level,
            form: SetTermForm::ReflectedAmbient { level },
        }),
        ComputationTermForm::Annotated { body, classifier } => {
            reflect_annotation(env, body.into(), classifier)?.try_into()?
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
            accessibility,
        } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::SetRun {
                state_ty: reflect_value_type(env, state_ty)?,
                result_ty: reflect_value_type(env, result_ty)?,
                step: reflect_value_term(env, step)?,
                initial: reflect_value_term(env, initial)?,
                accessibility,
            },
        }),
        ComputationTermForm::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => a.alloc(SetTermNode {
            level,
            form: SetTermForm::SetRunCase {
                state_ty: reflect_value_type(env, state_ty)?,
                result_ty: reflect_value_type(env, result_ty)?,
                step: reflect_value_term(env, step)?,
                initial: reflect_value_term(env, initial)?,
                transition: reflect_computation_term(env, transition)?,
                accessibility,
                transition_equality,
            },
        }),
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
        ComputationTypeForm::Ambient { level } => a.alloc(SetTypeNode {
            level: node.level,
            form: SetTypeForm::ReflectedAmbient { level },
        }),
        ComputationTypeForm::Annotated { body, classifier } => {
            reflect_annotation(env, body.into(), classifier)?.try_into()?
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

fn reflect_annotation(
    env: &Environment,
    body: Expression,
    classifier: super::environment::Classifier,
) -> Result<Expression, String> {
    use super::environment::Classifier;
    let body = reflect_program_expression(env, body)?;
    let classifier = match classifier {
        Classifier::Expression(ty) => Classifier::Expression(reflect_program_expression(env, ty)?),
        Classifier::Upper(sort) => {
            Classifier::Upper(BaseSort::Set(sort.level().ok_or("expected Program sort")?))
        }
    };
    env.arena.annotated(body, classifier)
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
