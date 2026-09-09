//! Structural Program-to-Set reflection, preserving family and level.
use super::{calculus::*, environment::*, sort::*, syntax::*};

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
    let d = a.data(e);
    if !d.sort.is_program() {
        return Err("reflection requires Program syntax".into());
    }
    let sort = d.sort.reflected();
    let family = Family::at(sort, e.family().stage());
    match d.op.clone() {
        Op::Thunk | Op::ReturnType | Op::ThunkValue | Op::Force | Op::Return => {
            return reflect(env, d.child(0));
        }
        Op::Constant { definition } => {
            let def = env
                .definition(definition)
                .ok_or("unknown Program definition")?;
            if let Some(cert) = def.certified_reflection {
                return Ok(cert.into());
            }
            return reflect(env, def.body);
        }
        Op::Sequence { var } | Op::ValueLet { var } => {
            let domain = reflect(env, d.child(0))?;
            let argument = reflect(env, d.child(1))?;
            let body = reflect(env, d.child(2))?;
            let rule = ProductRule::new(Sort::Base(a.sort(domain)), Sort::Base(a.sort(body)))?;
            let lambda = node(
                a,
                Family::SetTerm,
                rule.result.base(),
                Op::LambdaTerm { rule, var },
                &[(domain, 0), (body, 1)],
            );
            return Ok(apply(a, rule, lambda, argument));
        }
        Op::Run | Op::RunCase => {
            return Err("reflecting run requires an accessibility certificate".into());
        }
        _ => {}
    }
    let mut mapped = d.clone();
    mapped.sort = sort;
    for field in &mut mapped.fields {
        for child in field {
            child.expression = reflect(env, child.expression)?
        }
    }
    match &mut mapped.op {
        Op::ModuleParam { parameter } => {
            mapped.op = Op::ReflectedProgramParam {
                parameter: *parameter,
            }
        }
        Op::ProdTerm { rule, .. }
        | Op::ProdType { rule, .. }
        | Op::LambdaTerm { rule, .. }
        | Op::LambdaType { rule, .. }
        | Op::AppTerm { rule }
        | Op::AppType { rule } => *rule = rule.reflected(),
        Op::Inductive { inductive } => {
            mapped.op = Op::IndType {
                inductive: env
                    .datatype(*inductive)
                    .ok_or("unknown datatype")?
                    .reflected,
            }
        }
        Op::InductiveConstructor {
            inductive,
            constructor,
        } => {
            let id = env
                .datatype(*inductive)
                .ok_or("unknown datatype")?
                .reflected;
            let mut result = a.store(
                Family::SetTerm,
                Data {
                    sort,
                    op: Op::IndCtor {
                        inductive: id,
                        constructor: *constructor,
                    },
                    fields: vec![mapped.fields[0].clone()],
                },
            );
            for child in &mapped.fields[1] {
                let rule =
                    ProductRule::new(Sort::Base(a.sort(child.expression)), Sort::Base(sort))?;
                result = apply(a, rule, result, child.expression);
            }
            return Ok(result);
        }
        Op::Case { inductive, binders } => {
            mapped.op = Op::SetCase {
                inductive: *inductive,
                binders: binders.clone(),
            }
        }
        _ => {}
    }
    Ok(a.store(family, mapped))
}

/// Supply the proof fields needed to reflect a partial Program. The caller also
/// checks the certificate's Set type; correspondence alone is not a typing proof.
pub fn reflect_with_certificate(
    env: &Environment,
    program: Expression,
    certificate: SetTerm,
) -> Result<SetTerm, String> {
    fn go(env: &Environment, p: Expression, g: Expression) -> Result<Expression, String> {
        let a = &env.arena;
        if let Ok(expected) = reflect(env, p)
            && convertible(env, expected, g)?
        {
            return Ok(g);
        }
        let d = a.data(p);
        let guide = a.data(g);
        if !d.sort.is_program()
            || a.sort(g) != d.sort.reflected()
            || p.family().stage() != g.family().stage()
        {
            return Err("reflection certificate family mismatch".into());
        }
        match d.op {
            Op::Constant { definition } => {
                return go(
                    env,
                    env.definition(definition)
                        .ok_or("unknown Program definition")?
                        .body,
                    g,
                );
            }
            Op::Thunk | Op::ReturnType | Op::ThunkValue | Op::Return | Op::Force => {
                return go(env, d.child(0), g);
            }
            Op::InductiveConstructor {
                inductive,
                constructor,
            } => {
                let mut head = g;
                let mut args = vec![];
                loop {
                    let h = a.data(head);
                    if matches!(h.op, Op::AppTerm { .. } | Op::AppType { .. }) {
                        args.push(h.child(1));
                        head = h.child(0)
                    } else {
                        break;
                    }
                }
                args.reverse();
                let h = a.data(head);
                let spec = env.datatype(inductive).ok_or("unknown datatype")?;
                if !matches!(h.op,Op::IndCtor{inductive:i,constructor:c} if i==spec.reflected&&c==constructor)
                    || args.len() != d.fields[1].len()
                    || h.fields[0].len() != d.fields[0].len()
                {
                    return Err("constructor reflection mismatch".into());
                }
                for (p, g) in d.fields[0].iter().zip(&h.fields[0]) {
                    go(env, p.expression, g.expression)?;
                }
                for (p, g) in d.fields[1].iter().zip(args) {
                    go(env, p.expression, g)?;
                }
                return Ok(g);
            }
            Op::Sequence { .. } | Op::ValueLet { .. } => {
                if !matches!(guide.op, Op::AppTerm { .. }) {
                    return Err("sequence reflection must be a lambda application".into());
                }
                let lambda = a.data(guide.child(0));
                if !matches!(lambda.op, Op::LambdaTerm { .. }) {
                    return Err("sequence reflection requires a lambda".into());
                }
                go(env, d.child(0), lambda.child(0))?;
                go(env, d.child(1), guide.child(1))?;
                go(env, d.child(2), lambda.child(1))?;
                return Ok(g);
            }
            _ => {}
        }
        let mut expected = d.clone();
        expected.sort = d.sort.reflected();
        expected.op = match d.op {
            Op::Run => Op::SetRun,
            Op::RunCase => Op::SetRunCase,
            Op::Continue => Op::Continue,
            Op::Finish => Op::Finish,
            Op::LambdaTerm { rule, var } => Op::LambdaTerm {
                rule: rule.reflected(),
                var,
            },
            Op::LambdaType { rule, var } => Op::LambdaType {
                rule: rule.reflected(),
                var,
            },
            Op::AppTerm { rule } => Op::AppTerm {
                rule: rule.reflected(),
            },
            Op::AppType { rule } => Op::AppType {
                rule: rule.reflected(),
            },
            Op::Case { inductive, binders } => Op::SetCase { inductive, binders },
            _ => {
                return Err(format!(
                    "certificate does not have the structural reflection of {:?}; guide {:?}",
                    d.op, guide.op
                ));
            }
        };
        let same_shape = match (&expected.op, &guide.op) {
            (Op::SetRun, Op::SetRun)
            | (Op::SetRunCase, Op::SetRunCase)
            | (Op::Continue, Op::Continue)
            | (Op::Finish, Op::Finish) => true,
            (Op::LambdaTerm { rule: a, .. }, Op::LambdaTerm { rule: b, .. })
            | (Op::LambdaType { rule: a, .. }, Op::LambdaType { rule: b, .. })
            | (Op::AppTerm { rule: a }, Op::AppTerm { rule: b })
            | (Op::AppType { rule: a }, Op::AppType { rule: b }) => a == b,
            (
                Op::SetCase {
                    inductive: a,
                    binders: xs,
                },
                Op::SetCase {
                    inductive: b,
                    binders: ys,
                },
            ) => a == b && xs.iter().map(Vec::len).eq(ys.iter().map(Vec::len)),
            _ => false,
        };
        if !same_shape || guide.fields.len() < expected.fields.len() {
            return Err("reflection certificate shape mismatch".into());
        }
        for (field, gfield) in expected.fields.iter_mut().zip(&guide.fields) {
            if field.len() != gfield.len() {
                return Err("reflection certificate branch count mismatch".into());
            }
            for (child, gchild) in field.iter_mut().zip(gfield) {
                child.expression = go(env, child.expression, gchild.expression)?;
            }
        }
        if matches!(expected.op, Op::SetRun | Op::SetRunCase) {
            expected
                .fields
                .extend_from_slice(&guide.fields[expected.fields.len()..]);
        }
        let expected = a.store(g.family(), expected);
        if alpha_equal(a, expected, g) {
            Ok(g)
        } else {
            Err("reflection certificate differs from the Program".into())
        }
    }
    go(env, program, certificate.into())?;
    Ok(certificate)
}
