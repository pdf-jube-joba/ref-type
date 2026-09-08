//! Simultaneous, family-preserving transformations of all nine syntax partitions.
use super::{environment::Environment, syntax::*};
use crate::ids::*;

pub(crate) fn map_children(
    arena: &Arena,
    e: Expression,
    mut f: impl FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let original = arena.data(e);
    let mut data = original.clone();
    for field in &mut data.fields {
        for child in field {
            let mapped = f(child.expression, child.depth)?;
            if mapped.family() != child.expression.family()
                || arena.sort(mapped) != arena.sort(child.expression)
            {
                return Err("transformation changed syntax family or sort index".into());
            }
            child.expression = mapped;
        }
    }
    Ok(if original == data {
        e
    } else {
        arena.store(e.family(), data)
    })
}
pub fn shift(
    arena: &Arena,
    e: impl Into<Expression>,
    amount: usize,
    cutoff: usize,
) -> Result<Expression, String> {
    fn walk(a: &Arena, e: Expression, n: usize, c: usize) -> Result<Expression, String> {
        let mut d = a.data(e);
        if let Op::Bound { index } = d.op {
            if index >= c {
                d.op = Op::Bound {
                    index: index.checked_add(n).ok_or("bound index overflow")?,
                };
                return Ok(a.store(e.family(), d));
            }
            return Ok(e);
        }
        map_children(a, e, |e, depth| walk(a, e, n, c + depth))
    }
    walk(arena, e.into(), amount, cutoff)
}
pub fn substitute(
    arena: &Arena,
    body: impl Into<Expression>,
    argument: impl Into<Expression>,
) -> Result<Expression, String> {
    fn walk(a: &Arena, e: Expression, arg: Expression, depth: usize) -> Result<Expression, String> {
        let mut d = a.data(e);
        if let Op::Bound { index } = d.op {
            if index == depth {
                if e.family() != arg.family() || a.sort(e) != a.sort(arg) {
                    return Err("substitution argument has the wrong family or level".into());
                }
                return shift(a, arg, depth, 0);
            }
            if index > depth {
                d.op = Op::Bound { index: index - 1 };
                return Ok(a.store(e.family(), d));
            }
            return Ok(e);
        }
        map_children(a, e, |x, n| walk(a, x, arg, depth + n))
    }
    walk(arena, body.into(), argument.into(), 0)
}
pub fn instantiate_telescope(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
) -> Result<Expression, String> {
    let mut result = e;
    for (i, &argument) in arguments.iter().enumerate().rev() {
        result = substitute(arena, result, shift(arena, argument, i, 0)?)?
    }
    Ok(result)
}
pub fn contains_bound(arena: &Arena, e: Expression, index: usize) -> bool {
    let d = arena.data(e);
    if let Op::Bound { index: i } = d.op {
        return i == index;
    }
    d.fields
        .iter()
        .flatten()
        .any(|c| contains_bound(arena, c.expression, index + c.depth))
}
pub fn is_closed(arena: &Arena, e: Expression) -> bool {
    fn go(a: &Arena, e: Expression, depth: usize) -> bool {
        let d = a.data(e);
        match d.op {
            Op::Bound { index } => index < depth,
            Op::ModuleParam { .. } => false,
            _ => d
                .fields
                .iter()
                .flatten()
                .all(|c| go(a, c.expression, depth + c.depth)),
        }
    }
    go(arena, e, 0)
}
pub fn substitute_parameters(
    arena: &Arena,
    e: Expression,
    parameters: &std::collections::HashMap<ModuleParamId, Expression>,
) -> Result<Expression, String> {
    fn go(
        a: &Arena,
        e: Expression,
        p: &std::collections::HashMap<ModuleParamId, Expression>,
        depth: usize,
    ) -> Result<Expression, String> {
        if let Op::ModuleParam { parameter } = a.data(e).op {
            if let Some(&arg) = p.get(&parameter) {
                if arg.family() != e.family() || a.sort(arg) != a.sort(e) {
                    return Err("module argument classification mismatch".into());
                }
                return shift(a, arg, depth, 0);
            }
        }
        map_children(a, e, |x, n| go(a, x, p, depth + n))
    }
    go(arena, e, parameters, 0)
}
pub fn remap_ids(
    arena: &Arena,
    e: Expression,
    definitions: &std::collections::HashMap<DefId, DefId>,
    inductives: &std::collections::HashMap<InductiveId, InductiveId>,
    datatypes: &std::collections::HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Result<Expression, String> {
    let mapped = map_children(arena, e, |x, _| {
        remap_ids(arena, x, definitions, inductives, datatypes)
    })?;
    let mut d = arena.data(mapped);
    let old = d.op.clone();
    match &mut d.op {
        Op::Constant { definition } => {
            *definition = definitions.get(definition).copied().unwrap_or(*definition)
        }
        Op::IndType { inductive }
        | Op::IndCtor { inductive, .. }
        | Op::IndElim { inductive, .. } => {
            *inductive = inductives.get(inductive).copied().unwrap_or(*inductive)
        }
        Op::Inductive { inductive }
        | Op::InductiveConstructor { inductive, .. }
        | Op::Case { inductive, .. }
        | Op::SetCase { inductive, .. } => {
            *inductive = datatypes.get(inductive).copied().unwrap_or(*inductive)
        }
        _ => {}
    }
    Ok(if old == d.op {
        mapped
    } else {
        arena.store(mapped.family(), d)
    })
}
fn alpha_op(mut op: Op) -> Op {
    match &mut op {
        Op::ProdTerm { var, .. }
        | Op::ProdType { var, .. }
        | Op::LambdaTerm { var, .. }
        | Op::LambdaType { var, .. }
        | Op::Subset { var }
        | Op::Sequence { var }
        | Op::ValueLet { var }
        | Op::IdElim { var }
        | Op::Recursor { var, .. }
        | Op::BoxTypeApp { var, .. } => *var = SymbolId::ANONYMOUS,
        Op::IndElim { motive_vars, .. } => motive_vars.fill(SymbolId::ANONYMOUS),
        Op::Case { binders, .. } | Op::SetCase { binders, .. } => {
            for branch in binders {
                branch.fill(SymbolId::ANONYMOUS)
            }
        }
        _ => {}
    }
    op
}
pub fn alpha_equal(arena: &Arena, left: Expression, right: Expression) -> bool {
    if left == right {
        return true;
    }
    if left.family() != right.family() {
        return false;
    }
    let a = arena.data(left);
    let b = arena.data(right);
    a.sort == b.sort
        && alpha_op(a.op.clone()) == alpha_op(b.op.clone())
        && a.fields.len() == b.fields.len()
        && a.fields
            .iter()
            .zip(&b.fields)
            .take(computational_fields(&a))
            .all(|(xs, ys)| {
                xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(x, y)| {
                        x.depth == y.depth && alpha_equal(arena, x.expression, y.expression)
                    })
            })
}
pub(crate) fn node(
    arena: &Arena,
    family: Family,
    sort: super::sort::BaseSort,
    op: Op,
    children: &[(Expression, usize)],
) -> Expression {
    arena.store(
        family,
        Data {
            sort,
            op,
            fields: children
                .iter()
                .map(|&(expression, depth)| vec![Child { expression, depth }])
                .collect(),
        },
    )
}
pub(crate) fn apply(
    arena: &Arena,
    rule: super::sort::ProductRule,
    function: Expression,
    argument: Expression,
) -> Expression {
    let stage = if rule.body.is_upper() {
        Stage::Type
    } else {
        Stage::Term
    };
    let op = if rule.domain.is_upper() {
        Op::AppType { rule }
    } else {
        Op::AppTerm { rule }
    };
    node(
        arena,
        Family::at(rule.body.base(), stage),
        rule.body.base(),
        op,
        &[(function, 0), (argument, 0)],
    )
}
fn reduce_root(env: &Environment, e: Expression) -> Result<Option<Expression>, String> {
    if e.family() == Family::Value {
        return Ok(None);
    }
    let a = &env.arena;
    let d = a.data(e);
    let c = |i| d.child(i);
    let root = match d.op.clone() {
        Op::Constant { definition } => env.definition(definition).map(|x| x.body),
        Op::AppTerm { rule } | Op::AppType { rule } => {
            rule.validate()?;
            let f = a.data(c(0));
            match f.op {
                Op::LambdaTerm { rule: r, .. } | Op::LambdaType { rule: r, .. } if r == rule => {
                    Some(substitute(a, f.child(1), c(1))?)
                }
                _ => None,
            }
        }
        Op::Force => {
            let v = a.data(unfold_value(env, c(0))?);
            if v.op == Op::ThunkValue {
                Some(v.child(0))
            } else {
                None
            }
        }
        Op::ValueLet { .. } => Some(substitute(a, c(2), c(1))?),
        Op::Sequence { .. } => {
            let m = a.data(c(1));
            if m.op == Op::Return {
                Some(substitute(a, c(2), m.child(0))?)
            } else {
                None
            }
        }
        Op::BoxProgram => {
            if c(1).family() == Family::Computation {
                if let Some(next) = reduce_once(env, c(1))? {
                    let mut next_box = d.clone();
                    next_box.fields[1][0].expression = next;
                    next_box.fields[2][0].expression = advance_certificate(env, next, c(2))?;
                    Some(a.store(e.family(), next_box))
                } else {
                    None
                }
            } else {
                None
            }
        }
        Op::ForceBox => {
            let boxed = a.data(c(1));
            if boxed.op == Op::BoxProgram
                && convertible(env, c(0), boxed.child(0))?
                && (boxed.child(1).family() == Family::Value
                    || reduce_once(env, boxed.child(1))?.is_none())
            {
                Some(boxed.child(2))
            } else {
                None
            }
        }
        Op::BoxApp { rule } | Op::BoxTypeApp { rule, .. } => {
            let f = a.data(c(2));
            if f.op != Op::BoxProgram {
                None
            } else {
                let type_app = matches!(d.op, Op::BoxTypeApp { .. });
                let arg = if type_app {
                    Some((c(3), super::reflection::reflect(env, c(3))?))
                } else {
                    let x = a.data(c(3));
                    if x.op == Op::BoxProgram {
                        Some((x.child(1), x.child(2)))
                    } else {
                        None
                    }
                };
                if let Some((argument, reflected_argument)) = arg {
                    let result_ty = if type_app {
                        substitute(a, c(1), argument)?
                    } else {
                        c(1)
                    };
                    let program = apply(a, rule, f.child(1), argument);
                    let certificate = apply(a, rule.reflected(), f.child(2), reflected_argument);
                    Some(node(
                        a,
                        Family::SetTerm,
                        a.sort(result_ty).reflected(),
                        Op::BoxProgram,
                        &[(result_ty, 0), (program, 0), (certificate, 0)],
                    ))
                } else {
                    None
                }
            }
        }
        Op::Run | Op::SetRun => {
            let program = d.op == Op::Run;
            let b = a.sort(c(0));
            let i = b.level().ok_or("run requires a level")?;
            let rule = super::sort::ProductRule::new(
                super::sort::Sort::Base(b),
                super::sort::Sort::Base(if program {
                    super::sort::BaseSort::Computation(i)
                } else {
                    b
                }),
            )?;
            let step = if program {
                node(
                    a,
                    Family::Computation,
                    super::sort::BaseSort::Computation(i),
                    Op::Force,
                    &[(c(2), 0)],
                )
            } else {
                c(2)
            };
            let transition = apply(a, rule, step, c(3));
            let mut next = d.clone();
            next.op = if program { Op::RunCase } else { Op::SetRunCase };
            if program {
                next.fields.push(vec![Child {
                    depth: 0,
                    expression: transition,
                }]);
            } else {
                next.fields.insert(
                    4,
                    vec![Child {
                        depth: 0,
                        expression: transition,
                    }],
                );
                let proof = node(
                    a,
                    Family::SetTerm,
                    super::sort::BaseSort::Prop,
                    Op::IdRefl,
                    &[(transition, 0)],
                );
                next.fields.push(vec![Child {
                    depth: 0,
                    expression: proof,
                }]);
            }
            Some(a.store(e.family(), next))
        }
        Op::RunCase | Op::SetRunCase => {
            let program = d.op == Op::RunCase;
            let mut tr = a.data(c(4));
            if program && tr.op == Op::Return {
                tr = a.data(unfold_value(env, tr.child(0))?);
            }
            match tr.op {
                Op::Finish => {
                    let out = tr.child(2);
                    Some(if program {
                        node(a, Family::Computation, d.sort, Op::Return, &[(out, 0)])
                    } else {
                        out
                    })
                }
                Op::Continue => {
                    let next = tr.child(2);
                    if program {
                        Some(node(
                            a,
                            Family::Computation,
                            d.sort,
                            Op::Run,
                            &[(c(0), 0), (c(1), 0), (c(2), 0), (next, 0)],
                        ))
                    } else {
                        let proof = node(
                            a,
                            Family::SetTerm,
                            super::sort::BaseSort::Prop,
                            Op::AccDescent,
                            &[
                                (c(0), 0),
                                (c(1), 0),
                                (c(2), 0),
                                (c(3), 0),
                                (next, 0),
                                (c(5), 0),
                                (c(6), 0),
                            ],
                        );
                        Some(node(
                            a,
                            Family::SetTerm,
                            d.sort,
                            Op::SetRun,
                            &[(c(0), 0), (c(1), 0), (c(2), 0), (next, 0), (proof, 0)],
                        ))
                    }
                }
                _ => None,
            }
        }
        Op::SubsetIntro => Some(c(2)),
        Op::Pred => {
            let s = a.data(c(1));
            if matches!(s.op, Op::Subset { .. }) {
                Some(substitute(a, s.child(1), c(2))?)
            } else {
                None
            }
        }
        Op::Recursor { rule, .. } => {
            let scrutinee = a.data(c(5));
            match scrutinee.op {
                Op::Continue => Some(apply(a, rule, c(3), scrutinee.child(2))),
                Op::Finish => Some(apply(a, rule, c(4), scrutinee.child(2))),
                _ => None,
            }
        }
        Op::IndElim { .. } => reduce_inductive(env, e)?,
        Op::Case { .. } | Op::SetCase { .. } => {
            let scrutinee = if c(1).family() == Family::Value {
                unfold_value(env, c(1))?
            } else {
                c(1)
            };
            let (head, args) = decompose_application(a, scrutinee);
            let s = a.data(head);
            match s.op {
                Op::InductiveConstructor { constructor, .. } => {
                    let branch = d.fields[2]
                        .get(constructor)
                        .ok_or("case branch missing")?
                        .expression;
                    Some(instantiate_telescope(a, branch, &s.children(1))?)
                }
                Op::IndCtor { constructor, .. } => {
                    let branch = d.fields[2]
                        .get(constructor)
                        .ok_or("case branch missing")?
                        .expression;
                    Some(instantiate_telescope(a, branch, &args)?)
                }
                _ => None,
            }
        }
        _ => None,
    };
    if let Some(result) = root {
        if result.family() != e.family() || a.sort(result) != d.sort {
            return Err("reduction changed syntax family or level".into());
        }
        return Ok(Some(result));
    }
    Ok(None)
}
pub fn reduce_once(
    env: &Environment,
    e: impl Into<Expression>,
) -> Result<Option<Expression>, String> {
    let e = e.into();
    if let Some(result) = reduce_root(env, e)? {
        return Ok(Some(result));
    }
    let a = &env.arena;
    let d = a.data(e);
    // Program values do not step. Computations use precisely the evaluation contexts.
    if e.family() == Family::Value {
        return Ok(None);
    }
    let positions: Vec<(usize, usize)> = if e.family() == Family::Computation {
        match d.op {
            Op::AppTerm { .. } | Op::AppType { .. } => vec![(0, 0)],
            Op::Sequence { .. } => vec![(1, 0)],
            Op::RunCase => vec![(4, 0)],
            _ => vec![],
        }
    } else {
        d.fields
            .iter()
            .take(computational_fields(&d))
            .enumerate()
            .flat_map(|(i, f)| {
                f.iter().enumerate().filter_map(move |(j, x)| {
                    (!a.sort(x.expression).is_program()).then_some((i, j))
                })
            })
            .collect()
    };
    let positions = if matches!(
        e.family(),
        Family::ValueType | Family::ComputationType | Family::ValueKind | Family::ComputationKind
    ) {
        d.fields
            .iter()
            .enumerate()
            .flat_map(|(i, f)| (0..f.len()).map(move |j| (i, j)))
            .collect()
    } else {
        positions
    };
    for (i, j) in positions {
        if let Some(r) = reduce_once(env, d.fields[i][j].expression)? {
            let mut changed = d.clone();
            changed.fields[i][j].expression = r;
            return Ok(Some(a.store(e.family(), changed)));
        }
    }
    Ok(None)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(Expression),
    OutOfFuel(Expression),
}
pub fn evaluate(
    env: &Environment,
    e: impl Into<Expression>,
    fuel: usize,
) -> Result<Evaluation, String> {
    let mut e = e.into();
    for _ in 0..fuel {
        match reduce_once(env, e)? {
            Some(next) => e = next,
            None => return Ok(Evaluation::Normal(e)),
        }
    }
    Ok(if reduce_once(env, e)?.is_none() {
        Evaluation::Normal(e)
    } else {
        Evaluation::OutOfFuel(e)
    })
}
pub fn normalize(env: &Environment, e: impl Into<Expression>) -> Result<Expression, String> {
    match evaluate(env, e, 100_000)? {
        Evaluation::Normal(e) => Ok(e),
        Evaluation::OutOfFuel(_) => Err("normalization fuel exhausted".into()),
    }
}
pub fn convertible(env: &Environment, a: Expression, b: Expression) -> Result<bool, String> {
    fn go(
        env: &Environment,
        a: Expression,
        b: Expression,
        seen: &mut std::collections::HashMap<(Expression, Expression), bool>,
    ) -> Result<bool, String> {
        if a.family() != b.family() || env.arena.sort(a) != env.arena.sort(b) {
            return Ok(false);
        }
        if alpha_equal(&env.arena, a, b) {
            return Ok(true);
        }
        if let Some(&result) = seen.get(&(a, b)) {
            return Ok(result);
        }
        let ah = whnf(env, a)?;
        let bh = whnf(env, b)?;
        if alpha_equal(&env.arena, ah, bh) {
            seen.insert((a, b), true);
            return Ok(true);
        }
        let x = env.arena.data(ah);
        let y = env.arena.data(bh);
        if alpha_op(x.op.clone()) != alpha_op(y.op.clone()) || x.fields.len() != y.fields.len() {
            seen.insert((a, b), false);
            return Ok(false);
        }
        for (xs, ys) in x
            .fields
            .iter()
            .zip(&y.fields)
            .take(computational_fields(&x))
        {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys) {
                if x.depth != y.depth || !go(env, x.expression, y.expression, seen)? {
                    seen.insert((a, b), false);
                    return Ok(false);
                }
            }
        }
        seen.insert((a, b), true);
        Ok(true)
    }
    go(env, a, b, &mut std::collections::HashMap::new())
}
pub fn whnf(env: &Environment, e: Expression) -> Result<Expression, String> {
    if let Some(&cached) = env.head_cache.borrow().get(&e) {
        return Ok(cached);
    }
    let a = &env.arena;
    let original = e;
    let mut e = e;
    for _ in 0..100_000 {
        if let Some(next) = reduce_root(env, e)? {
            e = next;
            continue;
        }
        let mut d = a.data(e);
        let indices: &[usize] = match d.op {
            Op::AppTerm { .. } | Op::AppType { .. } | Op::IndElim { .. } => &[0],
            Op::Pred | Op::Case { .. } | Op::SetCase { .. } | Op::ForceBox => &[1],
            Op::Recursor { .. } => &[5],
            Op::RunCase | Op::SetRunCase => &[4],
            Op::Sequence { .. } => &[1],
            Op::BoxApp { .. } => &[2, 3],
            Op::BoxTypeApp { .. } => &[2],
            _ => &[],
        };
        let mut changed = false;
        for &i in indices {
            let child = d.child(i);
            let head = whnf(env, child)?;
            changed |= head != child;
            d.fields[i][0].expression = head;
        }
        if !changed {
            env.head_cache.borrow_mut().insert(original, e);
            return Ok(e);
        }
        e = a.store(e.family(), d);
    }
    Err("head normalization fuel exhausted".into())
}

fn decompose_application(a: &Arena, mut e: Expression) -> (Expression, Vec<Expression>) {
    let mut args = vec![];
    loop {
        let d = a.data(e);
        match d.op {
            Op::AppTerm { .. } | Op::AppType { .. } => {
                args.push(d.child(1));
                e = d.child(0)
            }
            _ => {
                args.reverse();
                return (e, args);
            }
        }
    }
}
fn expression_sort(a: &Arena, e: Expression) -> super::sort::Sort {
    if e.family().stage() == Stage::Type {
        super::sort::Sort::Upper(a.sort(e))
    } else {
        super::sort::Sort::Base(a.sort(e))
    }
}
fn recursive_case_argument(
    env: &Environment,
    elimination: Expression,
    inductive: InductiveId,
    ty: Expression,
    value: Expression,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let ty = normalize(env, ty)?;
    let d = a.data(ty);
    match d.op {
        Op::ProdTerm { rule, var } | Op::ProdType { rule, var } => {
            let domain = d.child(0);
            let value = shift(a, value, 1, 0)?;
            let argument = node(
                a,
                Family::at(
                    rule.domain.base(),
                    if rule.domain.is_upper() {
                        Stage::Type
                    } else {
                        Stage::Term
                    },
                ),
                rule.domain.base(),
                Op::Bound { index: 0 },
                &[],
            );
            let value = apply(a, rule, value, argument);
            let elimination = shift(a, elimination, 1, 0)?;
            let Some(body) =
                recursive_case_argument(env, elimination, inductive, d.child(1), value)?
            else {
                return Ok(None);
            };
            let rule = super::sort::ProductRule::new(rule.domain, expression_sort(a, body))?;
            Ok(Some(node(
                a,
                Family::at(rule.result.base(), body.family().stage()),
                rule.result.base(),
                if rule.domain.is_upper() {
                    Op::LambdaType { var, rule }
                } else {
                    Op::LambdaTerm { var, rule }
                },
                &[(domain, 0), (body, 1)],
            )))
        }
        _ => {
            let (head, _) = decompose_application(a, ty);
            if !matches!(a.data(head).op,Op::IndType{inductive:i} if i==inductive) {
                return Ok(None);
            }
            let mut data = a.data(elimination);
            data.fields[0][0].expression = value;
            Ok(Some(a.store(elimination.family(), data)))
        }
    }
}
fn reduce_inductive(
    env: &Environment,
    elimination: Expression,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let d = a.data(elimination);
    let Op::IndElim { inductive, .. } = d.op else {
        return Ok(None);
    };
    let (head, arguments) = decompose_application(a, d.child(0));
    let hd = a.data(head);
    let Op::IndCtor {
        inductive: actual,
        constructor,
    } = hd.op
    else {
        return Ok(None);
    };
    if actual != inductive {
        return Ok(None);
    }
    let spec = env.inductive(inductive).ok_or("unknown inductive")?;
    let mut ty = instantiate_telescope(
        a,
        *spec
            .constructors
            .get(constructor)
            .ok_or("unknown constructor")?,
        &hd.children(0),
    )?;
    let mut case_args = vec![];
    for arg in arguments {
        ty = normalize(env, ty)?;
        let td = a.data(ty);
        if !matches!(td.op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
            return Err("constructor applied to excess arguments".into());
        }
        case_args.push(arg);
        if let Some(ih) = recursive_case_argument(env, elimination, inductive, td.child(0), arg)? {
            case_args.push(ih)
        }
        ty = substitute(a, td.child(1), arg)?;
    }
    if matches!(a.data(ty).op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
        return Ok(None);
    }
    let mut sigma = expression_sort(a, elimination);
    let mut rules = vec![];
    for &arg in case_args.iter().rev() {
        let r = super::sort::ProductRule::new(expression_sort(a, arg), sigma)?;
        rules.push(r);
        sigma = r.result;
    }
    rules.reverse();
    let mut case = d.fields[3]
        .get(constructor)
        .ok_or("missing elimination branch")?
        .expression;
    for (arg, rule) in case_args.into_iter().zip(rules) {
        case = apply(a, rule, case, arg)
    }
    Ok(Some(case))
}

// These fields record typing premises; they are checked but do not form part of
// the computational syntax described in stratification4.
fn computational_fields(d: &Data) -> usize {
    match d.op {
        Op::SetRun => 4,
        Op::SetRunCase => 5,
        Op::BoxProgram => 2,
        _ => d.fields.len(),
    }
}

fn unfold_value(env: &Environment, mut value: Expression) -> Result<Expression, String> {
    let mut seen = std::collections::HashSet::new();
    while let Op::Constant { definition } = env.arena.data(value).op {
        if !seen.insert(definition) {
            return Err("cyclic Program constant".into());
        }
        value = env
            .definition(definition)
            .ok_or("unknown Program constant")?
            .body;
    }
    Ok(value)
}
pub fn closed_in_environment(env: &Environment, e: Expression) -> bool {
    fn go(
        env: &Environment,
        e: Expression,
        depth: usize,
        seen: &mut std::collections::HashSet<DefId>,
        cache: &mut std::collections::HashMap<(Expression, usize), bool>,
    ) -> bool {
        if let Some(&result) = cache.get(&(e, depth)) {
            return result;
        }
        let d = env.arena.data(e);
        let result = match d.op {
            Op::Bound { index } => index < depth,
            Op::ModuleParam { .. } | Op::ReflectedProgramParam { .. } => false,
            Op::Constant { definition } => {
                if !seen.insert(definition) {
                    return false;
                }
                let result = env
                    .definition(definition)
                    .is_some_and(|def| go(env, def.body, 0, seen, cache));
                seen.remove(&definition);
                result
            }
            _ => d
                .fields
                .iter()
                .flatten()
                .all(|c| go(env, c.expression, depth + c.depth, seen, cache)),
        };
        cache.insert((e, depth), result);
        result
    }
    go(
        env,
        e,
        0,
        &mut std::collections::HashSet::new(),
        &mut std::collections::HashMap::new(),
    )
}
/// Local binders must be abstracted before an expression becomes a named
/// declaration. Named module parameters remain explicit global references.
pub fn locally_closed(arena: &Arena, e: Expression) -> bool {
    fn visit(
        a: &Arena,
        e: Expression,
        depth: usize,
        seen: &mut std::collections::HashSet<(Expression, usize)>,
    ) -> bool {
        if !seen.insert((e, depth)) {
            return true;
        }
        let d = a.data(e);
        if let Op::Bound { index } = d.op {
            return index < depth;
        }
        d.fields
            .iter()
            .flatten()
            .all(|c| visit(a, c.expression, depth + c.depth, seen))
    }
    visit(arena, e, 0, &mut std::collections::HashSet::new())
}

// A Program step can correspond to zero or several Set steps (force/thunk is
// erased). Keep a certificate that still structurally reflects the residual.
fn advance_certificate(
    env: &Environment,
    program: Expression,
    mut certificate: Expression,
) -> Result<Expression, String> {
    for _ in 0..10_000 {
        if super::reflection::reflect_with_certificate(env, program, certificate.try_into()?)
            .is_ok()
        {
            return Ok(certificate);
        }
        certificate = reduce_once(env, certificate)?
            .ok_or("Program step has no corresponding certificate reduction")?;
    }
    Err("reflection correspondence fuel exhausted".into())
}
