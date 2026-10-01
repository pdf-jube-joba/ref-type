//! Reduction and CBPV evaluation on the common expression DAG.
use crate::{calculus::*, environment::Environment, ids::InductiveId, syntax::*};

fn app(env: &Environment, mode: Mode, function: Expression, argument: Expression) -> Expression {
    env.arena.alloc(Node::App {
        mode,
        function,
        argument,
    })
}
fn decompose(env: &Environment, mut e: Expression) -> (Expression, Vec<Expression>) {
    let mut args = vec![];
    while let Node::App {
        function, argument, ..
    } = env.arena.get(e)
    {
        args.push(argument);
        e = function;
    }
    args.reverse();
    (e, args)
}
fn unfold(env: &Environment, mut e: Expression) -> Result<Expression, String> {
    loop {
        match env.arena.get(e) {
            Node::Ascribe { term, .. } => e = term,
            Node::Definition { id, arguments } => {
                e = instantiate(&env.arena, env.definition(id)?.body, &arguments)?;
            }
            _ => return Ok(e),
        }
    }
}
fn recursive_argument(
    env: &Environment,
    elimination: Expression,
    inductive: InductiveId,
    ty: Expression,
    value: Expression,
) -> Result<Option<Expression>, String> {
    let ty = env.whnf(ty)?;
    if let Node::Product { var, domain, body } = env.arena.get(ty) {
        let value = app(
            env,
            Mode::Pure,
            shift(&env.arena, value, 1, 0)?,
            env.arena.bound(0),
        );
        let elimination = shift(&env.arena, elimination, 1, 0)?;
        let Some(body) = recursive_argument(env, elimination, inductive, body, value)? else {
            return Ok(None);
        };
        return Ok(Some(env.arena.alloc(Node::Lambda {
            mode: Mode::Pure,
            var,
            domain,
            body,
        })));
    }
    let (head, _) = decompose(env, ty);
    if !matches!(env.arena.get(head),Node::IndType {inductive:id,..} if id==inductive) {
        return Ok(None);
    }
    let mut node = env.arena.get(elimination);
    let Node::IndElim { scrutinee, .. } = &mut node else {
        return Err("expected induction".into());
    };
    *scrutinee = value;
    Ok(Some(env.arena.alloc(node)))
}
fn eliminate(
    env: &Environment,
    e: Expression,
    id: InductiveId,
    scrutinee: Expression,
    cases: &[Expression],
    recursive: bool,
) -> Result<Option<Expression>, String> {
    // Refinement introductions carry certificates, but their underlying value
    // is the same constructor seen by Set eliminators and record projections.
    let (head, args) = decompose(env, env.erased_head(scrutinee)?);
    let Node::IndCtor {
        inductive,
        constructor,
        parameters,
    } = env.arena.get(head)
    else {
        return Ok(None);
    };
    if inductive != id {
        return Ok(None);
    }
    let spec = env.inductives.get(&id).ok_or("unknown inductive")?;
    let mut declared = *spec
        .constructors
        .get(constructor)
        .ok_or("unknown constructor")?;
    let mut ty = instantiate(&env.arena, declared, &parameters)?;
    let mut branch = *cases.get(constructor).ok_or("missing elimination branch")?;
    for argument in args {
        let Node::Product { domain, body, .. } = env.arena.get(env.whnf(ty)?) else {
            return Err("constructor applied to excess arguments".into());
        };
        let Node::Product {
            domain: declared_domain,
            body: declared_body,
            ..
        } = env.arena.get(env.whnf(declared)?)
        else {
            return Err("expected declared constructor product".into());
        };
        branch = app(env, Mode::Pure, branch, argument);
        if recursive
            && env.recursive_field(id, declared_domain)?
            && let Some(ih) = recursive_argument(env, e, id, domain, argument)?
        {
            branch = app(env, Mode::Pure, branch, ih);
        }
        declared = declared_body;
        ty = instantiate(&env.arena, body, &[argument])?;
    }
    if matches!(env.arena.get(env.whnf(ty)?), Node::Product { .. }) {
        Ok(None)
    } else {
        Ok(Some(branch))
    }
}

/// Batch a maximal lambda spine using one simultaneous substitution.
pub(crate) fn head_application(
    env: &Environment,
    e: Expression,
) -> Result<Option<Expression>, String> {
    let Node::App { mode, .. } = env.arena.get(e) else {
        return Ok(None);
    };
    let mut args = vec![];
    let mut head = e;
    while let Node::App {
        mode: actual,
        function,
        argument,
    } = env.arena.get(head)
    {
        if actual != mode {
            break;
        }
        args.push(argument);
        head = function;
    }
    args.reverse();
    let original_head = head;
    head = env.erased_head(head)?;
    let mut consumed = 0;
    while let Node::Lambda {
        mode: actual, body, ..
    } = env.arena.get(head)
    {
        if actual != mode || consumed == args.len() {
            break;
        }
        consumed += 1;
        head = body;
    }
    if consumed == 0 && head == original_head {
        return Ok(None);
    }
    let mut result = instantiate(&env.arena, head, &args[..consumed])?;
    for &argument in &args[consumed..] {
        result = app(env, mode, result, argument);
    }
    Ok((result != e).then_some(result))
}

pub fn root(env: &Environment, e: Expression) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let result = match a.get(e) {
        Node::Ascribe { term, .. } => term,
        Node::Definition { id, arguments } => {
            let d = env.definition(id)?;
            if d.context.len() != arguments.len() {
                return Err("definition parameter count mismatch".into());
            }
            instantiate(a, d.body, &arguments)?
        }
        Node::App {
            mode,
            function,
            argument,
        } => match a.get(function) {
            Node::Lambda {
                mode: actual, body, ..
            } if mode == actual => instantiate(a, body, &[argument])?,
            Node::SetStepMatch {
                on_continue,
                on_finish,
                ..
            } if mode == Mode::Pure => match a.get(env.whnf(argument)?) {
                Node::Continue { next, .. } => app(env, Mode::Pure, on_continue, next),
                Node::Finish { output, .. } => app(env, Mode::Pure, on_finish, output),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        },
        Node::Pred {
            subset, element, ..
        } => match a.get(subset) {
            Node::Subset { predicate, .. } => instantiate(a, predicate, &[element])?,
            _ => return Ok(None),
        },
        Node::Reflect { term } => return env.reflect_step(term),
        Node::ProgramStepMatch {
            scrutinee,
            on_continue,
            on_finish,
            ..
        } => match a.get(unfold(env, scrutinee)?) {
            Node::ProgramContinue { next, .. } => app(env, Mode::Computation, on_continue, next),
            Node::ProgramFinish { output, .. } => app(env, Mode::Computation, on_finish, output),
            _ => return Ok(None),
        },
        Node::IndElim {
            inductive,
            scrutinee,
            cases,
            ..
        } => return eliminate(env, e, inductive, scrutinee, &cases, true),
        Node::Case {
            inductive,
            scrutinee,
            branches,
            ..
        } => return eliminate(env, e, inductive, scrutinee, &branches, false),
        Node::Force { value } => match a.get(unfold(env, value)?) {
            Node::ThunkValue { computation } => computation,
            _ => return Ok(None),
        },
        Node::ValueLet { value, body, .. } => instantiate(a, body, &[value])?,
        Node::Sequence {
            computation, body, ..
        } => match a.get(computation) {
            Node::Return { value } => instantiate(a, body, &[value])?,
            _ => return Ok(None),
        },
        Node::ProgramCase {
            inductive,
            scrutinee,
            branches,
            ..
        } => match a.get(unfold(env, scrutinee)?) {
            Node::InductiveConstructor {
                inductive: id,
                constructor,
                fields,
                ..
            } if id == inductive => instantiate(
                a,
                *branches.get(constructor).ok_or("missing branch")?,
                &fields,
            )?,
            _ => return Ok(None),
        },
        Node::SetCase {
            inductive,
            scrutinee,
            branches,
            ..
        } => {
            let (head, args) = decompose(env, scrutinee);
            let id = env
                .datatypes
                .get(&inductive)
                .ok_or("unknown datatype")?
                .reflected;
            match a.get(head) {
                Node::IndCtor {
                    inductive,
                    constructor,
                    ..
                } if inductive == id => instantiate(
                    a,
                    *branches.get(constructor).ok_or("missing branch")?,
                    &args,
                )?,
                _ => return Ok(None),
            }
        }
        Node::BoxProgram {
            program_ty,
            program,
        } => {
            let Some(program) = reduce_once(env, program)? else {
                return Ok(None);
            };
            a.alloc(Node::BoxProgram {
                program_ty,
                program,
            })
        }
        Node::ForceBox { program_ty, boxed } => {
            let Node::BoxProgram {
                program_ty: actual,
                program,
            } = a.get(boxed)
            else {
                return Ok(None);
            };
            if !convertible(env, program_ty, actual)? || reduce_once(env, program)?.is_some() {
                return Ok(None);
            }
            a.alloc(Node::Reflect { term: program })
        }
        Node::BoxApp {
            function, argument, ..
        } => {
            let Node::BoxProgram {
                program: function,
                program_ty,
            } = a.get(function)
            else {
                return Ok(None);
            };
            let Node::Product { body: codomain, .. } = a.get(env.whnf(program_ty)?) else {
                return Err("boxed function type must be product".into());
            };
            let Node::BoxProgram { program, .. } = a.get(argument) else {
                return Ok(None);
            };
            let Node::Return { value } = a.get(program) else {
                return Ok(None);
            };
            a.alloc(Node::BoxProgram {
                program_ty: instantiate(a, codomain, &[value])?,
                program: app(env, Mode::Computation, function, value),
            })
        }
        Node::BoxTypeApp {
            function, argument, ..
        } => {
            let Node::BoxProgram {
                program: function,
                program_ty,
            } = a.get(function)
            else {
                return Ok(None);
            };
            let Node::Product { body: codomain, .. } = a.get(env.whnf(program_ty)?) else {
                return Err("boxed function type must be product".into());
            };
            a.alloc(Node::BoxProgram {
                program_ty: instantiate(a, codomain, &[argument])?,
                program: app(env, Mode::Computation, function, argument),
            })
        }
        Node::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            let transition = app(env, Mode::Pure, step, initial);
            let transition_equality = a.alloc(Node::IdRefl {
                element: transition,
            });
            a.alloc(Node::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            })
        }
        Node::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => {
            let function = a.alloc(Node::Force { value: step });
            let transition = app(env, Mode::Computation, function, initial);
            let reflected = a.alloc(Node::Reflect { term: transition });
            let transition_equality = a.alloc(Node::IdRefl { element: reflected });
            a.alloc(Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            })
        }
        Node::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => match a.get(transition) {
            Node::Finish { output, .. } => output,
            Node::Continue { next, .. } => {
                let accessibility = a.alloc(Node::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from: initial,
                    to: next,
                    accessibility,
                    transition: transition_equality,
                });
                a.alloc(Node::SetRun {
                    state_ty,
                    result_ty,
                    step,
                    initial: next,
                    accessibility,
                })
            }
            _ => return Ok(None),
        },
        Node::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => {
            let Node::Return { value } = a.get(transition) else {
                return Ok(None);
            };
            match a.get(unfold(env, value)?) {
                Node::ProgramFinish { output, .. } => a.alloc(Node::Return { value: output }),
                Node::ProgramContinue { next, .. } => {
                    let rf = |term| a.alloc(Node::Reflect { term });
                    let accessibility = a.alloc(Node::AccDescent {
                        state_ty: rf(state_ty),
                        result_ty: rf(result_ty),
                        step: rf(step),
                        from: rf(initial),
                        to: rf(next),
                        accessibility,
                        transition: transition_equality,
                    });
                    a.alloc(Node::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial: next,
                        accessibility,
                    })
                }
                _ => return Ok(None),
            }
        }
        _ => return Ok(None),
    };
    tracing::trace!(target:"ref_type::reduction",?e,?result,"root reduction");
    Ok(Some(result))
}

pub(crate) fn map_head(
    env: &Environment,
    e: Expression,
    mut map: impl FnMut(Expression) -> Result<Expression, String>,
) -> Result<Expression, String> {
    let node = env.arena.get(e);
    let slots: &[usize] = match node {
        Node::App { .. } => &[0],
        Node::Pred { .. } => &[1],
        Node::ForceBox { .. } => &[1],
        Node::BoxApp { .. } => &[0, 1],
        Node::BoxTypeApp { .. } => &[0],
        Node::SetRunCase { .. } | Node::RunCase { .. } => &[4],
        Node::IndElim { .. } | Node::Case { .. } => &[0],
        Node::SetCase { .. } => &[0],
        Node::Sequence { .. } => &[1],
        _ => &[],
    };
    let mut i = 0;
    env.arena.map_children(e, |child, _| {
        let slot = i;
        i += 1;
        if slots.contains(&slot) {
            map(child)
        } else {
            Ok(child)
        }
    })
}
pub fn reduce_once(env: &Environment, e: Expression) -> Result<Option<Expression>, String> {
    if let Some(next) = root(env, e)? {
        return Ok(Some(next));
    }
    let node = env.arena.get(e);
    let slots: Option<&[usize]> = match node {
        Node::Lambda {
            mode: Mode::Computation,
            ..
        }
        | Node::ThunkValue { .. }
        | Node::ProgramContinue { .. }
        | Node::ProgramFinish { .. }
        | Node::InductiveConstructor { .. }
        | Node::Return { .. }
        | Node::Force { .. }
        | Node::ProgramCase { .. }
        | Node::ProgramStepMatch { .. }
        | Node::Run { .. }
        | Node::BoxType { .. }
        | Node::BoxProgram { .. } => Some(&[]),
        Node::App {
            mode: Mode::Computation,
            ..
        } => Some(&[0]),
        Node::Sequence { .. } => Some(&[1]),
        Node::RunCase { .. } => Some(&[4]),
        Node::ForceBox { .. } => Some(&[1]),
        Node::BoxApp { .. } => Some(&[0, 1]),
        Node::BoxTypeApp { .. } => Some(&[0]),
        _ => None,
    };
    let mut changed = false;
    let mut i = 0;
    let result = env
        .arena
        .map_children(e, |child, _| -> Result<Expression, String> {
            let slot = i;
            i += 1;
            if !changed
                && slots.is_none_or(|slots| slots.contains(&slot))
                && let Some(next) = reduce_once(env, child)?
            {
                changed = true;
                Ok(next)
            } else {
                Ok(child)
            }
        })?;
    Ok(changed.then_some(result))
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(Expression),
    OutOfFuel(Expression),
}
#[tracing::instrument(target = "ref_type::reduction", level = "debug", skip(env), fields(?e, fuel))]
pub fn evaluate(env: &Environment, mut e: Expression, fuel: usize) -> Result<Evaluation, String> {
    for _ in 0..fuel {
        match reduce_once(env, e)? {
            Some(next) => e = next,
            None => {
                tracing::debug!(target: "ref_type::reduction", "evaluation finished");
                return Ok(Evaluation::Normal(e));
            }
        }
    }
    Ok(if reduce_once(env, e)?.is_none() {
        Evaluation::Normal(e)
    } else {
        Evaluation::OutOfFuel(e)
    })
}
pub fn normalize(env: &Environment, e: Expression) -> Result<Expression, String> {
    match evaluate(env, e, 100_000)? {
        Evaluation::Normal(e) => Ok(e),
        Evaluation::OutOfFuel(_) => Err("normalization fuel exhausted".into()),
    }
}
/// Expose explicit beta redexes while retaining opaque definition heads.
fn beta_head(env: &Environment, e: Expression, erase: bool) -> Result<Expression, String> {
    match env.arena.get(e) {
        Node::SubsetIntro { element, .. } if erase => beta_head(env, element, erase),
        Node::App {
            mode,
            function,
            argument,
        } => {
            let function = beta_head(env, function, erase)?;
            if let Node::Lambda {
                mode: actual, body, ..
            } = env.arena.get(function)
                && mode == actual {
                    return beta_head(env, instantiate(&env.arena, body, &[argument])?, erase);
                }
            Ok(env.arena.alloc(Node::App {
                mode,
                function,
                argument,
            }))
        }
        _ => Ok(e),
    }
}
pub fn convertible(env: &Environment, left: Expression, right: Expression) -> Result<bool, String> {
    conversion(env, left, right, false)
}
pub fn erased_convertible(
    env: &Environment,
    left: Expression,
    right: Expression,
) -> Result<bool, String> {
    conversion(env, left, right, true)
}
fn conversion(
    env: &Environment,
    left: Expression,
    right: Expression,
    erase: bool,
) -> Result<bool, String> {
    fn compare(
        env: &Environment,
        left: Expression,
        right: Expression,
        erase: bool,
        seen: &mut rustc_hash::FxHashSet<(Expression, Expression)>,
    ) -> Result<bool, String> {
        let cacheable = !env.arena.contains_meta(left) && !env.arena.contains_meta(right);
        let key = if left.index() <= right.index() {
            (left, right, erase)
        } else {
            (right, left, erase)
        };
        if cacheable && let Some(&equal) = env.conversions.borrow().get(&key) {
            return Ok(equal);
        }
        let result = (|| {
            if alpha_equal(&env.arena, left, right) || !seen.insert((left, right)) {
                return Ok(true);
            }
            let left = beta_head(env, left, erase)?;
            let right = beta_head(env, right, erase)?;
            if alpha_equal(&env.arena, left, right) {
                return Ok(true);
            }
            if skeleton(&env.arena, left) == skeleton(&env.arena, right) {
                let mut congruent = true;
                for ((l, ld), (r, rd)) in comparison_children(&env.arena, left)
                    .into_iter()
                    .zip(comparison_children(&env.arena, right))
                {
                    if ld != rd || !compare(env, l, r, erase, &mut seen.clone())? {
                        congruent = false;
                        break;
                    }
                }
                if congruent {
                    return Ok(true);
                }
            }
            let left = if erase {
                env.erased_head(left)?
            } else {
                env.whnf(left)?
            };
            let right = if erase {
                env.erased_head(right)?
            } else {
                env.whnf(right)?
            };
            if alpha_equal(&env.arena, left, right) {
                return Ok(true);
            }
            if skeleton(&env.arena, left) != skeleton(&env.arena, right) {
                return Ok(false);
            }
            for ((l, ld), (r, rd)) in comparison_children(&env.arena, left)
                .into_iter()
                .zip(comparison_children(&env.arena, right))
            {
                if ld != rd || !compare(env, l, r, erase, seen)? {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        if cacheable && let Ok(equal) = result {
            env.conversions.borrow_mut().insert(key, equal);
        }
        result
    }
    compare(
        env,
        left,
        right,
        erase,
        &mut rustc_hash::FxHashSet::default(),
    )
}

/// Locate the first rigid difference after head reduction, for diagnostics.
pub fn first_difference(
    env: &Environment,
    left: Expression,
    right: Expression,
) -> Result<Option<(Vec<usize>, Expression, Expression)>, String> {
    fn walk(
        env: &Environment,
        left: Expression,
        right: Expression,
        path: &mut Vec<usize>,
    ) -> Result<Option<(Vec<usize>, Expression, Expression)>, String> {
        if erased_convertible(env, left, right)? {
            return Ok(None);
        }
        let left = env.erased_head(left)?;
        let right = env.erased_head(right)?;
        if skeleton(&env.arena, left) != skeleton(&env.arena, right) {
            return Ok(Some((path.clone(), left, right)));
        }
        for (i, ((left, _), (right, _))) in comparison_children(&env.arena, left)
            .into_iter()
            .zip(comparison_children(&env.arena, right))
            .enumerate()
        {
            path.push(i);
            if let Some(diff) = walk(env, left, right, path)? {
                return Ok(Some(diff));
            }
            path.pop();
        }
        Ok(None)
    }
    walk(env, left, right, &mut vec![])
}
