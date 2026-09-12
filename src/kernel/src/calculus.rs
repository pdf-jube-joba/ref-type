//! Family-preserving substitution, conversion, and syntax-directed evaluation.
use super::{
    construction as build,
    environment::Environment,
    sort::*,
    structure::{self, Traversal},
    syntax::*,
};
use crate::ids::*;
use std::collections::HashMap;

pub(crate) fn expressions<T: Copy + Into<Expression>>(values: &[T]) -> Vec<Expression> {
    values.iter().map(|&e| e.into()).collect()
}
pub(crate) fn map_children(
    arena: &Arena,
    e: Expression,
    map: impl FnMut(Expression, usize) -> Result<Expression, String>,
) -> Result<Expression, String> {
    structure::map_children(arena, e, Traversal::All, map)
}
pub fn shift(
    arena: &Arena,
    e: impl Into<Expression>,
    amount: usize,
    cutoff: usize,
) -> Result<Expression, String> {
    fn walk(
        a: &Arena,
        e: Expression,
        n: usize,
        cutoff: usize,
        cache: &mut HashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, String> {
        if a.max_loose_bound(e).is_none_or(|index| index < cutoff) {
            return Ok(e);
        }
        if let Some(&result) = cache.get(&(e, cutoff)) {
            return Ok(result);
        }
        if let Some(index) = structure::bound_index(a, e) {
            return build::bound(
                a,
                a.sort(e),
                e.family().stage(),
                index.checked_add(n).ok_or("bound index overflow")?,
            );
        }
        let result = map_children(a, e, |child, depth| {
            walk(a, child, n, cutoff + depth, cache)
        })?;
        cache.insert((e, cutoff), result);
        Ok(result)
    }
    let e = e.into();
    if amount == 0 {
        return Ok(e);
    }
    walk(arena, e, amount, cutoff, &mut HashMap::new())
}
pub fn substitute(
    arena: &Arena,
    body: impl Into<Expression>,
    argument: impl Into<Expression>,
) -> Result<Expression, String> {
    fn walk(
        a: &Arena,
        e: Expression,
        argument: Expression,
        depth: usize,
        cache: &mut HashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, String> {
        if a.max_loose_bound(e).is_none_or(|index| index < depth) {
            return Ok(e);
        }
        if let Some(&result) = cache.get(&(e, depth)) {
            return Ok(result);
        }
        if let Some(index) = structure::bound_index(a, e) {
            if index == depth {
                if e.family() != argument.family() || a.sort(e) != a.sort(argument) {
                    return Err("substitution argument has the wrong family or level".into());
                }
                return shift(a, argument, depth, 0);
            }
            return build::bound(a, a.sort(e), e.family().stage(), index - 1);
        }
        let result = map_children(a, e, |child, n| walk(a, child, argument, depth + n, cache))?;
        cache.insert((e, depth), result);
        Ok(result)
    }
    walk(arena, body.into(), argument.into(), 0, &mut HashMap::new())
}
pub fn instantiate_telescope(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
) -> Result<Expression, String> {
    let mut result = e;
    for (i, &argument) in arguments.iter().enumerate().rev() {
        result = substitute(arena, result, shift(arena, argument, i, 0)?)?;
    }
    Ok(result)
}
pub fn contains_bound(arena: &Arena, e: Expression, index: usize) -> bool {
    if let Some(i) = structure::bound_index(arena, e) {
        return i == index;
    }
    let mut found = false;
    structure::visit_children(arena, e, |child, depth| {
        found |= !found && contains_bound(arena, child, index + depth);
    });
    found
}
pub fn is_closed(arena: &Arena, e: Expression) -> bool {
    fn go(a: &Arena, e: Expression, depth: usize) -> bool {
        if let Some(index) = structure::bound_index(a, e) {
            return index < depth;
        }
        if structure::module_parameter(a, e).is_some()
            || structure::reflected_parameter(a, e).is_some()
        {
            return false;
        }
        let mut closed = true;
        structure::visit_children(a, e, |child, n| {
            closed = closed && go(a, child, depth + n);
        });
        closed
    }
    go(arena, e, 0)
}
pub fn substitute_parameters(
    arena: &Arena,
    e: Expression,
    parameters: &HashMap<ModuleParamId, Expression>,
) -> Result<Expression, String> {
    fn go(
        a: &Arena,
        e: Expression,
        p: &HashMap<ModuleParamId, Expression>,
        depth: usize,
    ) -> Result<Expression, String> {
        if let Some(parameter) = structure::module_parameter(a, e)
            && let Some(&argument) = p.get(&parameter)
        {
            if e.family() != argument.family() || a.sort(e) != a.sort(argument) {
                return Err("module argument classification mismatch".into());
            }
            return shift(a, argument, depth, 0);
        }
        map_children(a, e, |child, n| go(a, child, p, depth + n))
    }
    go(arena, e, parameters, 0)
}
pub fn remap_ids(
    arena: &Arena,
    e: Expression,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    datatypes: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Result<Expression, String> {
    let e = map_children(arena, e, |child, _| {
        remap_ids(arena, child, definitions, inductives, datatypes)
    })?;
    Ok(structure::remap_references(
        arena,
        e,
        definitions,
        inductives,
        datatypes,
    ))
}
pub fn alpha_equal(arena: &Arena, left: Expression, right: Expression) -> bool {
    left == right
        || structure::compare_children(arena, left, right, |left, right| {
            Ok(alpha_equal(arena, left, right))
        })
        .expect("alpha comparison cannot fail")
}
pub fn convertible(env: &Environment, a: Expression, b: Expression) -> Result<bool, String> {
    fn go(
        env: &Environment,
        a: Expression,
        b: Expression,
        seen: &mut HashMap<(Expression, Expression), bool>,
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
        let result = alpha_equal(&env.arena, ah, bh)
            || structure::compare_children(&env.arena, ah, bh, |left, right| {
                go(env, left, right, seen)
            })?;
        seen.insert((a, b), result);
        Ok(result)
    }
    go(env, a, b, &mut HashMap::new())
}
pub fn reduce_once(
    env: &Environment,
    e: impl Into<Expression>,
) -> Result<Option<Expression>, String> {
    let e = e.into();
    if let Some(result) = reduce_root(env, e)? {
        return Ok(Some(result));
    }
    let mut changed = false;
    let result = structure::map_children(&env.arena, e, Traversal::Evaluation, |child, _| {
        if !changed && let Some(result) = reduce_once(env, child)? {
            changed = true;
            return Ok(result);
        }
        Ok(child)
    })?;
    Ok(changed.then_some(result))
}
pub fn whnf(env: &Environment, e: Expression) -> Result<Expression, String> {
    if let Some(&cached) = env.head_cache.borrow().get(&e) {
        return Ok(cached);
    }
    let original = e;
    let mut e = e;
    for _ in 0..100_000 {
        if let Some(next) = reduce_root(env, e)? {
            e = next;
            continue;
        }
        let next =
            structure::map_children(&env.arena, e, Traversal::Head, |child, _| whnf(env, child))?;
        if next == e {
            env.head_cache.borrow_mut().insert(original, e);
            return Ok(e);
        }
        e = next;
    }
    Err("head normalization fuel exhausted".into())
}
pub(crate) fn decompose_application(
    arena: &Arena,
    mut e: Expression,
) -> (Expression, Vec<Expression>) {
    let mut arguments = vec![];
    while let Some(app) = structure::application(arena, e) {
        arguments.push(app.argument);
        e = app.function;
    }
    arguments.reverse();
    (e, arguments)
}
fn expression_sort(a: &Arena, e: Expression) -> Sort {
    if e.family().stage() == Stage::Type {
        Sort::Upper(a.sort(e))
    } else {
        Sort::Base(a.sort(e))
    }
}
// Test the declared field before instantiating parameters: Pair<Pair<_>> must
// not acquire an induction hypothesis merely because its parameter is a Pair.
pub(crate) fn recursive_constructor_field(
    env: &Environment,
    inductive: InductiveId,
    mut ty: Expression,
) -> Result<bool, String> {
    loop {
        ty = whnf(env, ty)?;
        if let Some(product) = structure::product(&env.arena, ty) {
            ty = product.body;
        } else {
            let (head, _) = decompose_application(&env.arena, ty);
            return Ok(
                structure::inductive_type(&env.arena, head).is_some_and(|(id, _)| id == inductive)
            );
        }
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
    if let Some(product) = structure::product(a, ty) {
        let rule = product.rule;
        let value = shift(a, value, 1, 0)?;
        let argument = build::bound(
            a,
            rule.domain.base(),
            if rule.domain.is_upper() {
                Stage::Type
            } else {
                Stage::Term
            },
            0,
        )?;
        let value = build::apply(a, rule, value, argument)?;
        let elimination = shift(a, elimination, 1, 0)?;
        let Some(body) = recursive_case_argument(env, elimination, inductive, product.body, value)?
        else {
            return Ok(None);
        };
        let rule = ProductRule::new(rule.domain, expression_sort(a, body))?;
        return Ok(Some(build::lambda(
            a,
            rule,
            product.var,
            product.domain,
            body,
        )?));
    }
    let (head, _) = decompose_application(a, ty);
    if !structure::inductive_type(a, head).is_some_and(|(id, _)| id == inductive) {
        return Ok(None);
    }
    // IndElim's only head position is its scrutinee.
    Ok(Some(structure::map_children(
        a,
        elimination,
        Traversal::Head,
        |_, _| Ok(value),
    )?))
}
fn reduce_inductive(
    env: &Environment,
    elimination: Expression,
    inductive: InductiveId,
    scrutinee: Expression,
    cases: &[LogicalArgument],
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let (head, arguments) = decompose_application(a, scrutinee);
    let Some((actual, constructor, parameters)) = structure::inductive_constructor(a, head) else {
        return Ok(None);
    };
    if actual != inductive {
        return Ok(None);
    }
    let spec = env.inductive(inductive).ok_or("unknown inductive")?;
    let mut declared_ty = *spec
        .constructors
        .get(constructor)
        .ok_or("unknown constructor")?;
    let mut ty = instantiate_telescope(a, declared_ty, &expressions(&parameters))?;
    let mut case_args = vec![];
    for argument in arguments {
        ty = normalize(env, ty)?;
        let product = structure::product(a, ty).ok_or("constructor applied to excess arguments")?;
        case_args.push(argument);
        let declared = structure::product(a, whnf(env, declared_ty)?)
            .ok_or("expected declared constructor product")?;
        if recursive_constructor_field(env, inductive, declared.domain)?
            && let Some(ih) =
                recursive_case_argument(env, elimination, inductive, product.domain, argument)?
        {
            case_args.push(ih);
        }
        declared_ty = declared.body;
        ty = substitute(a, product.body, argument)?;
    }
    if structure::product(a, ty).is_some() {
        return Ok(None);
    }
    let mut sigma = expression_sort(a, elimination);
    let mut rules = vec![];
    for &argument in case_args.iter().rev() {
        let rule = ProductRule::new(expression_sort(a, argument), sigma)?;
        rules.push(rule);
        sigma = rule.result;
    }
    rules.reverse();
    let mut case: Expression =
        (*cases.get(constructor).ok_or("missing elimination branch")?).into();
    for (argument, rule) in case_args.into_iter().zip(rules) {
        case = build::apply(a, rule, case, argument)?;
    }
    Ok(Some(case))
}
fn unfold_value(env: &Environment, mut value: Expression) -> Result<Expression, String> {
    let mut seen = std::collections::HashSet::new();
    while let Some(definition) = structure::constant(&env.arena, value) {
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
        cache: &mut HashMap<(Expression, usize), bool>,
    ) -> bool {
        if let Some(&result) = cache.get(&(e, depth)) {
            return result;
        }
        let a = &env.arena;
        let result = if let Some(index) = structure::bound_index(a, e) {
            index < depth
        } else if structure::module_parameter(a, e).is_some()
            || structure::reflected_parameter(a, e).is_some()
        {
            false
        } else if let Some(definition) = structure::constant(a, e) {
            if !seen.insert(definition) {
                return false;
            }
            let result = env
                .definition(definition)
                .is_some_and(|def| go(env, def.body, 0, seen, cache));
            seen.remove(&definition);
            result
        } else {
            let mut result = true;
            structure::visit_children(a, e, |child, n| {
                result = result && go(env, child, depth + n, seen, cache);
            });
            result
        };
        cache.insert((e, depth), result);
        result
    }
    go(
        env,
        e,
        0,
        &mut std::collections::HashSet::new(),
        &mut HashMap::new(),
    )
}
/// Local binders must be abstracted before a named declaration is registered.
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
        if let Some(index) = structure::bound_index(a, e) {
            return index < depth;
        }
        let mut closed = true;
        structure::visit_children(a, e, |child, n| {
            closed = closed && visit(a, child, depth + n, seen);
        });
        closed
    }
    visit(arena, e, 0, &mut std::collections::HashSet::new())
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
fn reduce_application(
    env: &Environment,
    rule: ProductRule,
    function: Expression,
    argument: Expression,
) -> Result<Option<Expression>, String> {
    rule.validate()?;
    match structure::lambda(&env.arena, function) {
        Some(lambda) if lambda.rule == rule => {
            Ok(Some(substitute(&env.arena, lambda.body, argument)?))
        }
        _ => Ok(None),
    }
}
fn reduce_force(env: &Environment, value: ValueTerm) -> Result<Option<Expression>, String> {
    let value: ValueTerm = unfold_value(env, value.into())?.try_into()?;
    Ok(match env.arena.read(value).form {
        ValueTermForm::ThunkValue { computation } => Some(computation.into()),
        _ => None,
    })
}
fn reduce_sequence(
    env: &Environment,
    computation: ComputationTerm,
    body: ComputationTerm,
) -> Result<Option<Expression>, String> {
    match env.arena.read(computation).form {
        ComputationTermForm::Return { value } => Ok(Some(substitute(&env.arena, body, value)?)),
        _ => Ok(None),
    }
}
fn reduce_box_program(
    env: &Environment,
    level: usize,
    program_ty: ProgramType,
    program: ProgramTerm,
    certified_reflection: SetTerm,
) -> Result<Option<Expression>, String> {
    if let ProgramTerm::ComputationTerm(computation) = program
        && let Some(next) = reduce_once(env, computation)?
    {
        let certificate = advance_certificate(env, next, certified_reflection.into())?;
        return Ok(Some(
            env.arena
                .alloc(SetTermNode {
                    level,
                    form: SetTermForm::BoxProgram {
                        program_ty,
                        program: next.try_into()?,
                        certified_reflection: certificate.try_into()?,
                    },
                })
                .into(),
        ));
    }
    Ok(None)
}
fn reduce_force_box(
    env: &Environment,
    program_ty: ProgramType,
    boxed: SetTerm,
) -> Result<Option<Expression>, String> {
    if let SetTermForm::BoxProgram {
        program_ty: actual,
        program,
        certified_reflection,
    } = env.arena.read(boxed).form
        && convertible(env, program_ty.into(), actual.into())?
        && (matches!(program, ProgramTerm::ValueTerm(_)) || reduce_once(env, program)?.is_none())
    {
        return Ok(Some(certified_reflection.into()));
    }
    Ok(None)
}
fn reduce_box_application(
    env: &Environment,
    rule: ProductRule,
    codomain: ComputationType,
    function: SetTerm,
    argument: Expression,
    type_application: bool,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let SetTermForm::BoxProgram {
        program: function,
        certified_reflection,
        ..
    } = a.read(function).form
    else {
        return Ok(None);
    };
    let (argument, reflected_argument) = if type_application {
        (argument, super::reflection::reflect(env, argument)?)
    } else {
        let argument: SetTerm = argument.try_into()?;
        let SetTermForm::BoxProgram {
            program,
            certified_reflection,
            ..
        } = a.read(argument).form
        else {
            return Ok(None);
        };
        (program.into(), certified_reflection.into())
    };
    let result_ty = if type_application {
        substitute(a, codomain, argument)?
    } else {
        codomain.into()
    };
    let program = build::apply(a, rule, function.into(), argument)?;
    let certificate = build::apply(
        a,
        rule.reflected(),
        certified_reflection.into(),
        reflected_argument,
    )?;
    Ok(Some(
        a.alloc(SetTermNode {
            level: a.sort(result_ty).level().ok_or("expected Program type")?,
            form: SetTermForm::BoxProgram {
                program_ty: result_ty.try_into()?,
                program: program.try_into()?,
                certified_reflection: certificate.try_into()?,
            },
        })
        .into(),
    ))
}
fn reduce_run(
    env: &Environment,
    level: usize,
    state_ty: ValueType,
    result_ty: ValueType,
    step: ValueTerm,
    initial: ValueTerm,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let i = a.sort(state_ty).level().ok_or("run requires a level")?;
    let rule = ProductRule::new(
        Sort::Base(BaseSort::Value(i)),
        Sort::Base(BaseSort::Computation(i)),
    )?;
    let force = a.alloc(ComputationTermNode {
        level: i,
        form: ComputationTermForm::Force { value: step },
    });
    let transition = build::apply(a, rule, force.into(), initial.into())?.try_into()?;
    Ok(Some(
        a.alloc(ComputationTermNode {
            level,
            form: ComputationTermForm::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            },
        })
        .into(),
    ))
}
fn reduce_set_run(
    env: &Environment,
    level: usize,
    state_ty: SetType,
    result_ty: SetType,
    step: SetTerm,
    initial: SetTerm,
    accessibility: PropTerm,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let b = a.sort(state_ty);
    let rule = ProductRule::new(Sort::Base(b), Sort::Base(b))?;
    let transition: SetTerm = build::apply(a, rule, step.into(), initial.into())?.try_into()?;
    let transition_equality = a.alloc(PropTermNode {
        form: PropTermForm::IdRefl {
            element: transition,
        },
    });
    Ok(Some(
        a.alloc(SetTermNode {
            level,
            form: SetTermForm::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            },
        })
        .into(),
    ))
}
fn reduce_run_case(
    env: &Environment,
    level: usize,
    state_ty: ValueType,
    result_ty: ValueType,
    step: ValueTerm,
    transition: ComputationTerm,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let ComputationTermForm::Return { value } = a.read(transition).form else {
        return Ok(None);
    };
    let value: ValueTerm = unfold_value(env, value.into())?.try_into()?;
    Ok(match a.read(value).form {
        ValueTermForm::Finish { output, .. } => Some(
            a.alloc(ComputationTermNode {
                level,
                form: ComputationTermForm::Return { value: output },
            })
            .into(),
        ),
        ValueTermForm::Continue { next, .. } => Some(
            a.alloc(ComputationTermNode {
                level,
                form: ComputationTermForm::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial: next,
                },
            })
            .into(),
        ),
        _ => None,
    })
}
struct SetRunCase {
    state_ty: SetType,
    result_ty: SetType,
    step: SetTerm,
    initial: SetTerm,
    transition: SetTerm,
    accessibility: PropTerm,
    transition_equality: PropTerm,
}

fn reduce_set_run_case(
    env: &Environment,
    level: usize,
    case: SetRunCase,
) -> Result<Option<Expression>, String> {
    let SetRunCase {
        state_ty,
        result_ty,
        step,
        initial,
        transition,
        accessibility,
        transition_equality,
    } = case;
    let a = &env.arena;
    Ok(match a.read(transition).form {
        SetTermForm::Finish { output, .. } => Some(output.into()),
        SetTermForm::Continue { next, .. } => {
            let accessibility = a.alloc(PropTermNode {
                form: PropTermForm::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from: initial,
                    to: next,
                    accessibility,
                    transition: transition_equality,
                },
            });
            Some(
                a.alloc(SetTermNode {
                    level,
                    form: SetTermForm::SetRun {
                        state_ty,
                        result_ty,
                        step,
                        initial: next,
                        accessibility,
                    },
                })
                .into(),
            )
        }
        _ => None,
    })
}
fn reduce_pred(
    env: &Environment,
    subset: SetTerm,
    element: SetTerm,
) -> Result<Option<Expression>, String> {
    match env.arena.read(subset).form {
        SetTermForm::Subset { predicate, .. } => {
            Ok(Some(substitute(&env.arena, predicate, element)?))
        }
        _ => Ok(None),
    }
}
fn reduce_recursor(
    env: &Environment,
    rule: ProductRule,
    on_continue: Expression,
    on_finish: Expression,
    scrutinee: SetTerm,
) -> Result<Option<Expression>, String> {
    match env.arena.read(scrutinee).form {
        SetTermForm::Continue { next, .. } => Ok(Some(build::apply(
            &env.arena,
            rule,
            on_continue,
            next.into(),
        )?)),
        SetTermForm::Finish { output, .. } => Ok(Some(build::apply(
            &env.arena,
            rule,
            on_finish,
            output.into(),
        )?)),
        _ => Ok(None),
    }
}
fn reduce_case(
    env: &Environment,
    scrutinee: ValueTerm,
    branches: &[ComputationTerm],
) -> Result<Option<Expression>, String> {
    let value: ValueTerm = unfold_value(env, scrutinee.into())?.try_into()?;
    let node = env.arena.read(value);
    let ValueTermForm::InductiveConstructor {
        constructor,
        fields,
        ..
    } = &node.form
    else {
        return Ok(None);
    };
    let branch = *branches.get(*constructor).ok_or("case branch missing")?;
    Ok(Some(instantiate_telescope(
        &env.arena,
        branch.into(),
        &expressions(fields),
    )?))
}
fn reduce_set_case(
    env: &Environment,
    scrutinee: SetTerm,
    branches: &[SetTerm],
) -> Result<Option<Expression>, String> {
    let (head, arguments) = decompose_application(&env.arena, scrutinee.into());
    let Some((_, constructor, _)) = structure::inductive_constructor(&env.arena, head) else {
        return Ok(None);
    };
    let branch = *branches.get(constructor).ok_or("case branch missing")?;
    Ok(Some(instantiate_telescope(
        &env.arena,
        branch.into(),
        &arguments,
    )?))
}
fn reduce_root(env: &Environment, e: Expression) -> Result<Option<Expression>, String> {
    let root = match e {
        Expression::SetTerm(h) => reduce_set_term_root(env, h)?,
        Expression::SetType(h) => reduce_set_type_root(env, h)?,
        Expression::SetKind(h) => reduce_set_kind_root(env, h)?,
        Expression::PropTerm(h) => reduce_prop_term_root(env, h)?,
        Expression::PropType(h) => reduce_prop_type_root(env, h)?,
        Expression::PropKind(h) => reduce_prop_kind_root(env, h)?,
        Expression::ValueTerm(_) => None,
        Expression::ValueType(h) => reduce_value_type_root(env, h)?,
        Expression::ValueKind(h) => reduce_value_kind_root(env, h)?,
        Expression::ComputationTerm(h) => reduce_computation_term_root(env, h)?,
        Expression::ComputationType(h) => reduce_computation_type_root(env, h)?,
        Expression::ComputationKind(h) => reduce_computation_kind_root(env, h)?,
    };
    if let Some(result) = root
        && (result.family() != e.family() || env.arena.sort(result) != env.arena.sort(e))
    {
        return Err("reduction changed syntax family or level".into());
    }
    Ok(root)
}
fn reduce_set_term_root(env: &Environment, h: SetTerm) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    let e = h.into();
    Ok(match node.form {
        SetTermForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        SetTermForm::AppTerm {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        SetTermForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        SetTermForm::SubsetIntro { element, .. } => Some(element.into()),
        SetTermForm::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => reduce_set_run(
            env,
            level,
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        )?,
        SetTermForm::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => reduce_set_run_case(
            env,
            level,
            SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            },
        )?,
        SetTermForm::Recursor {
            rule,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => reduce_recursor(env, rule, on_continue.into(), on_finish.into(), scrutinee)?,
        SetTermForm::BoxProgram {
            program_ty,
            program,
            certified_reflection,
        } => reduce_box_program(env, level, program_ty, program, certified_reflection)?,
        SetTermForm::ForceBox { program_ty, boxed } => reduce_force_box(env, program_ty, boxed)?,
        SetTermForm::BoxApp {
            rule,
            codomain,
            function,
            argument,
            ..
        } => reduce_box_application(env, rule, codomain, function, argument.into(), false)?,
        SetTermForm::BoxTypeApp {
            rule,
            codomain,
            function,
            argument,
            ..
        } => reduce_box_application(env, rule, codomain, function, argument.into(), true)?,
        SetTermForm::IndElim {
            inductive,
            scrutinee,
            cases,
            ..
        } => reduce_inductive(env, e, inductive, scrutinee.into(), &cases)?,
        SetTermForm::SetCase {
            scrutinee,
            branches,
            ..
        } => reduce_set_case(env, scrutinee, &branches)?,
        _ => None,
    })
}
fn reduce_set_type_root(env: &Environment, h: SetType) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    let e = h.into();
    Ok(match node.form {
        SetTypeForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        SetTypeForm::AppTerm {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        SetTypeForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        SetTypeForm::Recursor {
            rule,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => reduce_recursor(env, rule, on_continue.into(), on_finish.into(), scrutinee)?,
        SetTypeForm::IndElim {
            inductive,
            scrutinee,
            cases,
            ..
        } => reduce_inductive(env, e, inductive, scrutinee.into(), &cases)?,
        _ => None,
    })
}
fn reduce_set_kind_root(env: &Environment, h: SetKind) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    Ok(match node.form {
        SetKindForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        _ => None,
    })
}
fn reduce_prop_term_root(env: &Environment, h: PropTerm) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    let e = h.into();
    Ok(match node.form {
        PropTermForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        PropTermForm::AppTerm {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        PropTermForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        PropTermForm::Recursor {
            rule,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => reduce_recursor(env, rule, on_continue.into(), on_finish.into(), scrutinee)?,
        PropTermForm::IndElim {
            inductive,
            scrutinee,
            cases,
            ..
        } => reduce_inductive(env, e, inductive, scrutinee.into(), &cases)?,
        _ => None,
    })
}
fn reduce_prop_type_root(env: &Environment, h: PropType) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    let e = h.into();
    Ok(match node.form {
        PropTypeForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        PropTypeForm::AppTerm {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        PropTypeForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        PropTypeForm::Pred {
            subset, element, ..
        } => reduce_pred(env, subset, element)?,
        PropTypeForm::Recursor {
            rule,
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => reduce_recursor(env, rule, on_continue.into(), on_finish.into(), scrutinee)?,
        PropTypeForm::IndElim {
            inductive,
            scrutinee,
            cases,
            ..
        } => reduce_inductive(env, e, inductive, scrutinee.into(), &cases)?,
        _ => None,
    })
}
fn reduce_prop_kind_root(env: &Environment, h: PropKind) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    Ok(match node.form {
        PropKindForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        _ => None,
    })
}
fn reduce_value_type_root(env: &Environment, h: ValueType) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    Ok(match node.form {
        ValueTypeForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        ValueTypeForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        _ => None,
    })
}
fn reduce_value_kind_root(_env: &Environment, _h: ValueKind) -> Result<Option<Expression>, String> {
    Ok(None)
}
fn reduce_computation_term_root(
    env: &Environment,
    h: ComputationTerm,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    let level = node.level;
    Ok(match node.form {
        ComputationTermForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        ComputationTermForm::Force { value } => reduce_force(env, value)?,
        ComputationTermForm::AppTerm {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        ComputationTermForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        ComputationTermForm::Sequence {
            computation, body, ..
        } => reduce_sequence(env, computation, body)?,
        ComputationTermForm::ValueLet { value, body, .. } => Some(substitute(a, body, value)?),
        ComputationTermForm::Case {
            scrutinee,
            branches,
            ..
        } => reduce_case(env, scrutinee, &branches)?,
        ComputationTermForm::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => reduce_run(env, level, state_ty, result_ty, step, initial)?,
        ComputationTermForm::RunCase {
            state_ty,
            result_ty,
            step,
            transition,
            ..
        } => reduce_run_case(env, level, state_ty, result_ty, step, transition)?,
        _ => None,
    })
}
fn reduce_computation_type_root(
    env: &Environment,
    h: ComputationType,
) -> Result<Option<Expression>, String> {
    let a = &env.arena;
    let node = a.get(h);
    Ok(match node.form {
        ComputationTypeForm::Constant { definition } => env.definition(definition).map(|d| d.body),
        ComputationTypeForm::AppType {
            rule,
            function,
            argument,
        } => reduce_application(env, rule, function.into(), argument.into())?,
        _ => None,
    })
}
fn reduce_computation_kind_root(
    _env: &Environment,
    _h: ComputationKind,
) -> Result<Option<Expression>, String> {
    Ok(None)
}
