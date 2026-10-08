//! Resolve frontend names and delegate semantic judgements to the kernel.
use crate::{
    lowering::Lowerer,
    raw::{
        environment::{CrateEnv, DefinedConstant, ModuleParameterKind},
        exp::{Exp, ExpContext, ExpNode},
        program::{ComputationTermNode, ValueTermNode, ValueTypeNode},
        traversal::Term,
    },
};
use rustc_hash::FxHashSet;

/// Materialize source templates before borrowing the kernel environment.
/// Registered declarations are immutable and their dependencies are already
/// materialized. Each reference's actual arguments are still visited below.
fn prepare(env: &CrateEnv, mut pending: Vec<Term>) -> Result<(), String> {
    let mut seen = FxHashSet::default();
    let mut definitions = FxHashSet::default();
    let mut inductives = FxHashSet::default();
    let mut datatypes = FxHashSet::default();
    let mut parameters = FxHashSet::default();
    while let Some(term) = pending.pop() {
        if let Term::Logical(e) = term
            && env.arena().lowered_definitions.borrow().contains(&e.0)
        {
            continue;
        }
        if !seen.insert(term) {
            continue;
        }
        term.visit_children(env.arena(), |child, _| pending.push(child));
        let (definition, inductive, datatype, parameter) = match term {
            Term::Logical(e)
                if matches!(
                    env.arena().core.get(e.0),
                    kernel::syntax::Node::Definition { .. }
                ) =>
            {
                (None, None, None, None)
            }
            Term::Logical(e) => match env.arena().get(e) {
                ExpNode::DefinedConstant(id)
                | ExpNode::DefinitionInstance { definition: id, .. } => {
                    (Some(id), None, None, None)
                }
                ExpNode::IndType { indspec, .. }
                | ExpNode::IndCtor { indspec, .. }
                | ExpNode::IndElim { indspec, .. }
                | ExpNode::IndCase { indspec, .. } => (None, Some(indspec), None, None),
                ExpNode::ReflectedProgramCase { indspec, .. } => (None, None, Some(indspec), None),
                ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => {
                    (None, None, None, Some(id))
                }
                _ => (None, None, None, None),
            },
            Term::ValueType(e) => match env.arena().get(e) {
                ValueTypeNode::Inductive { indspec, .. } => (None, None, Some(indspec), None),
                ValueTypeNode::ModuleParam(id) => (None, None, None, Some(id)),
                _ => (None, None, None, None),
            },
            Term::Value(e) => match env.arena().get(e) {
                ValueTermNode::DefinedConstant(id)
                | ValueTermNode::DefinitionInstance { definition: id, .. } => {
                    (Some(id), None, None, None)
                }
                ValueTermNode::InductiveConstructor { indspec, .. } => {
                    (None, None, Some(indspec), None)
                }
                ValueTermNode::ModuleParam(id) => (None, None, None, Some(id)),
                _ => (None, None, None, None),
            },
            Term::Computation(e) => match env.arena().get(e) {
                ComputationTermNode::DefinedConstant(id)
                | ComputationTermNode::DefinitionInstance { definition: id, .. } => {
                    (Some(id), None, None, None)
                }
                ComputationTermNode::Case { indspec, .. } => (None, None, Some(indspec), None),
                _ => (None, None, None, None),
            },
            Term::ComputationType(_) => (None, None, None, None),
        };
        if let Some(id) = parameter
            && parameters.insert(id)
            && env.kernel.borrow().parameter(id.into()).is_none()
        {
            match env
                .module_parameter_opt(id)
                .map(|p| p.kind)
                .unwrap_or(ModuleParameterKind::ProgramType)
            {
                ModuleParameterKind::Pts { ty } => pending.push(Term::Logical(ty)),
                ModuleParameterKind::ProgramValue { ty } => pending.push(Term::ValueType(ty)),
                ModuleParameterKind::ProgramType => {}
            }
        }
        if let Some(id) = definition
            && definitions.insert(id)
            && !env.kernel_definitions.borrow().contains_key(&id)
        {
            match env.resolve_definition(id)?.clone() {
                DefinedConstant::Contextual {
                    parameters,
                    ty,
                    body,
                } => {
                    pending.extend(parameters.into_iter().map(|(_, e)| Term::Logical(e)));
                    pending.extend([Term::Logical(ty), Term::Logical(body)]);
                }
                DefinedConstant::Pts { ty, body } => {
                    pending.extend([Term::Logical(ty), Term::Logical(body)])
                }
                DefinedConstant::ProgramValue { ty, body } => {
                    pending.extend([Term::ValueType(ty), Term::Value(body)])
                }
                DefinedConstant::ProgramComputation { ty, body } => {
                    pending.extend([Term::ComputationType(ty), Term::Computation(body)])
                }
            }
        }
        if let Some(id) = inductive
            && inductives.insert(id)
            && env.kernel.borrow().inductive(id.into()).is_none()
        {
            if !env.is_program_mirror(id) {
                let arguments = if let Some(origin) = env.inductive_specialization(id) {
                    pending.push(Term::Logical(env.arena().alloc(ExpNode::IndType {
                        indspec: origin.source,
                        parameters: vec![],
                    })));
                    origin.arguments.clone()
                } else {
                    env.namespace_arguments(id.module)
                };
                pending.extend(arguments.into_iter().map(|(_, argument)| match argument {
                    crate::raw::environment::ModuleArgument::Pts(e) => Term::Logical(e),
                    crate::raw::environment::ModuleArgument::ProgramType(t) => Term::ValueType(t),
                    crate::raw::environment::ModuleArgument::ProgramValue(v) => Term::Value(v),
                }));
            }
            let spec = env.inductive(id);
            pending.extend(spec.parameters().iter().map(|(_, e)| Term::Logical(*e)));
            pending.push(Term::Logical(spec.arity(env.arena())));
            let this = env.arena().alloc(ExpNode::IndType {
                indspec: id,
                parameters: (0..spec.parameters().len())
                    .rev()
                    .map(|i| env.arena().exp_bound(i))
                    .collect(),
            });
            pending.extend(
                spec.constructors()
                    .iter()
                    .map(|c| Term::Logical(c.as_exp_with_type(env.arena(), this))),
            );
        }
        if let Some(id) = datatype
            && env.has_program_inductive(id)
            && datatypes.insert(id)
            && env.kernel.borrow().datatype(id.into()).is_none()
        {
            let spec = env.program_inductive(id);
            pending.extend(
                spec.constructors()
                    .iter()
                    .flat_map(|c| c.fields().iter().map(|(_, e)| Term::ValueType(*e))),
            );
            pending.push(Term::Logical(env.arena().alloc(ExpNode::IndType {
                indspec: spec.reflected(),
                parameters: vec![],
            })));
        }
    }
    Ok(())
}

pub(crate) fn logical<T>(
    env: &CrateEnv,
    context: &ExpContext,
    roots: &[Exp],
    f: impl FnOnce(
        &kernel::environment::Environment,
        kernel::syntax::Context,
        Vec<kernel::syntax::Expression>,
    ) -> Result<T, kernel::metavariables::Error>,
) -> Result<T, String> {
    logical_in_scope(env, context, 0, roots, f)
}
pub(crate) fn logical_in_scope<T>(
    env: &CrateEnv,
    context: &ExpContext,
    base: usize,
    roots: &[Exp],
    f: impl FnOnce(
        &kernel::environment::Environment,
        kernel::syntax::Context,
        Vec<kernel::syntax::Expression>,
    ) -> Result<T, kernel::metavariables::Error>,
) -> Result<T, String> {
    let profile = std::env::var_os("REF_TYPE_PROFILE_BRIDGE").is_some();
    if profile {
        eprintln!(
            "bridge prepare roots={roots:?} context={} base={base}",
            context.len()
        );
    }
    let mut pending = roots.iter().copied().map(Term::Logical).collect::<Vec<_>>();
    pending.extend(context.iter().map(|b| Term::Logical(b.ty)));
    prepare(env, pending)?;
    if profile {
        eprintln!("bridge lower roots={roots:?}");
    }
    let mut kernel = env.kernel.borrow_mut();
    let mut lower = Lowerer::new(env, &mut kernel);
    lower.nominal(base);
    let mut local = context.clone();
    let module = env.root_module();
    let terms = roots
        .iter()
        .map(|&e| lower.set(e, &mut local, module))
        .collect::<Result<Vec<_>, _>>()?;
    let context = lower.nominal_context(context, base, module)?;
    if profile {
        eprintln!("bridge kernel roots={terms:?}");
    }
    let result = f(&kernel, context, terms)
        .map_err(|error| crate::lowering::format_kernel_error(env, &error));
    if profile {
        eprintln!("bridge finished roots={roots:?}");
    }
    result
}

pub(crate) fn program<T>(
    env: &CrateEnv,
    context: &crate::raw::program::ProgramContext,
    roots: &[Term],
    f: impl FnOnce(
        &kernel::environment::Environment,
        kernel::syntax::Context,
        Vec<kernel::syntax::Expression>,
    ) -> Result<T, kernel::metavariables::Error>,
) -> Result<T, String> {
    use crate::raw::program::ProgramContextEntry;
    let mut pending = roots.to_vec();
    pending.extend(context.iter().filter_map(|b| match b {
        ProgramContextEntry::ValueTerm { ty, .. } => Some(Term::ValueType(*ty)),
        _ => None,
    }));
    prepare(env, pending)?;
    let mut kernel = env.kernel.borrow_mut();
    let mut lower = Lowerer::new(env, &mut kernel);
    lower.nominal(0);
    let mut local = context.clone();
    let terms = roots
        .iter()
        .map(|&term| lower.source_term(term, &mut local))
        .collect::<Result<Vec<_>, _>>()?;
    let context = lower.program_context(context)?;
    f(&kernel, context, terms).map_err(|e| crate::lowering::format_kernel_error(env, &e))
}

/// Resolve a term for structural operations, which accept open expressions.
pub(crate) fn expression<T>(
    env: &CrateEnv,
    term: Term,
    f: impl FnOnce(&kernel::environment::Environment, kernel::syntax::Expression) -> Result<T, String>,
) -> Result<T, String> {
    prepare(env, vec![term])?;
    let mut depth = env
        .arena()
        .max_loose_bound(term)
        .map_or(0, |i| i.saturating_add(1));
    let mut pending = vec![term];
    let mut seen = FxHashSet::default();
    while let Some(t) = pending.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let Term::Logical(e) = t
            && let ExpNode::DefinedConstant(id) = env.arena().get(e)
        {
            depth = depth.max(env.definition_context(id.module).len());
        }
        t.visit_children(env.arena(), |child, _| pending.push(child));
    }
    if depth > 100_000 {
        return Err("bound variable outside supported context".into());
    }
    let mut kernel = env.kernel.borrow_mut();
    let mut lower = Lowerer::new(env, &mut kernel);
    lower.nominal(0);
    lower.structural = true;
    let e = match term {
        Term::Logical(e) => {
            let mut context = (0..depth)
                .map(|_| crate::raw::exp::ExpContextEntry {
                    var: crate::raw::ids::SymbolId::ANONYMOUS,
                    ty: env.arena().sort(crate::raw::sort::Sort::Set(0)),
                })
                .collect();
            lower.set(e, &mut context, env.root_module())?
        }
        term => lower.source_term(term, &mut vec![])?,
    };
    f(&kernel, e)
}

pub(crate) fn captured_definition(
    env: &CrateEnv,
    definition: crate::raw::ids::DefId,
    substitutions: &[(crate::raw::ids::ModuleParamId, Exp)],
    parameters: &[Exp],
) -> Result<Exp, String> {
    let actual = substitutions
        .iter()
        .map(|(id, value)| expression(env, Term::Logical(*value), |_, term| Ok((*id, term))))
        .collect::<Result<Vec<_>, _>>()?;
    let reference = if matches!(
        env.definition(definition),
        DefinedConstant::Contextual { .. }
    ) {
        env.arena().alloc(ExpNode::DefinitionInstance {
            definition,
            arguments: parameters.to_vec(),
        })
    } else {
        env.arena().alloc(ExpNode::DefinedConstant(definition))
    };
    expression(env, Term::Logical(reference), |kernel, reference| {
        let kernel::syntax::Node::Definition { id, mut arguments } = kernel.arena().get(reference)
        else {
            return Err("expected a definition reference".into());
        };
        let captures = env
            .arena()
            .definition_captures(id)
            .ok_or("missing definition captures")?;
        for (parameter, argument) in captures.iter().zip(&mut arguments) {
            if let Some((_, value)) = actual.iter().find(|(id, _)| id == parameter) {
                *argument = *value;
            }
        }
        kernel.reference(id, arguments).map(Exp)
    })
}

mod terms;
pub(crate) use terms::*;

/// Specialize a logical expression after its dependencies have explicit captures.
pub(crate) fn captured_expression(
    env: &CrateEnv,
    value: Exp,
    substitutions: &[(crate::raw::ids::ModuleParamId, Exp)],
) -> Result<Exp, String> {
    let value = expression(env, Term::Logical(value), |_, value| Ok(Exp(value)))?;
    Ok(crate::raw::remapping::exp_subst_map(
        env.arena(),
        value,
        substitutions,
    ))
}
