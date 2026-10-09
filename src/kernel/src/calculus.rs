//! Binder-aware operations on the shared expression DAG.
use crate::ids::SymbolId;
use crate::sharing::{Cache, ContextId, ContextInterner};
use crate::syntax::{Arena, Expression, Node};
use rustc_hash::{FxHashMap, FxHashSet};

/// Syntax-only substitutions shared by judgements in one environment. Argument
/// telescopes are interned so keys do not repeatedly own the same argument list.
#[derive(Debug, Default)]
pub(crate) struct Instantiations {
    arguments: ContextInterner<Expression>,
    results: SubstitutionResults,
}

type SubstitutionResults = Cache<(Expression, ContextId, usize), Expression>;

impl Instantiations {
    pub fn apply(
        &mut self,
        arena: &Arena,
        term: Expression,
        arguments: &[Expression],
    ) -> Result<Expression, crate::error::Error> {
        if arguments.is_empty() || arena.max_loose_bound(term).is_none() {
            return Ok(term);
        }
        let id = self.arguments.intern(arguments.iter().copied());
        substitute(arena, term, arguments, 0, id, &mut self.results)
    }

    pub fn len(&self) -> usize {
        self.results.len()
    }

    pub fn begin_scratch(&mut self) -> usize {
        self.results.begin_scratch();
        self.arguments.len()
    }

    pub fn finish_scratch(&mut self, arena: &Arena, mark: usize) {
        self.arguments.truncate(mark);
        self.results.finish_scratch(|(term, arguments, _), result| {
            arguments.within(mark) && arena.is_live(*term) && arena.is_live(*result)
        });
    }
}

pub fn shift(
    arena: &Arena,
    e: Expression,
    amount: usize,
    cutoff: usize,
) -> Result<Expression, crate::error::Error> {
    fn walk(
        arena: &Arena,
        e: Expression,
        amount: usize,
        cutoff: usize,
        cache: &mut FxHashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, crate::error::Error> {
        if arena.max_loose_bound(e).is_none_or(|i| i < cutoff) {
            return Ok(e);
        }
        if let Some(&e) = cache.get(&(e, cutoff)) {
            return Ok(e);
        }
        let result = match *arena.read(e) {
            Node::Bound(index) if index >= cutoff => arena.bound(
                index
                    .checked_add(amount)
                    .ok_or(crate::error::Error::BoundIndexOverflow)?,
            ),
            _ => arena.map_children(e, |child, depth| {
                walk(
                    arena,
                    child,
                    amount,
                    cutoff
                        .checked_add(depth)
                        .ok_or(crate::error::Error::BinderDepthOverflow)?,
                    cache,
                )
            })?,
        };
        cache.insert((e, cutoff), result);
        Ok(result)
    }
    if amount == 0 {
        return Ok(e);
    }
    walk(arena, e, amount, cutoff, &mut FxHashMap::default())
}

/// Simultaneous telescope substitution; arguments are ordered outermost first.
pub fn instantiate(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
) -> Result<Expression, crate::error::Error> {
    instantiate_at(arena, e, arguments, 0)
}
pub fn instantiate_at(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
    inner: usize,
) -> Result<Expression, crate::error::Error> {
    substitute(
        arena,
        e,
        arguments,
        inner,
        ContextId::default(),
        &mut Cache::default(),
    )
}

fn substitute(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
    inner: usize,
    id: ContextId,
    cache: &mut SubstitutionResults,
) -> Result<Expression, crate::error::Error> {
    fn walk(
        arena: &Arena,
        e: Expression,
        arguments: &[Expression],
        depth: usize,
        id: ContextId,
        cache: &mut SubstitutionResults,
    ) -> Result<Expression, crate::error::Error> {
        if arena.max_loose_bound(e).is_none_or(|i| i < depth) {
            return Ok(e);
        }
        if let Some(&e) = cache.get(&(e, id, depth)) {
            return Ok(e);
        }
        let result = match *arena.read(e) {
            Node::Bound(index) if index >= depth => {
                let index = index - depth;
                if index < arguments.len() {
                    shift(arena, arguments[arguments.len() - index - 1], depth, 0)?
                } else {
                    arena.bound(index - arguments.len() + depth)
                }
            }
            _ => arena.map_children(e, |child, bound| {
                walk(
                    arena,
                    child,
                    arguments,
                    depth
                        .checked_add(bound)
                        .ok_or(crate::error::Error::BinderDepthOverflow)?,
                    id,
                    cache,
                )
            })?,
        };
        cache.insert((e, id, depth), result);
        Ok(result)
    }
    if arguments.is_empty() {
        return Ok(e);
    }
    // Replacing a telescope by its own variables leaves terms in that
    // telescope unchanged. Outer free variables would still need lowering.
    if arena
        .max_loose_bound(e)
        .is_none_or(|i| i < inner || i - inner < arguments.len())
        && arguments
            .iter()
            .rev()
            .enumerate()
            .all(|(index, &argument)| matches!(*arena.read(argument), Node::Bound(i) if i == index))
    {
        return Ok(e);
    }
    walk(arena, e, arguments, inner, id, cache)
}

/// Abstract an occurrence's distinct variable arguments into its declaration telescope.
pub fn abstract_pattern(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
) -> Result<Option<Expression>, crate::error::Error> {
    let mut variables = FxHashMap::default();
    for (position, &argument) in arguments.iter().enumerate() {
        let Node::Bound(index) = *arena.read(argument) else {
            return Ok(None);
        };
        if variables
            .insert(index, arguments.len() - position - 1)
            .is_some()
        {
            return Ok(None);
        }
    }
    fn walk(
        arena: &Arena,
        e: Expression,
        variables: &FxHashMap<usize, usize>,
        depth: usize,
        cache: &mut FxHashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, crate::error::Error> {
        if let Some(&e) = cache.get(&(e, depth)) {
            return Ok(e);
        }
        let result = match *arena.read(e) {
            Node::Bound(index) if index >= depth => {
                let target = variables
                    .get(&(index - depth))
                    .ok_or(crate::error::Error::EscapingVariable)?;
                arena.bound(
                    target
                        .checked_add(depth)
                        .ok_or(crate::error::Error::BoundIndexOverflow)?,
                )
            }
            _ => arena.map_children(e, |child, bound| {
                walk(
                    arena,
                    child,
                    variables,
                    depth
                        .checked_add(bound)
                        .ok_or(crate::error::Error::BinderDepthOverflow)?,
                    cache,
                )
            })?,
        };
        cache.insert((e, depth), result);
        Ok(result)
    }
    walk(arena, e, &variables, 0, &mut FxHashMap::default()).map(Some)
}

pub fn max_loose_bound(arena: &Arena, e: Expression) -> Option<usize> {
    arena.max_loose_bound(e)
}

/// Erase operand handles and binder labels, retaining every rigid discriminator.
pub fn skeleton(arena: &Arena, expression: Expression) -> Node {
    let dummy = arena.bound(0);
    let mut node = arena
        .map_node_children(arena.get(expression), |_, _| {
            Ok::<_, std::convert::Infallible>(dummy)
        })
        .unwrap();
    match &mut node {
        Node::Product { var, .. }
        | Node::Lambda { var, .. }
        | Node::Subset { var, .. }
        | Node::IdElim { var, .. }
        | Node::Sequence { var, .. }
        | Node::ValueLet { var, .. } => *var = SymbolId::ANONYMOUS,
        Node::IndElim {
            motive_bindings, ..
        } => {
            for (var, _) in motive_bindings {
                *var = SymbolId::ANONYMOUS;
            }
        }
        Node::SetCase { binders, .. } | Node::ProgramCase { binders, .. } => {
            for vars in binders {
                vars.fill(SymbolId::ANONYMOUS);
            }
        }
        _ => {}
    }
    node
}

pub fn alpha_equal(arena: &Arena, left: Expression, right: Expression) -> bool {
    fn compare(
        arena: &Arena,
        left: Expression,
        right: Expression,
        seen: &mut FxHashSet<(Expression, Expression)>,
    ) -> bool {
        if left == right || !seen.insert((left, right)) {
            return true;
        }
        if skeleton(arena, left) != skeleton(arena, right) {
            return false;
        }
        let left = comparison_children(arena, left);
        let right = comparison_children(arena, right);
        left.len() == right.len()
            && left
                .into_iter()
                .zip(right)
                .all(|((l, ld), (r, rd))| ld == rd && compare(arena, l, r, seen))
    }
    compare(arena, left, right, &mut FxHashSet::default())
}

/// Choice and run certificates are checked but erased by definitional equality.
pub fn comparison_children(arena: &Arena, e: Expression) -> Vec<(Expression, usize)> {
    let mut children = arena.children(e);
    match arena.get(e) {
        Node::Choice { .. } => children.truncate(1),
        Node::ChoiceEq { .. } => children.truncate(2),
        Node::SetRun { .. } | Node::Run { .. } => children.truncate(4),
        Node::SetRunCase { .. } | Node::RunCase { .. } => children.truncate(5),
        _ => {}
    }
    children
}

/// Map free indices while preserving all nested binders.
pub fn reindex(
    arena: &Arena,
    e: Expression,
    mut map: impl FnMut(usize) -> Result<usize, crate::error::Error>,
) -> Result<Expression, crate::error::Error> {
    fn walk(
        arena: &Arena,
        e: Expression,
        depth: usize,
        map: &mut impl FnMut(usize) -> Result<usize, crate::error::Error>,
    ) -> Result<Expression, crate::error::Error> {
        if arena.max_loose_bound(e).is_none_or(|i| i < depth) {
            return Ok(e);
        }
        if let Node::Bound(i) = arena.get(e) {
            if i >= depth {
                return Ok(arena.bound(
                    map(i - depth)?
                        .checked_add(depth)
                        .ok_or(crate::error::Error::IndexOverflow)?,
                ));
            }
            return Ok(e);
        }
        arena.map_children(e, |e, n| walk(arena, e, depth + n, map))
    }
    walk(arena, e, 0, &mut map)
}
pub fn strengthen(
    arena: &Arena,
    e: Expression,
    target: usize,
) -> Result<Expression, crate::error::Error> {
    reindex(arena, e, |i| {
        if i == target {
            Err(crate::error::Error::ExpressionDependsOnRemovedBinder)
        } else {
            Ok(if i > target { i - 1 } else { i })
        }
    })
}
