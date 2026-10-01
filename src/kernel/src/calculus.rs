//! Binder-aware operations on the shared expression DAG.
use crate::ids::SymbolId;
use crate::syntax::{Arena, Expression, Node};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn shift(
    arena: &Arena,
    e: Expression,
    amount: usize,
    cutoff: usize,
) -> Result<Expression, String> {
    fn walk(
        arena: &Arena,
        e: Expression,
        amount: usize,
        cutoff: usize,
        cache: &mut FxHashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, String> {
        if arena.max_loose_bound(e).is_none_or(|i| i < cutoff) {
            return Ok(e);
        }
        if let Some(&e) = cache.get(&(e, cutoff)) {
            return Ok(e);
        }
        let result = match *arena.read(e) {
            Node::Bound(index) if index >= cutoff => {
                arena.bound(index.checked_add(amount).ok_or("bound index overflow")?)
            }
            _ => arena.map_children(e, |child, depth| {
                walk(
                    arena,
                    child,
                    amount,
                    cutoff.checked_add(depth).ok_or("binder depth overflow")?,
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
) -> Result<Expression, String> {
    instantiate_at(arena, e, arguments, 0)
}
pub fn instantiate_at(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
    inner: usize,
) -> Result<Expression, String> {
    fn walk(
        arena: &Arena,
        e: Expression,
        arguments: &[Expression],
        depth: usize,
        cache: &mut FxHashMap<(Expression, usize), Expression>,
    ) -> Result<Expression, String> {
        if arena.max_loose_bound(e).is_none_or(|i| i < depth) {
            return Ok(e);
        }
        if let Some(&e) = cache.get(&(e, depth)) {
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
                    depth.checked_add(bound).ok_or("binder depth overflow")?,
                    cache,
                )
            })?,
        };
        cache.insert((e, depth), result);
        Ok(result)
    }
    if arguments.is_empty() {
        return Ok(e);
    }
    walk(arena, e, arguments, inner, &mut FxHashMap::default())
}

/// Abstract an occurrence's distinct variable arguments into its declaration telescope.
pub fn abstract_pattern(
    arena: &Arena,
    e: Expression,
    arguments: &[Expression],
) -> Result<Option<Expression>, String> {
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
    ) -> Result<Expression, String> {
        if let Some(&e) = cache.get(&(e, depth)) {
            return Ok(e);
        }
        let result = match *arena.read(e) {
            Node::Bound(index) if index >= depth => {
                let target = variables
                    .get(&(index - depth))
                    .ok_or("metavariable solution captures a variable outside its context")?;
                arena.bound(target.checked_add(depth).ok_or("bound index overflow")?)
            }
            _ => arena.map_children(e, |child, bound| {
                walk(
                    arena,
                    child,
                    variables,
                    depth.checked_add(bound).ok_or("binder depth overflow")?,
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
    mut map: impl FnMut(usize) -> Result<usize, String>,
) -> Result<Expression, String> {
    fn walk(
        arena: &Arena,
        e: Expression,
        depth: usize,
        map: &mut impl FnMut(usize) -> Result<usize, String>,
    ) -> Result<Expression, String> {
        if arena.max_loose_bound(e).is_none_or(|i| i < depth) {
            return Ok(e);
        }
        if let Node::Bound(i) = arena.get(e) {
            if i >= depth {
                return Ok(arena.bound(map(i - depth)?.checked_add(depth).ok_or("index overflow")?));
            }
            return Ok(e);
        }
        arena.map_children(e, |e, n| walk(arena, e, depth + n, map))
    }
    walk(arena, e, 0, &mut map)
}
pub fn strengthen(arena: &Arena, e: Expression, target: usize) -> Result<Expression, String> {
    reindex(arena, e, |i| {
        if i == target {
            Err("expression depends on removed binder".into())
        } else {
            Ok(if i > target { i - 1 } else { i })
        }
    })
}
