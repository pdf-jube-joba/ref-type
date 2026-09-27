//! Contextual metavariables and transactional unification on shared PTS terms.
use crate::{calculus::*, environment::Environment, syntax::*};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, Clone)]
pub enum Error {
    InvalidMeta(MetaId),
    TypeMismatch(Box<TypeMismatch>),
    Unresolved {
        metas: Vec<MetaId>,
        constraints: usize,
    },
    Contradiction(String),
}
impl From<String> for Error {
    fn from(s: String) -> Self {
        Self::Contradiction(s)
    }
}
impl From<&str> for Error {
    fn from(s: &str) -> Self {
        Self::Contradiction(s.into())
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeMismatch(_) => f.write_str("types are not convertible"),
            Self::InvalidMeta(id) => write!(f, "invalid metavariable {id:?}"),
            Self::Unresolved { metas, constraints } => write!(
                f,
                "unresolved metavariables {metas:?}; {constraints} pending constraints"
            ),
            Self::Contradiction(s) => f.write_str(s),
        }
    }
}
impl std::error::Error for Error {}
impl Error {
    pub(crate) fn at(mut self, phase: impl Into<String>) -> Self {
        let phase = phase.into();
        match &mut self {
            Self::TypeMismatch(error) => error.frames.push(phase),
            Self::Contradiction(message) => *message = format!("{message}\n{phase}"),
            _ => {}
        }
        self
    }
}
#[derive(Debug, Clone)]
pub struct TypeMismatch {
    pub arena: Arena,
    pub context: Context,
    pub term: Expression,
    pub inferred: Expression,
    pub expected: Expression,
    pub frames: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OriginId(pub u64);

#[derive(Debug, Clone)]
pub struct Entry {
    pub origin: Option<OriginId>,
    pub context: Context,
    pub expected: Option<Expression>,
    pub assignment: Option<Expression>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
    Equal {
        context: Context,
        left: Expression,
        right: Expression,
    },
    HasType {
        context: Context,
        term: Expression,
        expected: Expression,
    },
    IsSort {
        context: Context,
        term: Expression,
    },
    Validate {
        context: Context,
        term: Expression,
        expected: Option<Expression>,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Solved,
    Blocked,
}
#[derive(Debug, Clone)]
pub struct Snapshot {
    session: u64,
    revision: u64,
    history_len: usize,
    entries: Vec<Option<Entry>>,
    constraints: Vec<Constraint>,
}
#[derive(Debug)]
pub struct MetaContext {
    session: u64,
    history: Vec<Constraint>,
    recorded: FxHashSet<Constraint>,
    entries: Vec<Option<Entry>>,
    constraints: Vec<Constraint>,
    revision: u64,
    zonked: std::cell::RefCell<FxHashMap<Expression, Expression>>,
    pub(crate) inferred: FxHashMap<(crate::sharing::ContextId, Expression), Expression>,
}
impl Default for MetaContext {
    fn default() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self {
            session: NEXT.fetch_add(1, Ordering::Relaxed),
            entries: Vec::new(),
            history: Vec::new(),
            recorded: FxHashSet::default(),
            constraints: Vec::new(),
            revision: 0,
            zonked: Default::default(),
            inferred: Default::default(),
        }
    }
}
impl MetaContext {
    pub fn new() -> Self {
        Self::default()
    }
    fn changed(&mut self) {
        self.revision += 1;
        self.zonked.get_mut().clear();
        self.inferred.clear();
    }
    pub fn history(&self) -> &[Constraint] {
        &self.history
    }
    fn record(&mut self, constraint: Constraint) {
        if self.recorded.insert(constraint.clone()) {
            self.history.push(constraint);
        }
    }
    pub(crate) fn roots(&self) -> Vec<Expression> {
        let mut roots = vec![];
        for entry in self.entries.iter().flatten() {
            roots.extend(entry.context.iter().map(|b| b.ty));
            roots.extend(entry.expected);
            roots.extend(entry.assignment);
        }
        for constraint in self.constraints.iter().chain(&self.history) {
            match constraint {
                Constraint::Equal {
                    context,
                    left,
                    right,
                } => {
                    roots.extend(context.iter().map(|b| b.ty));
                    roots.extend([*left, *right]);
                }
                Constraint::HasType {
                    context,
                    term,
                    expected,
                } => {
                    roots.extend(context.iter().map(|b| b.ty));
                    roots.extend([*term, *expected]);
                }
                Constraint::Validate {
                    context,
                    term,
                    expected,
                } => {
                    roots.extend(context.iter().map(|b| b.ty));
                    roots.push(*term);
                    roots.extend(*expected);
                }
                Constraint::IsSort { context, term } => {
                    roots.extend(context.iter().map(|b| b.ty));
                    roots.push(*term);
                }
            }
        }
        roots
    }
    pub(crate) fn retain_caches(&mut self, arena: &Arena) {
        self.zonked
            .get_mut()
            .retain(|key, value| arena.is_live(*key) && arena.is_live(*value));
        self.inferred
            .retain(|(_, key), value| arena.is_live(*key) && arena.is_live(*value));
    }
    pub fn entries(&self) -> impl Iterator<Item = (MetaId, &Entry)> {
        self.entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                entry.as_ref().map(|entry| {
                    (
                        MetaId {
                            session: self.session,
                            index: index as u32,
                        },
                        entry,
                    )
                })
            })
    }
    pub fn entry(&self, id: MetaId) -> Result<&Entry, Error> {
        if id.session != self.session {
            return Err(Error::InvalidMeta(id));
        }
        self.entries
            .get(id.index as usize)
            .and_then(Option::as_ref)
            .ok_or(Error::InvalidMeta(id))
    }
    pub fn fresh(
        &mut self,
        arena: &Arena,
        context: Context,
        expected: Option<Expression>,
    ) -> Expression {
        let id = MetaId {
            session: self.session,
            index: u32::try_from(self.entries.len()).expect("metavariable arena exhausted"),
        };
        let arguments = (0..context.len())
            .rev()
            .map(|index| arena.bound(index))
            .collect();
        self.entries.push(Some(Entry {
            origin: None,
            context,
            expected,
            assignment: None,
        }));
        arena.alloc(Node::Meta { id, arguments })
    }
    pub fn set_origin(&mut self, id: MetaId, origin: OriginId) -> Result<(), Error> {
        self.entry(id)?;
        self.entries[id.index as usize].as_mut().unwrap().origin = Some(origin);
        Ok(())
    }
    pub fn constraint_origins(
        &self,
        arena: &Arena,
        constraint: &Constraint,
    ) -> Result<Vec<OriginId>, Error> {
        let mut origins = self
            .dependencies(arena, constraint)?
            .into_iter()
            .filter_map(|(id, _, _)| self.entry(id).ok().and_then(|e| e.origin))
            .collect::<Vec<_>>();
        origins.sort_by_key(|id| id.0);
        origins.dedup();
        Ok(origins)
    }
    fn dependencies(
        &self,
        arena: &Arena,
        constraint: &Constraint,
    ) -> Result<Vec<(MetaId, Option<Expression>, Option<Expression>)>, Error> {
        let (context, mut pending) = match constraint {
            Constraint::Equal {
                context,
                left,
                right,
            } => (context, vec![*left, *right]),
            Constraint::HasType {
                context,
                term,
                expected,
            } => (context, vec![*term, *expected]),
            Constraint::Validate {
                context,
                term,
                expected,
            } => (context, std::iter::once(*term).chain(*expected).collect()),
            Constraint::IsSort { context, term } => (context, vec![*term]),
        };
        pending.extend(context.iter().map(|b| b.ty));
        let mut seen = FxHashSet::default();
        let mut ids = FxHashSet::default();
        let mut result = vec![];
        while let Some(e) = pending.pop() {
            if !arena.contains_meta(e) || !seen.insert(e) {
                continue;
            }
            if let Node::Meta { id, .. } = arena.get(e)
                && ids.insert(id) {
                    let entry = self.entry(id)?;
                    result.push((id, entry.expected, entry.assignment));
                    pending.extend(entry.expected);
                    pending.extend(entry.assignment);
                    pending.extend(entry.context.iter().map(|b| b.ty));
                }
            pending.extend(arena.children(e).into_iter().map(|(e, _)| e));
        }
        result.sort_by_key(|(id, _, _)| id.index);
        Ok(result)
    }
    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            session: self.session,
            revision: self.revision,
            history_len: self.history.len(),
            entries: self.entries.clone(),
            constraints: self.constraints.clone(),
        }
    }
    /// Restrict a contextual hole to the shared outer prefix of two scopes.
    pub fn restrict(
        &mut self,
        env: &Environment,
        id: MetaId,
        keep: usize,
    ) -> Result<Expression, Error> {
        let entry = self.entry(id)?.clone();
        if keep > entry.context.len() {
            return Err("invalid metavariable scope restriction".into());
        }
        let removed = entry.context.len() - keep;
        let arguments = (removed..entry.context.len())
            .rev()
            .map(|i| env.arena.bound(i))
            .collect::<Vec<_>>();
        let strengthen = |e| {
            abstract_pattern(&env.arena, e, &arguments)
                .map_err(|_| {
                    Error::from("metavariable captures a variable outside its shared context")
                })?
                .ok_or_else(|| {
                    Error::from("metavariable captures a variable outside its shared context")
                })
        };
        let expected = entry.expected.map(strengthen).transpose()?;
        let assignment = entry.assignment.map(strengthen).transpose()?;
        let fresh = self.fresh(&env.arena, entry.context[..keep].to_vec(), expected);
        let Node::Meta { id: next, .. } = env.arena.get(fresh) else {
            unreachable!()
        };
        let restricted = self.entries[next.index as usize].as_mut().unwrap();
        restricted.assignment = assignment;
        restricted.origin = entry.origin;
        self.entries[id.index as usize].as_mut().unwrap().assignment =
            Some(env.arena.alloc(Node::Meta {
                id: next,
                arguments,
            }));
        self.changed();
        Ok(fresh)
    }
    pub fn rollback(&mut self, snapshot: Snapshot) -> Result<(), Error> {
        if snapshot.session != self.session {
            return Err("snapshot belongs to a different metavariable session".into());
        }
        let len = self.entries.len().max(snapshot.entries.len());
        self.entries = snapshot.entries;
        self.entries.resize_with(len, || None);
        self.constraints = snapshot.constraints;
        self.revision = snapshot.revision;
        for constraint in self.history.drain(snapshot.history_len..) {
            self.recorded.remove(&constraint);
        }
        self.zonked.get_mut().clear();
        self.inferred.clear();
        Ok(())
    }
    pub fn constrain(&mut self, constraint: Constraint) {
        self.record(constraint.clone());
        if !self.constraints.contains(&constraint) {
            self.constraints.push(constraint);
        }
    }
    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    pub fn zonk(&self, arena: &Arena, e: Expression) -> Result<Expression, Error> {
        fn visit(
            metas: &MetaContext,
            arena: &Arena,
            e: Expression,
            cache: &mut FxHashMap<Expression, Expression>,
            active: &mut FxHashSet<MetaId>,
        ) -> Result<Expression, Error> {
            if !arena.contains_meta(e) {
                return Ok(e);
            }
            if let Some(&e) = cache.get(&e) {
                return Ok(e);
            }
            let mapped =
                arena.map_children(e, |child, _| visit(metas, arena, child, cache, active))?;
            let result = if let Node::Meta { id, arguments } = arena.get(mapped) {
                let entry = metas.entry(id)?;
                if arguments.len() != entry.context.len() {
                    return Err("metavariable argument count mismatch".into());
                }
                if let Some(value) = entry.assignment {
                    if !active.insert(id) {
                        return Err("cyclic metavariable assignment".into());
                    }
                    let value = instantiate(arena, value, &arguments)?;
                    let result = visit(metas, arena, value, cache, active)?;
                    active.remove(&id);
                    result
                } else {
                    mapped
                }
            } else {
                mapped
            };
            cache.insert(e, result);
            Ok(result)
        }
        visit(
            self,
            arena,
            e,
            &mut self.zonked.borrow_mut(),
            &mut FxHashSet::default(),
        )
    }

    pub fn unresolved(
        &self,
        arena: &Arena,
        roots: impl IntoIterator<Item = Expression>,
    ) -> Result<Vec<MetaId>, Error> {
        let mut pending = roots.into_iter().collect::<Vec<_>>();
        let mut nodes = FxHashSet::default();
        let mut metas = FxHashSet::default();
        while let Some(e) = pending.pop() {
            if !arena.contains_meta(e) {
                continue;
            }
            if !nodes.insert(e) {
                continue;
            }
            if let Node::Meta { id, .. } = arena.get(e) {
                let entry = self.entry(id)?;
                if metas.insert(id) {
                    if let Some(ty) = entry.expected {
                        pending.push(ty);
                    }
                    pending.extend(entry.context.iter().map(|b| b.ty));
                    if let Some(value) = entry.assignment {
                        pending.push(value);
                    }
                }
            }
            pending.extend(arena.children(e).into_iter().map(|(e, _)| e));
        }
        let mut ids = metas
            .into_iter()
            .filter(|&id| self.entry(id).is_ok_and(|e| e.assignment.is_none()))
            .collect::<Vec<_>>();
        ids.sort_by_key(|id| id.index);
        Ok(ids)
    }

    pub fn require_solved(
        &self,
        arena: &Arena,
        roots: impl IntoIterator<Item = Expression>,
    ) -> Result<(), Error> {
        let metas = self.unresolved(arena, roots)?;
        if metas.is_empty() {
            Ok(())
        } else {
            Err(Error::Unresolved {
                metas,
                constraints: 0,
            })
        }
    }

    fn occurs(&self, arena: &Arena, needle: MetaId, expression: Expression) -> Result<bool, Error> {
        let mut terms = vec![expression];
        let mut seen = FxHashSet::default();
        let mut entries = FxHashSet::default();
        while let Some(e) = terms.pop() {
            if !seen.insert(e) {
                continue;
            }
            if let Node::Meta { id, .. } = arena.get(e) {
                if id == needle {
                    return Ok(true);
                }
                if entries.insert(id) {
                    let entry = self.entry(id)?;
                    terms.extend(entry.assignment);
                    terms.extend(entry.expected);
                    terms.extend(entry.context.iter().map(|b| b.ty));
                }
            }
            terms.extend(arena.children(e).into_iter().map(|(child, _)| child));
        }
        Ok(false)
    }

    fn assign(
        &mut self,
        env: &Environment,
        id: MetaId,
        arguments: &[Expression],
        value: Expression,
    ) -> Result<Outcome, Error> {
        if self.occurs(&env.arena, id, value)? {
            return Err("occurs check failed".into());
        }
        let entry = self.entry(id)?;
        if entry.context.len() != arguments.len() {
            return Err("metavariable argument count mismatch".into());
        }
        let Some(value) = abstract_pattern(&env.arena, value, arguments)? else {
            return Ok(Outcome::Blocked);
        };
        let entry = self.entries[id.index as usize]
            .as_mut()
            .ok_or(Error::InvalidMeta(id))?;
        entry.assignment = Some(value);
        let entry = entry.clone();
        self.constrain(Constraint::Validate {
            context: entry.context.clone(),
            term: value,
            expected: entry.expected,
        });
        if let Some(expected) = entry.expected {
            self.constrain(Constraint::HasType {
                context: entry.context.clone(),
                term: value,
                expected,
            });
        }
        self.changed();
        Ok(Outcome::Solved)
    }

    pub fn unify(
        &mut self,
        env: &Environment,
        context: &Context,
        left: Expression,
        right: Expression,
    ) -> Result<Outcome, Error> {
        if !env.arena.contains_meta(left) && !env.arena.contains_meta(right) {
            return if crate::reduction::erased_convertible(env, left, right)? {
                Ok(Outcome::Solved)
            } else {
                Err("incompatible rigid expressions in metavariable constraint".into())
            };
        }
        self.record(Constraint::Equal {
            context: context.clone(),
            left,
            right,
        });
        let snapshot = self.snapshot();
        match self.unify_inner(env, context, left, right, &mut FxHashSet::default()) {
            Ok(Outcome::Blocked) => {
                self.constrain(Constraint::Equal {
                    context: context.clone(),
                    left,
                    right,
                });
                Ok(Outcome::Blocked)
            }
            Ok(Outcome::Solved) => Ok(Outcome::Solved),
            Err(error) => {
                self.rollback(snapshot)?;
                Err(error)
            }
        }
    }
    fn unify_inner(
        &mut self,
        env: &Environment,
        context: &Context,
        left: Expression,
        right: Expression,
        active: &mut FxHashSet<(Expression, Expression)>,
    ) -> Result<Outcome, Error> {
        for term in [left, right] {
            if let Node::Meta { id, arguments } = env.arena.get(term) {
                let declaration = self.entry(id)?.context.clone();
                if declaration.len() != arguments.len() {
                    return Err("metavariable argument count mismatch".into());
                }
                for (i, binding) in declaration.iter().enumerate() {
                    let expected = instantiate(&env.arena, binding.ty, &arguments[..i])?;
                    self.check(env, context.clone(), arguments[i], expected)?;
                }
            }
        }
        let left = self.zonk(&env.arena, left)?;
        let right = self.zonk(&env.arena, right)?;
        if !env.arena.contains_meta(left) && !env.arena.contains_meta(right) {
            return if crate::reduction::erased_convertible(env, left, right)? {
                Ok(Outcome::Solved)
            } else {
                Err("incompatible rigid expressions in metavariable constraint".into())
            };
        }
        if alpha_equal(&env.arena, left, right) {
            return Ok(Outcome::Solved);
        }
        match (env.arena.get(left), env.arena.get(right)) {
            (Node::Meta { id, .. }, Node::Meta { id: other, .. }) if id == other => {}
            (
                Node::Meta { id, arguments },
                Node::Meta {
                    id: other,
                    arguments: other_arguments,
                },
            ) => {
                let left_first = self.entry(id)?.context.len() >= self.entry(other)?.context.len();
                let options = if left_first {
                    [(id, &arguments, right), (other, &other_arguments, left)]
                } else {
                    [(other, &other_arguments, left), (id, &arguments, right)]
                };
                for (id, arguments, value) in options {
                    let snapshot = self.snapshot();
                    match self.assign(env, id, arguments, value) {
                        Ok(Outcome::Solved) => return Ok(Outcome::Solved),
                        Ok(Outcome::Blocked) => self.rollback(snapshot)?,
                        Err(Error::Contradiction(message))
                            if message.contains("outside its context") =>
                        {
                            self.rollback(snapshot)?
                        }
                        Err(error) => {
                            self.rollback(snapshot)?;
                            return Err(error);
                        }
                    }
                }
                return Ok(Outcome::Blocked);
            }
            (Node::Meta { id, arguments }, _) => return self.assign(env, id, &arguments, right),
            (_, Node::Meta { id, arguments }) => return self.assign(env, id, &arguments, left),
            _ => {}
        }
        // Prefer congruence before unfolding; it exposes contextual holes in
        // arguments even when a definition's body eliminates its arguments.
        if skeleton(&env.arena, left) == skeleton(&env.arena, right) {
            let snapshot = self.snapshot();
            let attempt = (|| {
                let mut solved = true;
                for (slot, ((l, ld), (r, rd))) in comparison_children(&env.arena, left)
                    .into_iter()
                    .zip(comparison_children(&env.arena, right))
                    .enumerate()
                {
                    if ld != rd {
                        return Err(Error::from("incompatible binder structure"));
                    }
                    solved &= self.unify_child(env, context, left, slot, ld, l, r, active)?
                        == Outcome::Solved;
                }
                Ok(solved)
            })();
            match attempt {
                Ok(true) => return Ok(Outcome::Solved),
                Ok(false) => {}
                Err(_) => self.rollback(snapshot)?,
            }
        }
        let left = env.erased_head(self.zonk(&env.arena, left)?)?;
        let right = env.erased_head(self.zonk(&env.arena, right)?)?;
        if alpha_equal(&env.arena, left, right) {
            return Ok(Outcome::Solved);
        }
        if !active.insert((left, right)) {
            return Ok(Outcome::Blocked);
        }
        let result = match (env.arena.get(left), env.arena.get(right)) {
            (Node::Meta { id, .. }, Node::Meta { id: other, .. }) if id == other => {
                Ok(Outcome::Blocked)
            }
            (Node::Meta { id, arguments }, _) => self.assign(env, id, &arguments, right),
            (_, Node::Meta { id, arguments }) => self.assign(env, id, &arguments, left),
            _ => {
                if skeleton(&env.arena, left) != skeleton(&env.arena, right) {
                    if !self.unresolved(&env.arena, [left, right])?.is_empty() {
                        Ok(Outcome::Blocked)
                    } else {
                        Err("incompatible rigid expressions in metavariable constraint".into())
                    }
                } else {
                    let mut solved = true;
                    for (slot, ((l, ld), (r, rd))) in comparison_children(&env.arena, left)
                        .into_iter()
                        .zip(comparison_children(&env.arena, right))
                        .enumerate()
                    {
                        if ld != rd {
                            return Err("incompatible binder structure".into());
                        }
                        solved &= self.unify_child(env, context, left, slot, ld, l, r, active)?
                            == Outcome::Solved;
                    }
                    Ok(if solved {
                        Outcome::Solved
                    } else {
                        Outcome::Blocked
                    })
                }
            }
        };
        active.remove(&(left, right));
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn unify_child(
        &mut self,
        env: &Environment,
        context: &Context,
        parent: Expression,
        slot: usize,
        depth: usize,
        left: Expression,
        right: Expression,
        active: &mut FxHashSet<(Expression, Expression)>,
    ) -> Result<Outcome, Error> {
        if depth == 0 {
            return self.unify_inner(env, context, left, right, active);
        }
        let mut checker = crate::check::Checker::new(env, self, context.clone());
        checker.solving = true;
        let context = checker.child_context(parent, slot)?;
        self.unify_inner(env, &context, left, right, active)
    }
    pub(crate) fn ensure_type(&mut self, arena: &Arena, id: MetaId) -> Result<Expression, Error> {
        let entry = self.entry(id)?;
        if let Some(ty) = entry.expected {
            return Ok(ty);
        }
        let context = entry.context.clone();
        let ty = self.fresh(arena, context, None);
        self.entries[id.index as usize].as_mut().unwrap().expected = Some(ty);
        self.changed();
        Ok(ty)
    }
    pub(crate) fn expect(
        &mut self,
        env: &Environment,
        id: MetaId,
        arguments: &[Expression],
        expected: Expression,
    ) -> Result<(), Error> {
        let entry = self.entry(id)?;
        if entry.expected.is_some() {
            return Ok(());
        }
        if self.occurs(&env.arena, id, expected)? {
            return Err("cyclic metavariable type".into());
        }
        if let Some(expected) = abstract_pattern(&env.arena, expected, arguments)? {
            self.entries[id.index as usize].as_mut().unwrap().expected = Some(expected);
            self.changed();
        }
        Ok(())
    }
    /// Generate constraints using the same rules as strict checking.
    pub fn check(
        &mut self,
        env: &Environment,
        context: Context,
        term: Expression,
        expected: Expression,
    ) -> Result<Outcome, Error> {
        if [term, expected]
            .into_iter()
            .chain(context.iter().map(|b| b.ty))
            .all(|e| !env.arena.contains_meta(e))
        {
            crate::check::Checker::new(env, self, context).check(term, expected)?;
            return Ok(Outcome::Solved);
        }
        let snapshot = self.snapshot();
        let result = self.attempt_type(env, &context, term, Some(expected), true);
        match result {
            Ok(Outcome::Solved) => {
                self.constrain(Constraint::Validate {
                    context,
                    term,
                    expected: Some(expected),
                });
                Ok(Outcome::Solved)
            }
            Ok(Outcome::Blocked) => {
                self.constrain(Constraint::HasType {
                    context,
                    term,
                    expected,
                });
                Ok(Outcome::Blocked)
            }
            Err(error) => {
                self.rollback(snapshot)?;
                Err(error)
            }
        }
    }
    fn attempt_type(
        &mut self,
        env: &Environment,
        context: &Context,
        term: Expression,
        expected: Option<Expression>,
        solving: bool,
    ) -> Result<Outcome, Error> {
        let result = {
            let mut checker = crate::check::Checker::new(env, self, context.clone());
            checker.solving = solving;
            if solving {
                match expected {
                    Some(ty) => checker.check_open(term, ty),
                    None => checker.infer_open(term).map(|_| ()),
                }
            } else {
                match expected {
                    Some(ty) => checker.check(term, ty),
                    None => checker.validate(term),
                }
            }
        };
        match result {
            Ok(()) => Ok(Outcome::Solved),
            Err(Error::Unresolved { .. }) => Ok(Outcome::Blocked),
            Err(error @ Error::TypeMismatch(_)) => Err(error),
            Err(Error::Contradiction(message))
                if message.contains("incompatible rigid expressions")
                    || message.contains("outside its context")
                    || message.contains("occurs check") =>
            {
                Err(Error::Contradiction(message))
            }
            Err(error) => {
                // A rule may need the head of a still unknown type to proceed.
                let roots = std::iter::once(term)
                    .chain(expected)
                    .chain(context.iter().map(|b| b.ty));
                if self.unresolved(&env.arena, roots)?.is_empty() {
                    Err(error)
                } else {
                    Ok(Outcome::Blocked)
                }
            }
        }
    }
    pub fn infer(
        &mut self,
        env: &Environment,
        context: Context,
        term: Expression,
    ) -> Result<Expression, Error> {
        if std::iter::once(term)
            .chain(context.iter().map(|b| b.ty))
            .all(|e| !env.arena.contains_meta(e))
        {
            return crate::check::Checker::new(env, self, context).infer(term);
        }
        let snapshot = self.snapshot();
        let result = {
            let mut checker = crate::check::Checker::new(env, self, context.clone());
            checker.solving = true;
            checker.infer_open(term)
        };
        match result {
            Ok(ty) => {
                self.constrain(Constraint::Validate {
                    context,
                    term,
                    expected: Some(ty),
                });
                Ok(ty)
            }
            Err(error) => {
                if matches!(&error, Error::TypeMismatch(_))
                    || matches!(&error,Error::Contradiction(message) if message.contains("occurs check") || message.contains("outside its context") || message.contains("incompatible rigid expressions"))
                {
                    self.rollback(snapshot)?;
                    return Err(error);
                }
                if self
                    .unresolved(
                        &env.arena,
                        std::iter::once(term).chain(context.iter().map(|b| b.ty)),
                    )?
                    .is_empty()
                {
                    self.rollback(snapshot)?;
                    return Err(error);
                }
                let ty = self.fresh(&env.arena, context.clone(), None);
                self.constrain(Constraint::HasType {
                    context,
                    term,
                    expected: ty,
                });
                Ok(ty)
            }
        }
    }
    pub fn solve_pending(&mut self, env: &Environment) -> Result<Outcome, Error> {
        let snapshot = self.snapshot();
        let result = (|| {
            let mut waiting = FxHashMap::default();
            loop {
                let revision = self.revision;
                let mut pending = std::mem::take(&mut self.constraints);
                let mut blocked = Vec::new();
                while let Some(constraint) = pending.pop() {
                    let dependencies = self.dependencies(&env.arena, &constraint)?;
                    if waiting.get(&constraint) == Some(&dependencies) {
                        blocked.push(constraint);
                        continue;
                    }
                    let outcome = match &constraint {
                        Constraint::Equal {
                            context,
                            left,
                            right,
                        } => self.unify_inner(
                            env,
                            context,
                            *left,
                            *right,
                            &mut FxHashSet::default(),
                        )?,
                        Constraint::HasType {
                            context,
                            term,
                            expected,
                        } => self.attempt_type(env, context, *term, Some(*expected), true)?,
                        Constraint::Validate {
                            context,
                            term,
                            expected,
                        } => self.attempt_type(env, context, *term, *expected, false)?,
                        Constraint::IsSort { context, term } => {
                            let result = crate::check::Checker::new(env, self, context.clone())
                                .formation(*term);
                            match result {
                                Ok(_) => Outcome::Solved,
                                Err(Error::Unresolved { .. }) => Outcome::Blocked,
                                Err(error) => {
                                    if self.unresolved(&env.arena, [*term])?.is_empty() {
                                        return Err(error);
                                    }
                                    Outcome::Blocked
                                }
                            }
                        }
                    };
                    if outcome == Outcome::Blocked {
                        waiting.insert(
                            constraint.clone(),
                            self.dependencies(&env.arena, &constraint)?,
                        );
                        blocked.push(constraint);
                    } else {
                        waiting.remove(&constraint);
                    }
                    pending.append(&mut self.constraints);
                }
                self.constraints = blocked;
                if self.revision == revision {
                    return Ok(if self.constraints.is_empty() {
                        Outcome::Solved
                    } else {
                        Outcome::Blocked
                    });
                }
            }
        })();
        if result.is_err() {
            self.rollback(snapshot)?;
        }
        result
    }
    /// A declaration succeeds only after every generated meta and obligation is solved.
    pub fn finish(&mut self, env: &Environment) -> Result<(), Error> {
        self.solve_pending(env)?;
        let metas = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                entry
                    .as_ref()
                    .filter(|e| e.assignment.is_none())
                    .map(|_| MetaId {
                        session: self.session,
                        index: index as u32,
                    })
            })
            .collect::<Vec<_>>();
        if !metas.is_empty() || !self.constraints.is_empty() {
            return Err(Error::Unresolved {
                metas,
                constraints: self.constraints.len(),
            });
        }
        let entries = self.entries.iter().flatten().cloned().collect::<Vec<_>>();
        for entry in entries {
            let mut checker = crate::check::Checker::new(env, self, entry.context);
            let value = entry.assignment.ok_or("missing meta assignment")?;
            match entry.expected {
                Some(ty) => checker.check(value, ty)?,
                None => {
                    checker.validate(value)?;
                }
            }
        }
        Ok(())
    }
}
