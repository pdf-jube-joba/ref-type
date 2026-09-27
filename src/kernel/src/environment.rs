pub use crate::syntax::{Binding, Context};
// PTS environment and reduction over the shared expression arena.
use crate::{
    calculus::*,
    ids::{DefinitionId, InductiveId, ParameterId, ProgramInductiveId},
    sort::{BaseSort, Sort},
    syntax::*,
};
use rustc_hash::FxHashMap;
use std::{
    cell::RefCell,
    sync::atomic::{AtomicU64, Ordering},
};

#[derive(Debug, Clone)]
pub struct Definition {
    pub context: Context,
    pub ty: Expression,
    pub body: Expression,
}
#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub parameters: Context,
    pub arity: Expression,
    pub constructors: Vec<Expression>,
    pub sort: Sort,
}
#[derive(Debug, Clone)]
pub struct Datatype {
    pub parameters: Context,
    pub level: usize,
    pub constructors: Vec<Context>,
    pub reflected: InductiveId,
}
#[derive(Debug)]
pub struct Environment {
    pub arena: Arena,
    pub(crate) identity: u64,
    pub(crate) definitions: Vec<Definition>,
    parameters: FxHashMap<ParameterId, Expression>,
    pub(crate) reflected: FxHashMap<DefinitionId, DefinitionId>,
    program_parameters: FxHashMap<DefinitionId, Vec<bool>>,
    pub(crate) inductives: FxHashMap<InductiveId, InductiveSpec>,
    pub(crate) datatypes: FxHashMap<ProgramInductiveId, Datatype>,
    pub(crate) contexts: RefCell<crate::sharing::ContextInterner<Expression>>,
    pub(crate) inferred: RefCell<FxHashMap<(crate::sharing::ContextId, Expression), Expression>>,
    pub(crate) conversions: RefCell<FxHashMap<(Expression, Expression, bool), bool>>,
    pub(crate) heads: RefCell<FxHashMap<Expression, Expression>>,
}
impl Default for Environment {
    fn default() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self {
            arena: Arena::new(),
            identity: NEXT.fetch_add(1, Ordering::Relaxed),
            definitions: Vec::new(),
            parameters: FxHashMap::default(),
            reflected: FxHashMap::default(),
            program_parameters: FxHashMap::default(),
            inductives: FxHashMap::default(),
            datatypes: FxHashMap::default(),
            contexts: RefCell::default(),
            inferred: RefCell::default(),
            conversions: RefCell::default(),
            heads: RefCell::default(),
        }
    }
}
impl Environment {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_arena(arena: Arena) -> Self {
        Self {
            arena,
            ..Self::default()
        }
    }
    pub fn reflected_definition(&self, id: DefinitionId) -> Option<DefinitionId> {
        self.reflected.get(&id).copied()
    }
    pub fn referenced_definition(&self, e: Expression) -> Option<DefinitionId> {
        if let Node::Definition { id, .. } = self.arena.get(e) {
            Some(id)
        } else {
            None
        }
    }
    pub fn arena(&self) -> &Arena {
        &self.arena
    }
    pub fn inductive(&self, id: InductiveId) -> Option<&InductiveSpec> {
        self.inductives.get(&id)
    }
    pub fn datatype(&self, id: ProgramInductiveId) -> Option<&Datatype> {
        self.datatypes.get(&id)
    }
    pub fn cache_counts(&self) -> [(&'static str, usize); 4] {
        [
            ("heads", self.heads.borrow().len()),
            ("inferred", self.inferred.borrow().len()),
            ("conversions", self.conversions.borrow().len()),
            ("context bindings", self.contexts.borrow().len()),
        ]
    }
    pub fn declaration_node_count(&self) -> usize {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut pending = vec![];
        for d in &self.definitions {
            pending.extend([d.ty, d.body]);
            pending.extend(d.context.iter().map(|b| b.ty));
        }
        for d in self.inductives.values() {
            pending.push(d.arity);
            pending.extend(&d.constructors);
            pending.extend(d.parameters.iter().map(|b| b.ty));
        }
        for d in self.datatypes.values() {
            pending.extend(d.parameters.iter().map(|b| b.ty));
            for fields in &d.constructors {
                pending.extend(fields.iter().map(|b| b.ty));
            }
        }
        while let Some(e) = pending.pop() {
            if seen.insert(e) {
                pending.extend(self.arena.children(e).into_iter().map(|(child, _)| child));
            }
        }
        seen.len()
    }
    pub fn parameter(&self, id: ParameterId) -> Option<Expression> {
        self.parameters.get(&id).copied()
    }
    pub fn register_parameter(
        &mut self,
        id: ParameterId,
        ty: Expression,
    ) -> Result<(), crate::metavariables::Error> {
        if let Some(previous) = self.parameter(id) {
            if previous != ty {
                return Err("parameter identity already registered".into());
            }
            return Ok(());
        }
        let mut metas = crate::metavariables::MetaContext::new();
        crate::check::Checker::new(self, &mut metas, vec![]).infer(ty)?;
        self.parameters.insert(id, ty);
        Ok(())
    }
    pub fn contains_parameter(&self, expression: Expression) -> bool {
        let mut pending = vec![expression];
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if !seen.insert(e) {
                continue;
            }
            if matches!(self.arena.get(e), Node::Parameter(_)) {
                return true;
            }
            pending.extend(self.arena.children(e).into_iter().map(|(e, _)| e));
        }
        false
    }
    pub fn definition(&self, id: DefinitionId) -> Result<&Definition, String> {
        if id.arena != self.identity {
            return Err("definition belongs to a different arena".into());
        }
        self.definitions
            .get(id.index as usize)
            .ok_or_else(|| "unknown definition".into())
    }
    pub fn reference(
        &self,
        id: DefinitionId,
        arguments: Vec<Expression>,
    ) -> Result<Expression, String> {
        let definition = self.definition(id)?;
        if definition.context.len() != arguments.len() {
            return Err("definition parameter count mismatch".into());
        }
        Ok(self.arena.alloc(Node::Definition { id, arguments }))
    }
    pub fn whnf(&self, expression: Expression) -> Result<Expression, String> {
        if let Some(&cached) = self.heads.borrow().get(&expression) {
            return Ok(cached);
        }
        let mut e = expression;
        for _ in 0..100_000 {
            if let Some(next) = crate::reduction::head_application(self, e)? {
                e = next;
                continue;
            }
            if let Some(next) = crate::reduction::root(self, e)?
                && next != e {
                    e = next;
                    continue;
                }
            let next = crate::reduction::map_head(self, e, |child| self.whnf(child))?;
            if next == e {
                self.heads.borrow_mut().insert(expression, e);
                return Ok(e);
            }
            e = next;
        }
        Err("head normalization fuel exhausted".into())
    }

    pub fn erased_head(&self, mut e: Expression) -> Result<Expression, String> {
        loop {
            e = self.whnf(e)?;
            if let Node::SubsetIntro { element, .. } = self.arena.get(e) {
                e = element;
            } else {
                return Ok(e);
            }
        }
    }
    pub fn reflect_bound(&self, term: Expression) -> Result<Expression, String> {
        crate::reflection::Reflection::new(self).reflect_bound(term)
    }
    pub(crate) fn reflect_step(&self, term: Expression) -> Result<Option<Expression>, String> {
        crate::reflection::Reflection::new(self).reflect_step(term)
    }
    fn resolve_reflections(&self, term: Expression, depth: usize) -> Result<Expression, String> {
        crate::reflection::Reflection::new(self).resolve_reflections(term, depth)
    }
    pub(crate) fn recursive_field(
        &self,
        ind: InductiveId,
        mut ty: Expression,
    ) -> Result<bool, String> {
        loop {
            ty = self.whnf(ty)?;
            match self.arena.get(ty) {
                Node::Product { body, .. } => ty = body,
                _ => {
                    while let Node::App { function, .. } = self.arena.get(ty) {
                        ty = function;
                    }
                    return Ok(
                        matches!(self.arena.get(ty),Node::IndType { inductive,.. } if inductive==ind),
                    );
                }
            }
        }
    }
    fn contains_inductive(
        &self,
        expression: Expression,
        target: InductiveId,
    ) -> Result<bool, String> {
        let mut pending = vec![expression];
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.arena.get(e) {
                Node::IndType { inductive, .. } | Node::IndCtor { inductive, .. }
                    if inductive == target =>
                {
                    return Ok(true);
                }
                Node::Definition { id, .. } => pending.push(self.definition(id)?.body),
                _ => {}
            }
            pending.extend(self.arena.children(e).into_iter().map(|(child, _)| child));
        }
        Ok(false)
    }
    fn check_positive(
        &self,
        expression: Expression,
        target: InductiveId,
        positive: bool,
    ) -> Result<(), String> {
        if !self.contains_inductive(expression, target)? {
            return Ok(());
        }
        let e = self.whnf(expression)?;
        let inductive = match self.arena.get(e) {
            Node::IndType { inductive, .. } => Some(inductive == target),
            _ => None,
        };
        if inductive == Some(true) && !positive {
            return Err("inductive occurs in a non-strictly-positive position".into());
        }
        if let Node::Product { domain, body, .. } = self.arena.get(e) {
            self.check_positive(domain, target, false)?;
            return self.check_positive(body, target, positive);
        }
        let positive =
            positive && inductive != Some(false) && !matches!(self.arena.get(e), Node::App { .. });
        for (child, _) in self.arena.children(e) {
            self.check_positive(child, target, positive)?;
        }
        Ok(())
    }
    pub(crate) fn singleton_elimination(&self, id: InductiveId) -> Result<bool, String> {
        let spec = self.inductives.get(&id).ok_or("unknown inductive")?;
        if spec.constructors.len() != 1 || !matches!(self.arena.get(spec.arity), Node::Sort(_)) {
            return Ok(false);
        }
        let mut ty = spec.constructors[0];
        while let Node::Product { domain, body, .. } = self.arena.get(ty) {
            if self.contains_inductive(domain, id)? {
                return Ok(false);
            }
            ty = body;
        }
        Ok(true)
    }
    pub fn register_inductive(
        &mut self,
        id: InductiveId,
        spec: InductiveSpec,
    ) -> Result<(), crate::metavariables::Error> {
        use crate::{check::Checker, metavariables::MetaContext};
        if self.inductives.contains_key(&id) {
            return Err("duplicate inductive".into());
        }
        for ty in spec.parameters.iter().map(|b| b.ty).chain([spec.arity]) {
            if self.contains_inductive(ty, id)? {
                return Err("inductive occurs in its parameter telescope or arity".into());
            }
        }
        self.inductives.insert(id, spec.clone());
        let result = (|| {
            let mut metas = MetaContext::new();
            let mut checker = Checker::new(self, &mut metas, spec.parameters.clone());
            checker.check_context()?;
            checker.infer(spec.arity)?;
            for &ty in &spec.constructors {
                checker.metas.require_solved(&self.arena, [ty])?;
                if checker.formation(ty)? != spec.sort {
                    return Err("constructor universe does not match inductive".into());
                }
                let mut tail = ty;
                loop {
                    let head = self.whnf(tail)?;
                    if let Node::Product { domain, body, .. } = self.arena.get(head) {
                        self.check_positive(domain, id, true)?;
                        tail = body;
                    } else {
                        let mut head = head;
                        while let Node::App { function, .. } = self.arena.get(head) {
                            head = function;
                        }
                        if !matches!(self.arena.get(head),Node::IndType { inductive,.. } if inductive==id)
                        {
                            return Err("constructor does not return its declared inductive".into());
                        }
                        break;
                    }
                }
            }
            Ok(())
        })();
        if result.is_err() {
            self.inductives.remove(&id);
            self.heads.borrow_mut().clear();
            self.inferred.borrow_mut().clear();
            self.conversions.borrow_mut().clear();
        }
        result
    }
    #[tracing::instrument(target = "ref_type::declarations", level = "debug", skip_all)]
    pub fn register_definition(
        &mut self,
        metas: &mut crate::metavariables::MetaContext,
        definition: Definition,
    ) -> Result<DefinitionId, crate::metavariables::Error> {
        let mark = self.arena.scratch_mark();
        let result = self.register_definition_inner(metas, definition);
        let mut roots = metas.roots();
        for definition in &self.definitions {
            roots.extend([definition.ty, definition.body]);
            roots.extend(definition.context.iter().map(|b| b.ty));
        }
        roots.extend(self.contexts.borrow().bindings().copied());
        if let Err(crate::metavariables::Error::TypeMismatch(error)) = &result {
            roots.extend([error.term, error.inferred, error.expected]);
            roots.extend(error.context.iter().map(|b| b.ty));
        }
        if self.arena.finish_scratch(mark, roots) > 0 {
            self.heads
                .borrow_mut()
                .retain(|key, value| self.arena.is_live(*key) && self.arena.is_live(*value));
            self.inferred
                .borrow_mut()
                .retain(|(_, key), value| self.arena.is_live(*key) && self.arena.is_live(*value));
            self.conversions.borrow_mut().retain(|(left, right, _), _| {
                self.arena.is_live(*left) && self.arena.is_live(*right)
            });
            metas.retain_caches(&self.arena);
        }
        result
    }
    fn register_definition_inner(
        &mut self,
        metas: &mut crate::metavariables::MetaContext,
        definition: Definition,
    ) -> Result<DefinitionId, crate::metavariables::Error> {
        use crate::check::Checker;
        metas.finish(self)?;
        if std::iter::once(definition.body)
            .chain([definition.ty])
            .chain(definition.context.iter().map(|b| b.ty))
            .any(|e| self.contains_parameter(e))
        {
            return Err("module parameters must be captured in the declaration telescope".into());
        }
        Checker::new(self, metas, definition.context.clone())
            .check(definition.body, definition.ty)?;
        let context = definition
            .context
            .iter()
            .map(|b| {
                Ok(Binding {
                    var: b.var,
                    ty: metas.zonk(&self.arena, b.ty)?,
                })
            })
            .collect::<Result<Context, crate::metavariables::Error>>()?;
        let ty = metas.zonk(&self.arena, definition.ty)?;
        let body = metas.zonk(&self.arena, definition.body)?;
        let definition = Definition { context, ty, body };
        let sort = match self.arena.get(self.whnf(ty)?) {
            Node::Sort(Sort::Upper(sort)) => sort,
            _ => Checker::new(self, metas, definition.context.clone())
                .formation(ty)?
                .base(),
        };
        let mut parameter_modes = vec![];
        let reflected = if sort.is_program() {
            let mut context = Vec::new();
            let mut prefix = vec![];
            for binding in &definition.context {
                let program = Checker::new(self, metas, prefix.clone())
                    .formation(binding.ty)?
                    .base()
                    .is_program();
                parameter_modes.push(program);
                let ty = if program {
                    self.reflect_bound(binding.ty)?
                } else {
                    self.resolve_reflections(binding.ty, usize::MAX)?
                };
                context.push(Binding {
                    var: binding.var,
                    ty,
                });
                prefix.push(binding.clone());
            }
            let ty = self.reflect_bound(ty)?;
            let body = self.reflect_bound(body)?;
            Checker::new(self, metas, context.clone()).check(body, ty)?;
            Some(Definition { context, ty, body })
        } else {
            None
        };
        let id = DefinitionId {
            arena: self.identity,
            index: u32::try_from(self.definitions.len())
                .map_err(|_| "definition arena exhausted")?,
        };
        self.definitions.push(definition);
        if let Some(reflected) = reflected {
            let target = DefinitionId {
                arena: self.identity,
                index: u32::try_from(self.definitions.len())
                    .map_err(|_| "definition arena exhausted")?,
            };
            self.definitions.push(reflected);
            self.reflected.insert(id, target);
            self.program_parameters.insert(id, parameter_modes);
        }
        Ok(id)
    }
    pub fn register_datatype(
        &mut self,
        id: ProgramInductiveId,
        spec: Datatype,
    ) -> Result<(), crate::metavariables::Error> {
        use crate::{check::Checker, ids::SymbolId, metavariables::MetaContext};
        if self.datatypes.contains_key(&id) {
            return Err("duplicate Program datatype".into());
        }
        if self
            .datatypes
            .values()
            .any(|d| d.reflected == spec.reflected)
        {
            return Err("datatype mirror identity is already owned".into());
        }
        self.datatypes.insert(id, spec.clone());
        let result = (|| {
            let mut metas = MetaContext::new();
            let mut prefix = vec![];
            for binding in &spec.parameters {
                let sort = Checker::new(self, &mut metas, prefix.clone()).formation(binding.ty)?;
                if !sort.is_upper()
                    || !sort.base().is_program()
                    || sort.base().level().is_none_or(|i| i > spec.level)
                {
                    return Err("datatype parameter kind level exceeds result level".into());
                }
                prefix.push(binding.clone());
            }
            for fields in &spec.constructors {
                let mut checker = Checker::new(self, &mut metas, spec.parameters.clone());
                for field in fields {
                    let sort = checker.formation(field.ty)?;
                    if !matches!(sort,Sort::Base(BaseSort::Value(i)) if i<=spec.level) {
                        return Err("datatype field level exceeds result level".into());
                    }
                }
            }
            let parameters = spec
                .parameters
                .iter()
                .map(|b| {
                    Ok(Binding {
                        var: b.var,
                        ty: self.reflect_bound(b.ty)?,
                    })
                })
                .collect::<Result<Context, String>>()?;
            let arguments = (0..parameters.len())
                .rev()
                .map(|i| self.arena.bound(i))
                .collect::<Vec<_>>();
            let mut constructors = Vec::new();
            for fields in &spec.constructors {
                let result = self.arena.alloc(Node::IndType {
                    inductive: spec.reflected,
                    parameters: arguments.clone(),
                });
                let mut body = shift(&self.arena, result, fields.len(), 0)?;
                for (i, field) in fields.iter().enumerate().rev() {
                    let domain = shift(&self.arena, self.reflect_bound(field.ty)?, i, 0)?;
                    body = self.arena.alloc(Node::Product {
                        var: field.var,
                        domain,
                        body,
                    });
                }
                constructors.push(body);
            }
            let mirror = InductiveSpec {
                parameters,
                arity: self.arena.sort(Sort::Base(BaseSort::Set(spec.level))),
                constructors,
                sort: Sort::Base(BaseSort::Set(spec.level)),
            };
            if let Some(existing) = self.inductives.get(&spec.reflected) {
                if existing.sort != mirror.sort
                    || existing.parameters.len() != mirror.parameters.len()
                    || existing.constructors.len() != mirror.constructors.len()
                    || !alpha_equal(&self.arena, existing.arity, mirror.arity)
                    || !existing
                        .parameters
                        .iter()
                        .zip(&mirror.parameters)
                        .all(|(a, b)| alpha_equal(&self.arena, a.ty, b.ty))
                    || !existing
                        .constructors
                        .iter()
                        .zip(&mirror.constructors)
                        .all(|(&a, &b)| alpha_equal(&self.arena, a, b))
                {
                    return Err("Program datatype mirror does not match its declaration".into());
                }
            } else {
                self.register_inductive(spec.reflected, mirror)?;
            }
            let _ = SymbolId::ANONYMOUS;
            Ok(())
        })();
        if result.is_err() {
            self.datatypes.remove(&id);
            self.heads.borrow_mut().clear();
            self.inferred.borrow_mut().clear();
            self.conversions.borrow_mut().clear();
        }
        result
    }
}

impl crate::reflection::Resolver for Environment {
    fn arena(&self) -> &Arena {
        &self.arena
    }
    fn definition(&self, id: DefinitionId) -> Result<(DefinitionId, Vec<bool>), String> {
        Ok((
            *self
                .reflected
                .get(&id)
                .ok_or("missing reflected definition")?,
            self.program_parameters
                .get(&id)
                .ok_or("missing reflected parameter modes")?
                .clone(),
        ))
    }
    fn datatype(&self, id: ProgramInductiveId) -> Result<InductiveId, String> {
        Ok(self.datatypes.get(&id).ok_or("unknown datatype")?.reflected)
    }
}
