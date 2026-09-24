use super::{construction as build, structure};
use super::{sort::*, syntax::*};
use crate::ids::*;
use crate::sharing::ScopedCache;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Classifier {
    Expression(Expression),
    Upper(BaseSort),
}

impl<T: Into<Expression>> From<T> for Classifier {
    fn from(x: T) -> Self {
        Self::Expression(x.into())
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub var: SymbolId,
    pub classifier: Expression,
}

pub type Context = Vec<Binding>;
#[derive(Debug, Clone)]
pub struct Definition {
    pub context: Context,
    pub body: Expression,
    pub classifier: Classifier,
}
#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub parameters: Context,
    pub arity: Expression,
    /// Each constructor classifier is scoped under the parameter telescope.
    pub constructors: Vec<Expression>,
    pub sort: Sort,
}
#[derive(Debug, Clone)]
pub struct ProgramDatatype {
    pub parameters: Context,
    pub level: usize,
    pub constructors: Vec<Vec<(SymbolId, ValueType)>>,
    pub reflected: InductiveId,
}
#[derive(Debug, Default)]
pub struct Environment {
    pub(crate) publication_order: Vec<Declaration>,
    next_identity: std::cell::Cell<u32>,
    /// Innermost-first checking path from the latest failed judgement.
    pub check_error: std::cell::RefCell<Vec<Expression>>,
    pub(crate) arena: Arena,
    pub(crate) inference_cache:
        std::cell::RefCell<ScopedCache<(Expression, Vec<Expression>), Classifier>>,
    pub(crate) head_cache: std::cell::RefCell<ScopedCache<Expression, Expression>>,
    pub(crate) definitions: HashMap<GlobalId, Definition>,
    pub(crate) definition_templates: HashMap<GlobalId, Definition>,
    /// Checked outer telescope, addressed by stable de Bruijn levels.
    pub(crate) ambient: Context,
    pub(crate) inductives: HashMap<InductiveId, InductiveSpec>,
    pub(crate) datatypes: HashMap<ProgramInductiveId, ProgramDatatype>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Declaration {
    Binding(usize),
    Definition(GlobalId),
    Template(GlobalId),
    Inductive(InductiveId),
    Datatype(ProgramInductiveId),
}

struct CheckScope<'a> {
    env: &'a mut Environment,
    checkpoint: ArenaCheckpoint,
}

/// A recursive declaration is visible only while its premises are checked.
/// Failed checking and cooperative cancellation both roll back this scope.
struct Registration<'a> {
    env: &'a mut Environment,
    declaration: Declaration,
    publication_start: usize,
    committed: bool,
}

impl<'a> Registration<'a> {
    fn new(env: &'a mut Environment, declaration: Declaration) -> Self {
        Self {
            publication_start: env.publication_order.len(),
            env,
            declaration,
            committed: false,
        }
    }

    fn commit(&mut self) {
        self.env.publication_order.push(self.declaration);
        self.committed = true;
    }
}

impl Drop for Registration<'_> {
    fn drop(&mut self) {
        if self.committed {
            return;
        }
        let mut declarations = self.env.publication_order.split_off(self.publication_start);
        declarations.push(self.declaration);
        for declaration in declarations.into_iter().rev() {
            match declaration {
                Declaration::Inductive(id) => {
                    self.env.inductives.remove(&id);
                }
                Declaration::Datatype(id) => {
                    self.env.datatypes.remove(&id);
                }
                Declaration::Definition(id) => {
                    self.env.definitions.remove(&id);
                }
                Declaration::Template(id) => {
                    self.env.definition_templates.remove(&id);
                }
                Declaration::Binding(level) => self.env.ambient.truncate(level),
            }
        }
        self.env.inference_cache.get_mut().clear();
        self.env.head_cache.get_mut().clear();
    }
}

#[cfg(test)]
mod scope_tests {
    use super::*;

    #[test]
    fn scratch_scope_is_discarded_during_unwinding() {
        let mut env = Environment::new();
        let counts = env.arena.node_counts();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = env.check_scoped(|env| {
                let term: Expression = env
                    .arena
                    .alloc(SetKindNode {
                        level: 0,
                        form: SetKindForm::Base,
                    })
                    .into();
                env.head_cache.borrow_mut().insert(term, term);
                env.inference_cache
                    .borrow_mut()
                    .insert((term, vec![]), Classifier::Upper(BaseSort::Set(0)));
                panic!("interrupt scratch checking");
            });
        }));
        assert!(result.is_err());
        assert_eq!(env.arena.node_counts(), counts);
        assert!(env.cache_counts().iter().all(|(_, count)| *count == 0));
        env.check_scoped(|_| Ok(())).unwrap();
    }
}

impl Drop for CheckScope<'_> {
    fn drop(&mut self) {
        let checkpoint = self.checkpoint;
        self.env
            .inference_cache
            .get_mut()
            .finish_scope(|(e, context), classifier| {
                checkpoint.contains(*e)
                    && context.iter().all(|&ty| checkpoint.contains(ty))
                    && match classifier {
                        Classifier::Expression(ty) => checkpoint.contains(*ty),
                        Classifier::Upper(_) => true,
                    }
            });
        self.env
            .head_cache
            .get_mut()
            .finish_scope(|e, head| checkpoint.contains(*e) && checkpoint.contains(*head));
        self.env
            .check_error
            .get_mut()
            .retain(|&term| checkpoint.contains(term));
        self.env.arena.truncate(checkpoint);
    }
}

impl Environment {
    fn fresh_identity(&self) -> (ArenaId, u32) {
        let index = self.next_identity.get();
        self.next_identity
            .set(index.checked_add(1).expect("kernel identity exhausted"));
        (self.arena.id(), index)
    }

    pub fn fresh_global_id(&self) -> GlobalId {
        let (owner, index) = self.fresh_identity();
        GlobalId { owner, index }
    }

    pub fn fresh_inductive_id(&self) -> InductiveId {
        let (owner, index) = self.fresh_identity();
        InductiveId { owner, index }
    }

    pub fn fresh_datatype_id(&self) -> ProgramInductiveId {
        let (owner, index) = self.fresh_identity();
        ProgramInductiveId { owner, index }
    }

    fn check_identity(&self, owner: ArenaId) -> Result<(), String> {
        if owner != self.arena.id() {
            return Err("identity belongs to another checking environment".into());
        }
        Ok(())
    }

    fn check_scoped(
        &mut self,
        check: impl FnOnce(&Self) -> Result<(), String>,
    ) -> Result<(), String> {
        let checkpoint = self.arena.checkpoint();
        self.inference_cache.get_mut().begin_scope();
        self.head_cache.get_mut().begin_scope();
        let scope = CheckScope {
            env: self,
            checkpoint,
        };
        crate::control::checkpoint();
        check(scope.env)
    }

    pub(crate) fn check_definition(&mut self, definition: &Definition) -> Result<(), String> {
        self.check_scoped(|env| {
            let mut checker = super::check::Checker::new(env, definition.context.clone());
            checker.check_context()?;
            checker.check(definition.body, definition.classifier)?;
            if let Classifier::Expression(ty) = definition.classifier
                && env.arena.sort(ty).is_program()
            {
                let context = super::reflection::reflect_context(env, &definition.context)?;
                let ty = super::reflection::reflect_program_expression(env, ty)?;
                let body = super::reflection::reflect_program_expression(env, definition.body)?;
                super::check::Checker::new(env, context).check(body, ty)?;
            }
            Ok(())
        })
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Retained cache entries and the number of copied context bindings.
    pub fn cache_counts(&self) -> [(&'static str, usize); 3] {
        let inference = self.inference_cache.borrow();
        [
            ("inference", inference.len()),
            (
                "context bindings",
                inference.keys().map(|(_, ctx)| ctx.len()).sum(),
            ),
            ("weak heads", self.head_cache.borrow().len()),
        ]
    }

    /// Release inference and reduction working state while retaining declarations.
    pub fn clear_caches(&self) {
        *self.inference_cache.borrow_mut() = Default::default();
        *self.head_cache.borrow_mut() = Default::default();
    }

    /// Nodes reachable from declarations, excluding caches and external handles.
    pub fn declaration_node_count(&self) -> usize {
        let mut pending = Vec::new();
        for definition in self
            .definitions
            .values()
            .chain(self.definition_templates.values())
        {
            pending.push(definition.body);
            if let Classifier::Expression(ty) = definition.classifier {
                pending.push(ty);
            }
            pending.extend(definition.context.iter().map(|b| b.classifier));
        }
        pending.extend(self.ambient.iter().map(|b| b.classifier));
        for spec in self.inductives.values() {
            pending.push(spec.arity);
            pending.extend(spec.parameters.iter().map(|b| b.classifier));
            pending.extend(&spec.constructors);
        }
        for datatype in self.datatypes.values() {
            pending.extend(datatype.parameters.iter().map(|b| b.classifier));
            pending.extend(
                datatype
                    .constructors
                    .iter()
                    .flatten()
                    .map(|(_, ty)| Expression::from(*ty)),
            );
        }
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if seen.insert(e) {
                structure::visit_children(&self.arena, e, |child, _| pending.push(child));
            }
        }
        seen.len()
    }

    pub fn definition(&self, id: GlobalId) -> Option<&Definition> {
        self.definitions.get(&id)
    }

    pub fn definition_template(&self, id: GlobalId) -> Option<&Definition> {
        self.definition_templates.get(&id)
    }

    pub fn ambient_context(&self) -> &[Binding] {
        &self.ambient
    }

    pub fn inductive(&self, id: InductiveId) -> Option<&InductiveSpec> {
        self.inductives.get(&id)
    }

    pub fn datatype(&self, id: ProgramInductiveId) -> Option<&ProgramDatatype> {
        self.datatypes.get(&id)
    }
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_definition(
        &mut self,
        id: GlobalId,
        definition: Definition,
    ) -> Result<(), String> {
        self.check_identity(id.owner)?;
        self.check_owned_definition(&definition)?;
        if self.definitions.contains_key(&id) || self.definition_templates.contains_key(&id) {
            return Err("duplicate definition".into());
        }
        if !super::calculus::is_closed(&self.arena, definition.body)
            || matches!(definition.classifier,Classifier::Expression(t) if !super::calculus::is_closed(&self.arena,t))
        {
            return Err("a definition must abstract over its local bound variables".into());
        }
        self.check_definition(&definition)?;
        self.definitions.insert(id, definition);
        self.publication_order.push(Declaration::Definition(id));
        // Expressions contain annotations, not names. Adding metadata cannot
        // change the meaning of any previously checked expression.
        Ok(())
    }

    /// Check and retain an open definition whose local context is supplied by
    /// the caller. Templates are never exposed as closed named constants.
    pub fn register_definition_template(
        &mut self,
        id: GlobalId,
        definition: Definition,
    ) -> Result<(), String> {
        self.check_identity(id.owner)?;
        self.check_owned_definition(&definition)?;
        if self.definitions.contains_key(&id) || self.definition_templates.contains_key(&id) {
            return Err("duplicate definition template".into());
        }
        self.check_definition(&definition)?;
        self.definition_templates.insert(id, definition);
        self.publication_order.push(Declaration::Template(id));
        Ok(())
    }
    /// Check a binding in the existing prefix, then extend the outer context.
    pub fn push_binding(&mut self, binding: Binding) -> Result<usize, String> {
        self.check_owned(binding.classifier)?;
        if !super::calculus::locally_closed(&self.arena, binding.classifier) {
            return Err("an ambient binding cannot capture local bound variables".into());
        }
        self.check_scoped(|env| {
            let mut checker = super::check::Checker::new(env, vec![]);
            checker.formation(binding.classifier)?;
            Ok(())
        })?;
        let level = self.ambient.len();
        self.ambient.push(binding);
        self.publication_order.push(Declaration::Binding(level));
        Ok(level)
    }
}

impl Environment {
    fn check_owned(&self, term: Expression) -> Result<(), String> {
        if !self.arena.owns(term) {
            return Err("expression belongs to another checking environment".into());
        }
        Ok(())
    }

    fn check_owned_definition(&self, definition: &Definition) -> Result<(), String> {
        self.check_owned(definition.body)?;
        if let Classifier::Expression(ty) = definition.classifier {
            self.check_owned(ty)?;
        }
        for binding in &definition.context {
            self.check_owned(binding.classifier)?;
        }
        Ok(())
    }

    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_inductive(
        &mut self,
        id: InductiveId,
        spec: InductiveSpec,
    ) -> Result<(), String> {
        self.check_identity(id.owner)?;
        self.check_owned(spec.arity)?;
        for term in spec
            .parameters
            .iter()
            .map(|b| b.classifier)
            .chain(spec.constructors.iter().copied())
        {
            self.check_owned(term)?;
        }
        if self.inductives.contains_key(&id) {
            return Err("duplicate inductive".into());
        }
        for binding in &spec.parameters {
            if contains_inductive(self, binding.classifier, id) {
                return Err("inductive occurs in its parameter telescope".into());
            }
        }
        if contains_inductive(self, spec.arity, id) {
            return Err("inductive occurs in its arity".into());
        }
        self.inductives.insert(id, spec.clone());
        let mut registration = Registration::new(self, Declaration::Inductive(id));
        let result = registration.env.check_scoped(|env| {
            let mut checker = super::check::Checker::new(env, spec.parameters.clone());
            checker.check_context()?;
            if spec.sort.is_upper() {
                checker.check(spec.arity, Classifier::Upper(spec.sort.base()))?;
            } else {
                checker.formation(spec.arity)?;
            }
            for ty in &spec.constructors {
                let sort = checker.formation(*ty)?;
                if sort != spec.sort {
                    return Err("constructor universe does not match inductive".into());
                }
                let mut tail = *ty;
                loop {
                    // Positivity only needs to expose the constructor telescope
                    // and the head of its result.  Normalizing the entire tail
                    // also reduces parameters embedded in field and result types;
                    // those parameters can be arbitrarily large and are irrelevant
                    // to this check.
                    let head = super::calculus::whnf(env, tail)?;
                    if let Some(product) = structure::product(&env.arena, head) {
                        check_positive(env, product.domain, id, true)?;
                        tail = product.body;
                    } else {
                        let mut head = head;
                        while let Some(application) = structure::application(&env.arena, head) {
                            head = application.function;
                        }
                        if !structure::inductive_type(&env.arena, head)
                            .is_some_and(|(inductive, _)| inductive == id)
                        {
                            return Err("constructor does not return its declared inductive".into());
                        }
                        break;
                    }
                }
            }
            Ok(())
        });
        if result.is_ok() {
            registration.commit();
        }
        result
    }
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_datatype(
        &mut self,
        id: ProgramInductiveId,
        spec: ProgramDatatype,
    ) -> Result<(), String> {
        self.check_identity(id.owner)?;
        self.check_identity(spec.reflected.owner)?;
        for term in spec.parameters.iter().map(|b| b.classifier).chain(
            spec.constructors
                .iter()
                .flatten()
                .map(|(_, ty)| Expression::from(*ty)),
        ) {
            self.check_owned(term)?;
        }
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
        let mut registration = Registration::new(self, Declaration::Datatype(id));
        let result = registration
            .env
            .check_scoped(|env| {
                let mut checker = super::check::Checker::new(env, spec.parameters.clone());
                checker.check_context()?;
                for p in &spec.parameters {
                    let s = checker.formation(p.classifier)?;
                    if !s.is_upper()
                        || !s.base().is_program()
                        || s.base().level().unwrap() > spec.level
                    {
                        return Err("datatype parameter kind level exceeds result level".into());
                    }
                }
                for fields in &spec.constructors {
                    for (_, ty) in fields {
                        let s = checker.formation((*ty).into())?;
                        if !matches!(s,Sort::Base(BaseSort::Value(i)) if i<=spec.level) {
                            return Err("datatype field level exceeds result level".into());
                        }
                        check_program_positive(env, (*ty).into(), id, true)?;
                        let reflected = super::reflection::reflect_type(env, (*ty).into())?;
                        check_positive(env, reflected.into(), spec.reflected, true)?;
                    }
                }
                Ok(())
            })
            .and_then(|()| registration.env.install_datatype_mirror(&spec));
        if result.is_ok() {
            registration.commit();
        }
        result
    }
}

fn check_positive(
    env: &Environment,
    e: Expression,
    id: InductiveId,
    positive: bool,
) -> Result<(), String> {
    check_strictly_positive(
        env,
        e,
        RecursiveType::Logical(id),
        positive,
        &mut FxHashMap::default(),
    )
}
fn check_program_positive(
    env: &Environment,
    e: Expression,
    id: ProgramInductiveId,
    positive: bool,
) -> Result<(), String> {
    check_strictly_positive(
        env,
        e,
        RecursiveType::Program(id),
        positive,
        &mut FxHashMap::default(),
    )
}

#[derive(Clone, Copy)]
enum RecursiveType {
    Logical(InductiveId),
    Program(ProgramInductiveId),
}

fn check_strictly_positive(
    env: &Environment,
    e: Expression,
    target: RecursiveType,
    positive: bool,
    occurrences: &mut FxHashMap<Expression, bool>,
) -> Result<(), String> {
    if !contains_recursive_type(env, e, target, occurrences) {
        return Ok(());
    }
    // Head-normalize one node at a time. The recursive walk below visits every
    // relevant child itself and skips subtrees that cannot contain `target`.
    let e = super::calculus::whnf(env, e)?;
    let inductive = match target {
        RecursiveType::Logical(id) => {
            structure::inductive_type(&env.arena, e).map(|(actual, _)| actual == id)
        }
        RecursiveType::Program(id) => {
            structure::program_inductive(&env.arena, e).map(|(actual, _)| actual == id)
        }
    };
    if inductive == Some(true) && !positive {
        return Err(match target {
            RecursiveType::Logical(_) => {
                "inductive occurs in a non-strictly-positive position".into()
            }
            RecursiveType::Program(_) => {
                "Program datatype occurs in a non-strictly-positive position".into()
            }
        });
    }
    if let Some(product) = structure::product(&env.arena, e) {
        check_strictly_positive(env, product.domain, target, false, occurrences)?;
        return check_strictly_positive(env, product.body, target, positive, occurrences);
    }
    let positive =
        positive && inductive != Some(false) && structure::application(&env.arena, e).is_none();
    let mut result = Ok(());
    structure::visit_children(&env.arena, e, |child, _| {
        if result.is_ok() {
            result = check_strictly_positive(env, child, target, positive, occurrences);
        }
    });
    result
}
fn contains_inductive(env: &Environment, e: Expression, id: InductiveId) -> bool {
    contains_recursive_type(
        env,
        e,
        RecursiveType::Logical(id),
        &mut FxHashMap::default(),
    )
}
fn contains_recursive_type(
    env: &Environment,
    e: Expression,
    target: RecursiveType,
    cache: &mut FxHashMap<Expression, bool>,
) -> bool {
    if let Some(&found) = cache.get(&e) {
        return found;
    }
    let mut found = match target {
        RecursiveType::Logical(id) => structure::inductive_id(&env.arena, e) == Some(id),
        RecursiveType::Program(id) => {
            structure::program_inductive(&env.arena, e).map(|(actual, _)| actual) == Some(id)
        }
    };
    structure::visit_children(&env.arena, e, |child, _| {
        found = found || contains_recursive_type(env, child, target, cache);
    });
    cache.insert(e, found);
    found
}

impl Environment {
    pub(crate) fn singleton_elimination(&self, id: InductiveId) -> bool {
        let Some(spec) = self.inductive(id) else {
            return false;
        };
        if spec.constructors.len() != 1 || !structure::is_base(&self.arena, spec.arity) {
            return false;
        }
        let mut ty = spec.constructors[0];
        loop {
            if let Some(product) = structure::product(&self.arena, ty) {
                if contains_inductive(self, product.domain, id) {
                    return false;
                }
                ty = product.body
            } else {
                return true;
            }
        }
    }

    fn install_datatype_mirror(&mut self, spec: &ProgramDatatype) -> Result<(), String> {
        use super::calculus::{alpha_equal, shift};
        let sort = BaseSort::Set(spec.level);
        let parameters = super::reflection::reflect_context(self, &spec.parameters)?;
        let arity = build::base_kind(&self.arena, sort)?;
        let arguments = parameters
            .iter()
            .enumerate()
            .map(|(i, p)| {
                build::bound(
                    &self.arena,
                    self.arena.sort(p.classifier),
                    Stage::Type,
                    parameters.len() - i - 1,
                )?
                .try_into()
            })
            .collect::<Result<Vec<LogicalArgument>, String>>()?;
        let mut constructors = vec![];
        for fields in &spec.constructors {
            let result = build::inductive_type(
                &self.arena,
                sort,
                Stage::Type,
                spec.reflected,
                arguments.clone(),
            )?;
            let mut body = shift(&self.arena, result, fields.len(), 0)?;
            for (i, (var, ty)) in fields.iter().enumerate().rev() {
                let domain = super::reflection::reflect_type(self, (*ty).into())?;
                let domain = shift(&self.arena, domain, i, 0)?;
                let rule = ProductRule::new(Sort::Base(self.arena.sort(domain)), Sort::Base(sort))?;
                body = build::product(&self.arena, rule, *var, domain, body)?;
            }
            constructors.push(body);
        }
        let mirror = InductiveSpec {
            parameters,
            arity,
            constructors,
            sort: Sort::Base(sort),
        };
        if let Some(existing) = self.inductive(spec.reflected) {
            if existing.sort != mirror.sort
                || existing.parameters.len() != mirror.parameters.len()
                || existing.constructors.len() != mirror.constructors.len()
                || !alpha_equal(&self.arena, existing.arity, mirror.arity)
                || !existing
                    .parameters
                    .iter()
                    .zip(&mirror.parameters)
                    .all(|(a, b)| alpha_equal(&self.arena, a.classifier, b.classifier))
                || !existing
                    .constructors
                    .iter()
                    .zip(&mirror.constructors)
                    .all(|(&a, &b)| alpha_equal(&self.arena, a, b))
            {
                return Err("Program datatype mirror does not match its declaration".into());
            }
            Ok(())
        } else {
            self.register_inductive(spec.reflected, mirror)
        }
    }
}
