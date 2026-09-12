use super::{construction as build, structure};
use super::{sort::*, syntax::*};
use crate::ids::*;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    pub certified_reflection: Option<SetTerm>,
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
    pub(crate) arena: Arena,
    pub(crate) inference_cache:
        std::cell::RefCell<HashMap<(Expression, Vec<Expression>), Classifier>>,
    pub(crate) head_cache: std::cell::RefCell<HashMap<Expression, Expression>>,
    pub(crate) definitions: HashMap<DefId, Definition>,
    pub(crate) definition_templates: HashMap<DefId, Definition>,
    pub(crate) parameters: HashMap<ModuleParamId, Binding>,
    pub(crate) inductives: HashMap<InductiveId, InductiveSpec>,
    pub(crate) datatypes: HashMap<ProgramInductiveId, ProgramDatatype>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn definition(&self, id: DefId) -> Option<&Definition> {
        self.definitions.get(&id)
    }

    pub fn definition_template(&self, id: DefId) -> Option<&Definition> {
        self.definition_templates.get(&id)
    }

    pub fn parameter(&self, id: ModuleParamId) -> Option<&Binding> {
        self.parameters.get(&id)
    }

    pub fn inductive(&self, id: InductiveId) -> Option<&InductiveSpec> {
        self.inductives.get(&id)
    }

    pub fn datatype(&self, id: ProgramInductiveId) -> Option<&ProgramDatatype> {
        self.datatypes.get(&id)
    }
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_definition(&mut self, id: DefId, definition: Definition) -> Result<(), String> {
        if self.definitions.contains_key(&id) || self.definition_templates.contains_key(&id) {
            return Err("duplicate definition".into());
        }
        if !super::calculus::locally_closed(&self.arena, definition.body)
            || matches!(definition.classifier,Classifier::Expression(t) if !super::calculus::locally_closed(&self.arena,t))
            || definition.certified_reflection.is_some_and(|certificate| {
                !super::calculus::locally_closed(&self.arena, certificate.into())
            })
        {
            return Err("a definition must abstract over its local bound variables".into());
        }
        let mut checker = super::check::Checker::new(self, definition.context.clone());
        checker.check_context()?;
        checker.check(definition.body, definition.classifier)?;
        if let Some(certificate) = definition.certified_reflection {
            let Classifier::Expression(ty) = definition.classifier else {
                return Err("only Program terms have reflection certificates".into());
            };
            let context = super::reflection::reflect_context(self, &definition.context)?;
            let ty = super::reflection::reflect(self, ty)?;
            super::check::Checker::new(self, context).check(certificate, ty)?;
            super::reflection::reflect_with_certificate(self, definition.body, certificate)?;
        }
        self.definitions.insert(id, definition);
        // Normalization can have visited this name before it was registered.
        // Inference also depends on those cached conversion results.
        self.head_cache.borrow_mut().clear();
        self.inference_cache.borrow_mut().clear();
        Ok(())
    }

    /// Check and retain an open definition whose local context is supplied by
    /// the caller. Templates are never exposed as closed named constants.
    pub fn register_definition_template(
        &mut self,
        id: DefId,
        definition: Definition,
    ) -> Result<(), String> {
        if self.definitions.contains_key(&id) || self.definition_templates.contains_key(&id) {
            return Err("duplicate definition template".into());
        }
        let mut checker = super::check::Checker::new(self, definition.context.clone());
        checker.check_context()?;
        checker.check(definition.body, definition.classifier)?;
        if let Some(certificate) = definition.certified_reflection {
            let Classifier::Expression(ty) = definition.classifier else {
                return Err("only Program terms have reflection certificates".into());
            };
            let context = super::reflection::reflect_context(self, &definition.context)?;
            let ty = super::reflection::reflect(self, ty)?;
            super::check::Checker::new(self, context).check(certificate, ty)?;
            super::reflection::reflect_with_certificate(self, definition.body, certificate)?;
        }
        self.definition_templates.insert(id, definition);
        Ok(())
    }
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_parameter(
        &mut self,
        id: ModuleParamId,
        binding: Binding,
        context: Context,
    ) -> Result<(), String> {
        if self.parameters.contains_key(&id) {
            return Err("duplicate module parameter".into());
        }
        if !super::calculus::locally_closed(&self.arena, binding.classifier) {
            return Err("a named parameter cannot capture local bound variables".into());
        }
        let mut checker = super::check::Checker::new(self, context);
        checker.check_context()?;
        checker.formation(binding.classifier)?;
        self.parameters.insert(id, binding);
        Ok(())
    }
}

impl Environment {
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_inductive(
        &mut self,
        id: InductiveId,
        spec: InductiveSpec,
    ) -> Result<(), String> {
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
        let result = (|| {
            let mut checker = super::check::Checker::new(self, spec.parameters.clone());
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
                    let head = super::calculus::normalize(self, tail)?;
                    if let Some(product) = structure::product(&self.arena, head) {
                        check_positive(self, product.domain, id, true)?;
                        tail = product.body;
                    } else {
                        let mut head = head;
                        while let Some(application) = structure::application(&self.arena, head) {
                            head = application.function;
                        }
                        if !structure::inductive_type(&self.arena, head)
                            .is_some_and(|(inductive, _)| inductive == id)
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
            self.head_cache.borrow_mut().clear();
            self.inference_cache.borrow_mut().clear();
        }
        result
    }
    #[tracing::instrument(target="ref_type::typing::indexed",level="debug",skip_all,fields(?id),err)]
    pub fn register_datatype(
        &mut self,
        id: ProgramInductiveId,
        spec: ProgramDatatype,
    ) -> Result<(), String> {
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
            let mut checker = super::check::Checker::new(self, spec.parameters.clone());
            checker.check_context()?;
            for p in &spec.parameters {
                let s = checker.formation(p.classifier)?;
                if !s.is_upper() || !s.base().is_program() || s.base().level().unwrap() > spec.level
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
                    check_program_positive(self, (*ty).into(), id, true)?;
                    let reflected = super::reflection::reflect(self, (*ty).into())?;
                    check_positive(self, reflected, spec.reflected, true)?;
                }
            }
            Ok(())
        })()
        .and_then(|()| self.install_datatype_mirror(&spec));
        if result.is_err() {
            self.datatypes.remove(&id);
            self.head_cache.borrow_mut().clear();
            self.inference_cache.borrow_mut().clear();
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
    let e = super::calculus::normalize(env, e)?;
    let inductive = structure::inductive_type(&env.arena, e).map(|(id, _)| id);
    if inductive == Some(id) && !positive {
        return Err("inductive occurs in a non-strictly-positive position".into());
    }
    if let Some(product) = structure::product(&env.arena, e) {
        check_positive(env, product.domain, id, false)?;
        return check_positive(env, product.body, id, positive);
    }
    let positive = positive
        && !inductive.is_some_and(|other| other != id)
        && structure::application(&env.arena, e).is_none();
    let mut result = Ok(());
    structure::visit_children(&env.arena, e, |child, _| {
        if result.is_ok() {
            result = check_positive(env, child, id, positive);
        }
    });
    result
}
fn check_program_positive(
    env: &Environment,
    e: Expression,
    id: ProgramInductiveId,
    positive: bool,
) -> Result<(), String> {
    let e = super::calculus::normalize(env, e)?;
    let inductive = structure::program_inductive(&env.arena, e).map(|(id, _)| id);
    if inductive == Some(id) && !positive {
        return Err("Program datatype occurs in a non-strictly-positive position".into());
    }
    if let Some(product) = structure::product(&env.arena, e) {
        check_program_positive(env, product.domain, id, false)?;
        return check_program_positive(env, product.body, id, positive);
    }
    let positive = positive
        && !inductive.is_some_and(|other| other != id)
        && structure::application(&env.arena, e).is_none();
    let mut result = Ok(());
    structure::visit_children(&env.arena, e, |child, _| {
        if result.is_ok() {
            result = check_program_positive(env, child, id, positive);
        }
    });
    result
}
fn contains_inductive(env: &Environment, e: Expression, id: InductiveId) -> bool {
    let mut found = structure::inductive_id(&env.arena, e) == Some(id);
    structure::visit_children(&env.arena, e, |child, _| {
        found = found || contains_inductive(env, child, id);
    });
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
                let domain = super::reflection::reflect(self, (*ty).into())?;
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
