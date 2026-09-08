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
        if self.definitions.contains_key(&id) {
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
                    let data = self.arena.data(head);
                    if matches!(data.op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
                        check_positive(self, data.child(0), id, true)?;
                        tail = data.child(1);
                    } else {
                        let mut head = head;
                        while matches!(
                            self.arena.data(head).op,
                            Op::AppTerm { .. } | Op::AppType { .. }
                        ) {
                            head = self.arena.data(head).child(0)
                        }
                        if !matches!(self.arena.data(head).op,Op::IndType{inductive} if inductive==id)
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
    let d = env.arena.data(e);
    if matches!(d.op,Op::IndType{inductive} if inductive==id) && !positive {
        return Err("inductive occurs in a non-strictly-positive position".into());
    }
    for (i, field) in d.fields.iter().enumerate() {
        for c in field {
            let unknown_variance = matches!(d.op,Op::IndType{inductive:other} if other!=id)
                || matches!(d.op, Op::AppTerm { .. } | Op::AppType { .. });
            let positive = positive
                && !unknown_variance
                && !(i == 0 && matches!(d.op, Op::ProdTerm { .. } | Op::ProdType { .. }));
            check_positive(env, c.expression, id, positive)?;
        }
    }
    Ok(())
}

fn check_program_positive(
    env: &Environment,
    e: Expression,
    id: ProgramInductiveId,
    positive: bool,
) -> Result<(), String> {
    let e = super::calculus::normalize(env, e)?;
    let d = env.arena.data(e);
    if matches!(d.op,Op::Inductive{inductive} if inductive==id) && !positive {
        return Err("Program datatype occurs in a non-strictly-positive position".into());
    }
    for (i, field) in d.fields.iter().enumerate() {
        for c in field {
            check_program_positive(
                env,
                c.expression,
                id,
                positive
                    && !matches!(d.op,Op::Inductive{inductive:other} if other!=id)
                    && !matches!(d.op, Op::AppType { .. })
                    && !(i == 0 && matches!(d.op, Op::ProdTerm { .. } | Op::ProdType { .. })),
            )?
        }
    }
    Ok(())
}

fn contains_inductive(env: &Environment, e: Expression, id: InductiveId) -> bool {
    let d = env.arena.data(e);
    matches!(d.op,Op::IndType{inductive}|Op::IndCtor{inductive,..}|Op::IndElim{inductive,..} if inductive==id)
        || d.fields
            .iter()
            .flatten()
            .any(|c| contains_inductive(env, c.expression, id))
}

impl Environment {
    pub(crate) fn singleton_elimination(&self, id: InductiveId) -> bool {
        let Some(spec) = self.inductive(id) else {
            return false;
        };
        if spec.constructors.len() != 1 || self.arena.data(spec.arity).op != Op::Base {
            return false;
        }
        let mut ty = spec.constructors[0];
        loop {
            let d = self.arena.data(ty);
            if matches!(d.op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
                if contains_inductive(self, d.child(0), id) {
                    return false;
                }
                ty = d.child(1)
            } else {
                return true;
            }
        }
    }

    fn install_datatype_mirror(&mut self, spec: &ProgramDatatype) -> Result<(), String> {
        use super::calculus::{alpha_equal, node, shift};
        let sort = BaseSort::Set(spec.level);
        let parameters = super::reflection::reflect_context(self, &spec.parameters)?;
        let arity = node(&self.arena, Family::SetKind, sort, Op::Base, &[]);
        let arguments: Vec<_> = parameters
            .iter()
            .enumerate()
            .map(|(i, p)| {
                node(
                    &self.arena,
                    Family::SetType,
                    self.arena.sort(p.classifier),
                    Op::Bound {
                        index: parameters.len() - i - 1,
                    },
                    &[],
                )
            })
            .collect();
        let mut constructors = vec![];
        for fields in &spec.constructors {
            let result = self.arena.store(
                Family::SetType,
                Data {
                    sort,
                    op: Op::IndType {
                        inductive: spec.reflected,
                    },
                    fields: vec![
                        arguments
                            .iter()
                            .map(|&expression| Child {
                                expression,
                                depth: 0,
                            })
                            .collect(),
                    ],
                },
            );
            let mut body = shift(&self.arena, result, fields.len(), 0)?;
            for (i, (var, ty)) in fields.iter().enumerate().rev() {
                let domain = super::reflection::reflect(self, (*ty).into())?;
                let domain = shift(&self.arena, domain, i, 0)?;
                let rule = ProductRule::new(Sort::Base(self.arena.sort(domain)), Sort::Base(sort))?;
                body = node(
                    &self.arena,
                    Family::SetType,
                    sort,
                    Op::ProdTerm { rule, var: *var },
                    &[(domain, 0), (body, 1)],
                );
            }
            constructors.push(body)
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
