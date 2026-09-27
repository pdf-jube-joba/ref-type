//! Close declarations over their free frontend parameters before kernel checking.
use super::*;
use raw::environment::{DefinedConstant, ModuleParameterKind};
use raw::traversal::Term;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Declaration {
    Definition(DefId),
    Inductive(InductiveId),
    Datatype(ProgramInductiveId),
    Parameter(ModuleParamId),
}

impl Lowerer<'_> {
    fn roots(&self, declaration: Declaration) -> Vec<Term> {
        match declaration {
            Declaration::Definition(id) => definition_roots(self.raw.definition(id)),
            Declaration::Parameter(id) => match self.raw.module_parameter_opt(id).unwrap().kind {
                ModuleParameterKind::Pts { ty } => vec![Term::Logical(ty)],
                ModuleParameterKind::ProgramType => vec![],
                ModuleParameterKind::ProgramValue { ty } => vec![Term::ValueType(ty)],
            },
            Declaration::Inductive(id) => {
                let spec = self.raw.inductive(id);
                let mut roots: Vec<_> = spec
                    .parameters()
                    .iter()
                    .map(|(_, ty)| Term::Logical(*ty))
                    .collect();
                roots.push(Term::Logical(spec.arity(self.raw.arena())));
                let this = self.raw.arena().alloc(ExpNode::IndType {
                    indspec: id,
                    parameters: (0..spec.parameters().len())
                        .rev()
                        .map(|i| self.raw.arena().exp_bound(i))
                        .collect(),
                });
                roots.extend(
                    spec.constructors()
                        .iter()
                        .map(|c| Term::Logical(c.as_exp_with_type(self.raw.arena(), this))),
                );
                roots
            }
            Declaration::Datatype(id) => self
                .raw
                .program_inductive(id)
                .constructors()
                .iter()
                .flat_map(|c| c.fields().iter().map(|(_, ty)| Term::ValueType(*ty)))
                .collect(),
        }
    }

    pub(super) fn definition_dependencies(&self, id: DefId) -> Vec<DefId> {
        let mut definitions: Vec<_> = self
            .dependencies(self.roots(Declaration::Definition(id)))
            .into_iter()
            .filter_map(|d| match d {
                Declaration::Definition(id) => Some(id),
                _ => None,
            })
            .collect();
        definitions.sort_by_key(|id| (id.module.0, id.index));
        definitions
    }

    pub(super) fn captures(&mut self, declaration: Declaration) -> Vec<ModuleParamId> {
        if let Some(captures) = self.registered_captures(declaration) {
            return captures;
        }
        if let Some(captures) = self.capture_cache.get(&declaration) {
            return captures.clone();
        }
        let captures = self.collect_captures(vec![declaration]);
        let result = self.order_captures(captures);
        self.capture_cache.insert(declaration, result.clone());
        result
    }

    fn registered_captures(&self, declaration: Declaration) -> Option<Vec<ModuleParamId>> {
        let Declaration::Definition(id) = declaration else {
            return None;
        };
        let native = self.raw.kernel_definitions.borrow().get(&id).copied()?;
        self.kernel.definition(native).ok()?;
        self.raw.arena().definition_captures(native)
    }

    fn collect_captures(&self, declarations: Vec<Declaration>) -> HashSet<ModuleParamId> {
        let mut captures = HashSet::new();
        let mut visited = HashSet::new();
        let mut pending = declarations;
        while let Some(dependency) = pending.pop() {
            if !visited.insert(dependency) {
                continue;
            }
            if let Declaration::Parameter(id) = dependency {
                captures.insert(id);
            }
            if let Some(cached) = self.registered_captures(dependency) {
                captures.extend(cached);
            } else if let Some(cached) = self.capture_cache.get(&dependency) {
                captures.extend(cached);
            } else {
                pending.extend(self.dependencies(self.roots(dependency)));
            }
        }
        captures
    }

    fn order_captures(&self, mut captures: HashSet<ModuleParamId>) -> Vec<ModuleParamId> {
        // Parameter classifiers precede the bindings which depend on them, even
        // when specialization has allocated modules in a different order.
        fn order(
            this: &Lowerer<'_>,
            id: ModuleParamId,
            remaining: &mut HashSet<ModuleParamId>,
            result: &mut Vec<ModuleParamId>,
        ) {
            if !remaining.remove(&id) {
                return;
            }
            let mut dependencies: Vec<_> = this
                .collect_captures(
                    this.dependencies(this.roots(Declaration::Parameter(id)))
                        .into_iter()
                        .collect(),
                )
                .into_iter()
                .collect();
            dependencies.sort_by_key(|p| (p.module.0, p.position));
            for dependency in dependencies {
                order(this, dependency, remaining, result);
            }
            result.push(id);
        }
        let mut ids: Vec<_> = captures.iter().copied().collect();
        ids.sort_by_key(|p| (p.module.0, p.position));
        let mut result = vec![];
        for id in ids {
            order(self, id, &mut captures, &mut result);
        }
        result
    }

    fn dependencies(&self, mut pending: Vec<Term>) -> HashSet<Declaration> {
        use raw::program::{ComputationTermNode as C, ValueTermNode as V, ValueTypeNode as VT};
        let mut seen = HashSet::new();
        let mut dependencies = HashSet::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            let dependency = match term {
                Term::Logical(e) => match self.raw.arena().get(e) {
                    ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => {
                        Some(Declaration::Parameter(id))
                    }
                    ExpNode::DefinedConstant(id) => Some(Declaration::Definition(id)),
                    ExpNode::IndType { indspec, .. }
                    | ExpNode::IndCtor { indspec, .. }
                    | ExpNode::IndElim { indspec, .. }
                    | ExpNode::IndCase { indspec, .. } => Some(Declaration::Inductive(indspec)),
                    ExpNode::ReflectedProgramCase { indspec, .. } => {
                        Some(Declaration::Datatype(indspec))
                    }
                    _ => None,
                },
                Term::ValueType(e) => match self.raw.arena().get(e) {
                    VT::ModuleParam(id) => Some(Declaration::Parameter(id)),
                    VT::Inductive { indspec, .. } => Some(Declaration::Datatype(indspec)),
                    _ => None,
                },
                Term::Value(e) => match self.raw.arena().get(e) {
                    V::ModuleParam(id) => Some(Declaration::Parameter(id)),
                    V::DefinedConstant(id) | V::DefinitionInstance { definition: id, .. } => {
                        Some(Declaration::Definition(id))
                    }
                    V::InductiveConstructor { indspec, .. } => Some(Declaration::Datatype(indspec)),
                    _ => None,
                },
                Term::Computation(e) => match self.raw.arena().get(e) {
                    C::DefinedConstant(id) | C::DefinitionInstance { definition: id, .. } => {
                        Some(Declaration::Definition(id))
                    }
                    C::Case { indspec, .. } => Some(Declaration::Datatype(indspec)),
                    _ => None,
                },
                Term::ComputationType(_) => None,
            };
            dependencies.extend(dependency);
            term.visit_children(self.raw.arena(), |child, _| pending.push(child));
        }
        dependencies
    }

    pub(super) fn in_scope<T>(
        &mut self,
        captures: Vec<ModuleParamId>,
        logical_base: usize,
        program_depth: usize,
        f: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let previous = std::mem::replace(
            &mut self.scope,
            Scope {
                captures,
                logical_base,
                program_depth,
                program_context: false,
                proof_base: None,
                nominal: false,
            },
        );
        let cache = std::mem::take(&mut self.cache);
        let result = f(self);
        self.scope = previous;
        self.cache = cache;
        result
    }

    pub(super) fn parameter_index(&self, id: ModuleParamId, depth: usize) -> Result<usize, String> {
        let position = self
            .scope
            .captures
            .iter()
            .position(|p| *p == id)
            .ok_or_else(|| format!("uncaptured parameter {id:?}"))?;
        Ok(depth + self.scope.captures.len() - position - 1)
    }

    pub(super) fn capture_context(&mut self, program: bool) -> Result<ke::Context, String> {
        let captures = self.scope.captures.clone();
        let mut result = vec![];
        for (position, id) in captures.iter().copied().enumerate() {
            let p = self.raw.module_parameter_opt(id).unwrap().clone();
            let classifier = self.in_scope(captures[..position].to_vec(), 0, 0, |this| {
                this.scope.program_context = program;
                match p.kind {
                    ModuleParameterKind::Pts { ty } => this.set(ty, &mut vec![], id.module),
                    ModuleParameterKind::ProgramType => {
                        if program {
                            Ok(this
                                .kernel
                                .arena()
                                .sort(k::Sort::Base(k::BaseSort::Value(0))))
                        } else {
                            this.logical_base_kind(k::BaseSort::Set(0))
                        }
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        if program {
                            Ok(this.value_type(ty)?)
                        } else {
                            let ty = raw::reflection::reflect_value_type(this.raw, ty)
                                .map_err(|e| e.to_string())?;
                            this.set(ty, &mut vec![], id.module)
                        }
                    }
                }
            })?;
            result.push(ke::Binding {
                var: p.name,
                ty: classifier,
            });
        }
        Ok(result)
    }

    pub(super) fn capture_arguments(
        &mut self,
        captures: &[ModuleParamId],
        depth: usize,
        program: bool,
    ) -> Result<Vec<s::Expression>, String> {
        captures
            .iter()
            .map(|&id| {
                if self.scope.nominal {
                    let e = self.nominal_parameter(id)?;
                    let program_parameter = !matches!(
                        self.raw.module_parameter_opt(id).unwrap().kind,
                        ModuleParameterKind::Pts { .. }
                    );
                    return Ok(if !program && program_parameter {
                        self.kernel.arena().alloc(s::Node::Reflect { term: e })
                    } else {
                        e
                    });
                }
                let index = self.parameter_index(id, depth)?;
                let bound = self.kernel.arena().bound(index);
                let reflects = !program
                    && self.scope.program_context
                    && !matches!(
                        self.raw.module_parameter_opt(id).unwrap().kind,
                        ModuleParameterKind::Pts { .. }
                    );
                Ok(if reflects {
                    self.kernel.arena().alloc(s::Node::Reflect { term: bound })
                } else {
                    bound
                })
            })
            .collect()
    }

    pub(super) fn definition_ambient(&mut self, id: DefId) -> Result<usize, String> {
        if let Some(native) = self.raw.kernel_definitions.borrow().get(&id).copied()
            && let Ok(definition) = self.kernel.definition(native)
            && let Some(captures) = self.raw.arena().definition_captures(native)
        {
            let explicit = match self.raw.definition(id) {
                DefinedConstant::Alias { parameters, .. } => parameters.len(),
                _ => self.raw.definition_parameters(id).len(),
            };
            return Ok(definition.context.len() - captures.len() - explicit);
        }
        let parameters = self.raw.definition_parameters(id).len();
        let own = definition_roots(self.raw.definition(id))
            .into_iter()
            .any(|root| {
                self.raw
                    .arena()
                    .max_loose_bound(root)
                    .is_some_and(|i| i >= parameters)
            });
        let dependencies = self.definition_dependencies(id);
        let mut open = own;
        for dependency in dependencies {
            let native = self
                .raw
                .kernel_definitions
                .borrow()
                .get(&dependency)
                .copied();
            if let Some(native) = native {
                let captures = self.captures(Declaration::Definition(dependency)).len();
                open |= self.kernel.definition(native)?.context.len()
                    > captures + self.raw.definition_parameters(dependency).len();
            }
        }
        Ok(if open {
            self.raw.definition_context(id.module).len()
        } else {
            0
        })
    }

    pub(super) fn definition_expression(
        &mut self,
        id: DefId,
        depth: usize,
        program: bool,
    ) -> Result<s::Expression, String> {
        self.definition(id)?;
        let captures = self.captures(Declaration::Definition(id));
        let mut arguments = self.capture_arguments(&captures, depth, program)?;
        let ambient = self.definition_ambient(id)?;
        if ambient > depth {
            return Err("definition local context is outside reference scope".into());
        }
        arguments.extend(
            (depth - ambient..depth)
                .rev()
                .map(|i| self.kernel.arena().bound(i)),
        );
        let kernel_id = self
            .raw
            .kernel_definitions
            .borrow()
            .get(&id)
            .copied()
            .ok_or("unknown definition")?;
        self.kernel.reference(kernel_id, arguments)
    }

    pub(crate) fn prepare_query(&mut self, roots: Vec<Term>) {
        let mut captures = HashSet::new();
        for dependency in self.dependencies(roots) {
            captures.extend(self.captures(dependency));
        }
        self.scope.captures = self.order_captures(captures);
    }
}

pub(super) fn definition_roots(definition: &DefinedConstant) -> Vec<Term> {
    match *definition {
        DefinedConstant::Alias {
            ref parameters,
            ty,
            body,
        } => {
            let mut roots = vec![Term::Logical(ty), Term::Logical(body)];
            roots.extend(parameters.iter().map(|(_, ty)| Term::Logical(*ty)));
            roots
        }
        DefinedConstant::Pts { ty, body } => vec![Term::Logical(ty), Term::Logical(body)],
        DefinedConstant::ProgramValue { ty, body } => vec![Term::ValueType(ty), Term::Value(body)],
        DefinedConstant::ProgramComputation { ty, body } => {
            vec![Term::ComputationType(ty), Term::Computation(body)]
        }
    }
}

#[derive(Default)]
pub(super) struct Scope {
    pub captures: Vec<ModuleParamId>,
    pub logical_base: usize,
    pub program_depth: usize,
    pub program_context: bool,
    pub proof_base: Option<usize>,
    pub nominal: bool,
}
