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
        if let Some(captures) = self.capture_cache.get(&declaration) {
            return captures.clone();
        }
        let captures = self.collect_captures(vec![declaration]);
        let result = self.order_captures(captures);
        self.capture_cache.insert(declaration, result.clone());
        result
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
            if let Some(cached) = self.capture_cache.get(&dependency) {
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
            let classifier =
                self.in_scope(captures[..position].to_vec(), 0, 0, |this| match p.kind {
                    ModuleParameterKind::Pts { ty } => this.set(ty, &mut vec![], id.module),
                    ModuleParameterKind::ProgramType => {
                        if program {
                            Ok(this
                                .kernel
                                .arena()
                                .alloc(s::ValueKindNode {
                                    level: 0,
                                    form: s::ValueKindForm::Base,
                                })
                                .into())
                        } else {
                            this.logical_base_kind(k::BaseSort::Set(0))
                        }
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        if program {
                            Ok(this.value_type(ty)?.into())
                        } else {
                            let ty = raw::reflection::reflect_value_type(this.raw, ty)
                                .map_err(|e| e.to_string())?;
                            this.set(ty, &mut vec![], id.module)
                        }
                    }
                })?;
            result.push(ke::Binding {
                var: p.name,
                classifier,
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
                let index = self.parameter_index(id, depth)?;
                let kind = self.raw.module_parameter_opt(id).unwrap().kind;
                let (sort, stage) = match kind {
                    ModuleParameterKind::Pts { ty } => {
                        let sort = self.formation(ty, &mut vec![])?;
                        (
                            sort.base(),
                            if sort.is_upper() {
                                s::Stage::Type
                            } else {
                                s::Stage::Term
                            },
                        )
                    }
                    ModuleParameterKind::ProgramType => (
                        if program {
                            k::BaseSort::Value(0)
                        } else {
                            k::BaseSort::Set(0)
                        },
                        s::Stage::Type,
                    ),
                    ModuleParameterKind::ProgramValue { .. } => (
                        if program {
                            k::BaseSort::Value(0)
                        } else {
                            k::BaseSort::Set(0)
                        },
                        s::Stage::Term,
                    ),
                };
                kernel::construction::bound(self.kernel.arena(), sort, stage, index)
            })
            .collect()
    }

    pub(super) fn definition_expression(
        &mut self,
        id: DefId,
        depth: usize,
        program: bool,
    ) -> Result<s::Expression, String> {
        self.definition(id)?;
        let captures = self.captures(Declaration::Definition(id));
        let arguments = self.capture_arguments(&captures, depth, program)?;
        let definition = self
            .kernel
            .definition(id.into())
            .ok_or("unknown definition")?;
        let expression =
            self.kernel
                .arena()
                .identified(id.into(), definition.body, definition.classifier)?;
        kernel::calculus::instantiate_telescope(self.kernel, expression, &arguments)
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
}
