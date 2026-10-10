//! Front-only provenance for substitution-specialized nominal declarations.
//!
//! Namespace aliases do not confer identity. Only the original declaration and
//! its arguments do; conversion in the kernel still compares ordinary type IDs.
use super::{environment::*, exp::Exp, ids::*, program::*};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) struct Specialization<I> {
    pub source: I,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
}

// A namespace import updates declaration remappings as each declaration is
// canonicalized. Cache only when every global reference in the argument still
// has the same image, and the complete parameter substitution is unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Reference {
    Definition(DefId),
    Inductive(InductiveId),
    ProgramInductive(ProgramInductiveId),
}

#[derive(Default, Debug)]
pub(crate) struct SubstitutionCache {
    references: rustc_hash::FxHashMap<Exp, Vec<Reference>>,
    results: rustc_hash::FxHashMap<Exp, (Vec<Reference>, Vec<(ModuleParamId, Exp)>, Exp)>,
}

// Thousands of declarations in an import share one argument telescope.
// Intern it once so conversion results can be reused across declarations.
#[derive(Default, Debug)]
pub(crate) struct ArgumentCache {
    sets: rustc_hash::FxHashMap<Vec<(ModuleParamId, ModuleArgument)>, usize>,
    comparisons: rustc_hash::FxHashMap<(usize, usize), bool>,
    shareability: rustc_hash::FxHashMap<usize, bool>,
}

impl ArgumentCache {
    pub(crate) fn intern(&mut self, arguments: &[(ModuleParamId, ModuleArgument)]) -> usize {
        if let Some(&id) = self.sets.get(arguments) {
            return id;
        }
        let id = self.sets.len();
        self.sets.insert(arguments.to_vec(), id);
        id
    }
}

impl CrateEnv {
    fn namespace_syntax_equal(&self, left: Exp, right: Exp) -> bool {
        use super::exp::ExpNode;
        fn compare(
            env: &CrateEnv,
            left: Exp,
            right: Exp,
            seen: &mut rustc_hash::FxHashSet<(Exp, Exp)>,
        ) -> bool {
            if left == right || !seen.insert((left, right)) {
                return true;
            }
            let declarations = match (env.arena().get(left), env.arena().get(right)) {
                (ExpNode::DefinedConstant(l), ExpNode::DefinedConstant(r)) => Some((l, r)),
                (
                    ExpNode::DefinitionInstance { definition: l, .. },
                    ExpNode::DefinitionInstance { definition: r, .. },
                ) => Some((l, r)),
                _ => None,
            };
            // Matching closed declarations can be compared by provenance and
            // arguments before expanding their bodies. Large structure aliases
            // otherwise unfold the same signature for every imported item.
            let matching_source = declarations.is_some_and(|(l, r)| {
                !env.namespace_has_local_context(l.module)
                    && !env.namespace_has_local_context(r.module)
                    && env.definition_specialization_source(l)
                        == env.definition_specialization_source(r)
            });
            if !matching_source {
                let left_head = env.namespace_alias_head(left);
                let right_head = env.namespace_alias_head(right);
                if left_head != left || right_head != right {
                    return compare(env, left_head, right_head, seen);
                }
            }
            if let Some((l, r)) = declarations {
                // A closed declaration's identity is its source plus its
                // specialization arguments. Ambient local contexts require the
                // ordinary conversion path, which explicitly applies captures.
                if env.namespace_has_local_context(l.module)
                    || env.namespace_has_local_context(r.module)
                    || env.definition_specialization_source(l)
                        != env.definition_specialization_source(r)
                {
                    return false;
                }
                let left_args = env.definition_specialization_arguments(l);
                let right_args = env.definition_specialization_arguments(r);
                let source = env.definition_specialization_source(l);
                if (left_args.is_empty() || right_args.is_empty())
                    && !env.namespace_arguments(source.module).is_empty()
                {
                    return false;
                }
                if left_args.len() != right_args.len()
                    || !left_args.iter().zip(&right_args).all(|((lp, l), (rp, r))| {
                        lp == rp
                            && match (*l, *r) {
                                (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                                    compare(env, l, r, seen)
                                }
                                _ => l == r,
                            }
                    })
                {
                    return false;
                }
            } else if kernel::calculus::skeleton(&env.arena().core, left.0)
                != kernel::calculus::skeleton(&env.arena().core, right.0)
            {
                return false;
            }
            let left = kernel::calculus::comparison_children(&env.arena().core, left.0);
            let right = kernel::calculus::comparison_children(&env.arena().core, right.0);
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|((l, ld), (r, rd))| ld == rd && compare(env, Exp(l), Exp(r), seen))
        }
        compare(self, left, right, &mut rustc_hash::FxHashSet::default())
    }

    fn namespace_alias_head(&self, term: Exp) -> Exp {
        use super::exp::ExpNode;
        fn head(env: &CrateEnv, mut term: Exp, fuel: &mut usize) -> Exp {
            // This only visits already materialized, closed definitions. The
            // shared budget also bounds beta reduction in application spines.
            while *fuel > 0 {
                *fuel -= 1;
                match env.arena().get(term) {
                    ExpNode::Ascribe { term: value, .. } => term = value,
                    ExpNode::App { func, arg } => {
                        let function = head(env, func, fuel);
                        if let ExpNode::Lam { body, .. } = env.arena().get(function)
                            && let Ok(body) =
                                kernel::calculus::instantiate(&env.arena().core, body.0, &[arg.0])
                        {
                            term = Exp(body);
                        } else {
                            return if function == func {
                                term
                            } else {
                                env.arena().alloc(ExpNode::App {
                                    func: function,
                                    arg,
                                })
                            };
                        }
                    }
                    ExpNode::DefinedConstant(id) => {
                        if env.namespace_has_local_context(id.module)
                            || !env.definition_parameters(id).is_empty()
                            || matches!(env.arena().core.get(term.0), kernel::syntax::Node::Definition { arguments, .. } if !arguments.is_empty())
                        {
                            break;
                        }
                        let Some(DefinedConstant::Pts { body, .. }) =
                            env.materialized_definition(id)
                        else {
                            break;
                        };
                        let body = *body;
                        if env.arena().core.max_loose_bound(body.0).is_some() || body == term {
                            break;
                        }
                        term = body;
                    }
                    _ => break,
                }
            }
            term
        }
        head(self, term, &mut 32)
    }

    pub(crate) fn namespace_terms_equal(&self, left: Exp, right: Exp) -> bool {
        let _cost = timing::costs::Scope::enter("namespace.compare-term");
        if left == right {
            return true;
        }
        if let Some(&equal) = self.namespace_conversion_cache.borrow().get(&(left, right)) {
            return equal;
        }
        use super::exp::ExpNode;
        // Distinct variables and opaque parameters cannot become equal as
        // imported definitions are materialized. Check these rigid leaves
        // before recursively comparing syntax or expanding aliases.
        if matches!(
            (self.arena().get(left), self.arena().get(right)),
            (ExpNode::Bound(_), ExpNode::Bound(_))
                | (ExpNode::Bound(_), ExpNode::ModuleParam(_))
                | (ExpNode::ModuleParam(_), ExpNode::Bound(_))
                | (ExpNode::ModuleParam(_), ExpNode::ModuleParam(_))
        ) {
            self.cache_namespace_equality(left, right, false);
            return false;
        }
        // The source and kernel share an expression arena. Binder renaming is
        // already decidable on that syntax; it does not require materializing
        // the declarations mentioned by a namespace argument.
        if kernel::calculus::alpha_equal(&self.arena().core, left.0, right.0)
            || self.namespace_syntax_equal(left, right)
        {
            self.cache_namespace_equality(left, right, true);
            return true;
        }
        let left_alias = self.namespace_alias_head(left);
        let right_alias = self.namespace_alias_head(right);
        if (left_alias != left || right_alias != right)
            && self.namespace_syntax_equal(left_alias, right_alias)
        {
            self.cache_namespace_equality(left, right, true);
            return true;
        }
        // These heads are rigid: neither a local variable nor an opaque module
        // parameter reduces to another variable. Avoid registering an entire
        // captured declaration graph merely to reject this comparison.
        match (self.arena().get(left_alias), self.arena().get(right_alias)) {
            (ExpNode::Bound(_), ExpNode::Bound(_))
            | (ExpNode::Bound(_), ExpNode::ModuleParam(_))
            | (ExpNode::ModuleParam(_), ExpNode::Bound(_))
            | (ExpNode::ModuleParam(_), ExpNode::ModuleParam(_)) => {
                self.cache_namespace_equality(left, right, false);
                return false;
            }
            _ => {}
        }
        let Some(equal) = crate::kernel_bridge::resolved_convertible(self, left, right) else {
            return false;
        };
        self.cache_namespace_equality(left, right, equal);
        equal
    }

    fn cache_namespace_equality(&self, left: Exp, right: Exp, equal: bool) {
        let mut cache = self.namespace_conversion_cache.borrow_mut();
        cache.insert((left, right), equal);
        cache.insert((right, left), equal);
    }

    pub(crate) fn namespace_arguments(
        &self,
        module: ModuleId,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        let _cost = timing::costs::Scope::enter("namespace.collect-arguments");
        let mut ancestors = Vec::new();
        let mut current = Some(module);
        while let Some(id) = current {
            ancestors.push(id);
            current = self.module(id).parent();
        }
        ancestors.reverse();
        ancestors
            .into_iter()
            .flat_map(|module| {
                self.module(module).parameters().iter().enumerate().map(
                    move |(position, parameter)| {
                        let id = ModuleParamId {
                            module,
                            position: position as u32,
                        };
                        let argument = match parameter.kind {
                            ModuleParameterKind::Pts { .. } => {
                                ModuleArgument::Pts(self.arena().exp_module_param(id))
                            }
                            ModuleParameterKind::ProgramType => ModuleArgument::ProgramType(
                                self.arena().alloc(ValueTypeNode::ModuleParam(id)),
                            ),
                            ModuleParameterKind::ProgramValue { .. } => {
                                ModuleArgument::ProgramValue(
                                    self.arena().alloc(ValueTermNode::ModuleParam(id)),
                                )
                            }
                        };
                        (id, argument)
                    },
                )
            })
            .collect()
    }

    pub(crate) fn substitute_namespace_arguments(
        &self,
        arguments: &[(ModuleParamId, ModuleArgument)],
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        let _cost = timing::costs::Scope::enter("namespace.substitute-arguments");
        arguments
            .iter()
            .map(|(id, argument)| {
                // Remap the source graph first. Inserted caller arguments must not
                // themselves be remapped or substituted a second time.
                let argument = match *argument {
                    ModuleArgument::Pts(e) => ModuleArgument::Pts(
                        self.substitute_namespace_expression(e, reflected, remapping),
                    ),
                    ModuleArgument::ProgramType(t) => ModuleArgument::ProgramType(
                        crate::raw::remapping::subst_value_type_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_value_type_global_ids(
                                self.arena(),
                                t,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                            ),
                            substitutions,
                        ),
                    ),
                    ModuleArgument::ProgramValue(v) => ModuleArgument::ProgramValue(
                        crate::raw::remapping::subst_value_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_value_global_ids(
                                self.arena(),
                                v,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                                &remapping.inductive_ids,
                            ),
                            substitutions,
                            reflected,
                        ),
                    ),
                };
                (*id, argument)
            })
            .collect()
    }

    fn substitute_namespace_expression(
        &self,
        expression: Exp,
        reflected: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> Exp {
        use super::exp::ExpNode;
        use super::traversal::{Memoized, Term};
        let mut cache = self.namespace_substitution_cache.borrow_mut();
        let references = cache.references.entry(expression).or_insert_with(|| {
            let mut references = rustc_hash::FxHashSet::default();
            Term::Logical(expression).walk(
                self.arena(),
                0,
                &mut Memoized::new(|term: Term, _: usize| {
                    let reference = match term {
                        Term::Logical(e) => match self.arena().get(e) {
                            ExpNode::DefinedConstant(id)
                            | ExpNode::DefinitionInstance { definition: id, .. } => {
                                Some(Reference::Definition(id))
                            }
                            ExpNode::IndType { indspec, .. }
                            | ExpNode::IndCtor { indspec, .. }
                            | ExpNode::IndElim { indspec, .. }
                            | ExpNode::IndCase { indspec, .. } => {
                                Some(Reference::Inductive(indspec))
                            }
                            ExpNode::ReflectedProgramCase { indspec, .. } => {
                                Some(Reference::ProgramInductive(indspec))
                            }
                            _ => None,
                        },
                        Term::ValueType(t) => match self.arena().get(t) {
                            ValueTypeNode::Inductive { indspec, .. } => {
                                Some(Reference::ProgramInductive(indspec))
                            }
                            _ => None,
                        },
                        Term::Value(v) => match self.arena().get(v) {
                            ValueTermNode::DefinedConstant(id)
                            | ValueTermNode::DefinitionInstance { definition: id, .. } => {
                                Some(Reference::Definition(id))
                            }
                            ValueTermNode::InductiveConstructor { indspec, .. } => {
                                Some(Reference::ProgramInductive(indspec))
                            }
                            _ => None,
                        },
                        Term::Computation(c) => match self.arena().get(c) {
                            ComputationTermNode::DefinedConstant(id)
                            | ComputationTermNode::DefinitionInstance { definition: id, .. } => {
                                Some(Reference::Definition(id))
                            }
                            ComputationTermNode::Case { indspec, .. } => {
                                Some(Reference::ProgramInductive(indspec))
                            }
                            _ => None,
                        },
                        Term::ComputationType(_) => None,
                    };
                    if let Some(reference) = reference {
                        references.insert(reference);
                    }
                    None
                }),
            );
            references.into_iter().collect()
        });
        let images: Vec<_> = references
            .iter()
            .map(|reference| match *reference {
                Reference::Definition(id) => {
                    Reference::Definition(remapping.definition_ids.get(&id).copied().unwrap_or(id))
                }
                Reference::Inductive(id) => {
                    Reference::Inductive(remapping.inductive_ids.get(&id).copied().unwrap_or(id))
                }
                Reference::ProgramInductive(id) => Reference::ProgramInductive(
                    remapping
                        .program_inductive_ids
                        .get(&id)
                        .copied()
                        .unwrap_or(id),
                ),
            })
            .collect();
        if let Some((old_images, old_reflected, result)) = cache.results.get(&expression)
            && *old_images == images
            && old_reflected == reflected
        {
            return *result;
        }
        let result = crate::raw::remapping::exp_subst_map(
            self.arena(),
            crate::raw::remapping::remap_all_global_ids(
                self.arena(),
                expression,
                &remapping.definition_ids,
                &remapping.inductive_ids,
                &remapping.program_inductive_ids,
            ),
            reflected,
        );
        cache
            .results
            .insert(expression, (images, reflected.to_vec(), result));
        result
    }

    /// Imports from local telescopes cannot share nominal IDs across scopes.
    pub(crate) fn namespace_arguments_shareable(
        &self,
        arguments: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        let _cost = timing::costs::Scope::enter("namespace.check-shareability");
        use super::traversal::Term;
        let key = self.namespace_argument_cache.borrow_mut().intern(arguments);
        if let Some(&shareable) = self
            .namespace_argument_cache
            .borrow()
            .shareability
            .get(&key)
        {
            return shareable;
        }
        let shareable = arguments.iter().all(|(_, arg)| {
            let term = match *arg {
                ModuleArgument::Pts(e) => Term::Logical(e),
                ModuleArgument::ProgramType(t) => Term::ValueType(t),
                ModuleArgument::ProgramValue(v) => Term::Value(v),
            };
            if self.arena().max_loose_bound(term).is_some() {
                return false;
            }
            let Term::Logical(expression) = term else {
                return true;
            };
            if let Some(&shareable) = self.namespace_shareability.borrow().get(&expression) {
                return shareable;
            }
            // A declaration reference may hide an ambient telescope even when
            // its argument syntax contains no loose variable. Such references
            // cannot be reused as closed namespace arguments in another scope.
            use super::exp::ExpNode;
            use super::traversal::Memoized;
            let mut shareable = true;
            let mut visitor = Memoized::new(|term: Term, _: usize| {
                if let Term::Logical(e) = term {
                    let module = match self.arena().get(e) {
                        ExpNode::DefinedConstant(id)
                        | ExpNode::DefinitionInstance { definition: id, .. } => Some(id.module),
                        ExpNode::IndType { indspec, .. }
                        | ExpNode::IndCtor { indspec, .. }
                        | ExpNode::IndElim { indspec, .. }
                        | ExpNode::IndCase { indspec, .. } => Some(indspec.module),
                        _ => None,
                    };
                    if let Some(module) = module {
                        shareable &= !self.namespace_has_local_context(module);
                    }
                }
                None
            });
            term.walk(self.arena(), 0, &mut visitor);
            self.namespace_shareability
                .borrow_mut()
                .insert(expression, shareable);
            shareable
        });
        self.namespace_argument_cache
            .borrow_mut()
            .shareability
            .insert(key, shareable);
        shareable
    }

    pub(crate) fn namespace_arguments_equal(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        if left == right {
            return true;
        }
        let key = {
            let mut cache = self.namespace_argument_cache.borrow_mut();
            let left = cache.intern(left);
            let right = cache.intern(right);
            (left.min(right), left.max(right))
        };
        if let Some(&equal) = self.namespace_argument_cache.borrow().comparisons.get(&key) {
            return equal;
        }
        let equal = left.len() == right.len()
            && left.iter().zip(right).all(|((lp, l), (rp, r))| {
                lp == rp
                    && match (*l, *r) {
                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                            self.namespace_terms_equal(l, r)
                        }
                        (ModuleArgument::ProgramType(l), ModuleArgument::ProgramType(r)) => {
                            crate::kernel_bridge::value_type_is_alpha_eq(self.arena(), l, r)
                        }
                        (ModuleArgument::ProgramValue(l), ModuleArgument::ProgramValue(r)) => {
                            l == r
                                || match (
                                    super::reflection::reflect_program(
                                        self,
                                        ProgramTerm::ValueTerm(l),
                                    ),
                                    super::reflection::reflect_program(
                                        self,
                                        ProgramTerm::ValueTerm(r),
                                    ),
                                ) {
                                    (Ok(l), Ok(r)) => self.namespace_terms_equal(l, r),
                                    _ => false,
                                }
                        }
                        _ => false,
                    }
            });
        // An unresolved kernel comparison may become decidable when a lazy
        // declaration is materialized. Retain failures only when a stable
        // mismatch was established by the ordinary term comparison.
        let stable = equal
            || left.len() != right.len()
            || left.iter().zip(right).any(|((lp, l), (rp, r))| {
                lp != rp
                    || match (*l, *r) {
                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                            self.namespace_conversion_cache.borrow().get(&(l, r)) == Some(&false)
                        }
                        (ModuleArgument::ProgramType(l), ModuleArgument::ProgramType(r)) => {
                            !crate::kernel_bridge::value_type_is_alpha_eq(self.arena(), l, r)
                        }
                        (ModuleArgument::ProgramValue(_), ModuleArgument::ProgramValue(_)) => false,
                        _ => true,
                    }
            });
        if stable {
            self.namespace_argument_cache
                .borrow_mut()
                .comparisons
                .insert(key, equal);
        }
        equal
    }

    /// Reject incompatible opaque parameters before comparing a shared prefix
    /// of large specialization arguments. Other heads, including aliases, may
    /// still convert and must go through the ordinary comparison.
    pub(crate) fn namespace_arguments_rigidly_differ(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        use super::exp::ExpNode;
        left.len() != right.len()
            || left.iter().zip(right).any(|((lp, l), (rp, r))| {
                if lp != rp {
                    return true;
                }
                let (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) = (*l, *r) else {
                    return false;
                };
                if l == r {
                    return false;
                }
                matches!(
                    (self.arena().get(l), self.arena().get(r)),
                    (ExpNode::ModuleParam(_), ExpNode::ModuleParam(_))
                        | (ExpNode::Bound(_), ExpNode::Bound(_))
                        | (ExpNode::ModuleParam(_), ExpNode::Bound(_))
                        | (ExpNode::Bound(_), ExpNode::ModuleParam(_))
                )
            })
    }
}

/// Determine identity before reserving another copy of an imported graph.
/// Following declaration provenance is essential: an argument can refer to a
/// definition whose own telescope contains a substituted parameter.
pub(crate) struct NamespaceStability<'a> {
    env: &'a CrateEnv,
    reflected: &'a [(ModuleParamId, Exp)],
    argument_sets: std::collections::HashMap<Vec<(ModuleParamId, ModuleArgument)>, bool>,
    definitions: std::collections::HashMap<DefId, bool>,
    inductives: std::collections::HashMap<InductiveId, bool>,
    datatypes: std::collections::HashMap<ProgramInductiveId, bool>,
}

impl<'a> NamespaceStability<'a> {
    pub(crate) fn new(env: &'a CrateEnv, reflected: &'a [(ModuleParamId, Exp)]) -> Self {
        Self {
            env,
            reflected,
            argument_sets: Default::default(),
            definitions: Default::default(),
            inductives: Default::default(),
            datatypes: Default::default(),
        }
    }

    fn definition(&mut self, id: DefId) -> bool {
        if let Some(&stable) = self.definitions.get(&id) {
            return stable;
        }
        self.definitions.insert(id, false);
        let stable = self.arguments(&self.env.definition_specialization_arguments(id));
        self.definitions.insert(id, stable);
        stable
    }

    fn inductive(&mut self, id: InductiveId) -> bool {
        if let Some(&stable) = self.inductives.get(&id) {
            return stable;
        }
        self.inductives.insert(id, false);
        let stable = self.arguments(&self.env.inductive_specialization_arguments(id));
        self.inductives.insert(id, stable);
        stable
    }

    fn datatype(&mut self, id: ProgramInductiveId) -> bool {
        if let Some(&stable) = self.datatypes.get(&id) {
            return stable;
        }
        self.datatypes.insert(id, false);
        let stable = self.arguments(&self.env.datatype_specialization_arguments(id));
        self.datatypes.insert(id, stable);
        stable
    }

    pub(crate) fn arguments(&mut self, arguments: &[(ModuleParamId, ModuleArgument)]) -> bool {
        use super::traversal::{Memoized, Term};
        if let Some(&stable) = self.argument_sets.get(arguments) {
            return stable;
        }
        if !self.env.namespace_arguments_shareable(arguments) {
            return false;
        }
        self.argument_sets.insert(arguments.to_vec(), false);
        let stable = arguments.iter().all(|(_, argument)| {
            // Program imports retain the existing materialization path.
            let ModuleArgument::Pts(expression) = *argument else {
                return false;
            };
            let arena = self.env.arena();
            let mut stable = true;
            let mut visitor = Memoized::new(|term: Term, _: usize| {
                if let Term::Logical(expression) = term {
                    use super::exp::ExpNode;
                    stable &= match arena.get(expression) {
                        ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => self
                            .reflected
                            .iter()
                            .find(|(p, _)| *p == id)
                            .is_none_or(|(_, value)| *value == expression),
                        ExpNode::DefinedConstant(id)
                        | ExpNode::DefinitionInstance { definition: id, .. } => self.definition(id),
                        ExpNode::IndType { indspec, .. }
                        | ExpNode::IndCtor { indspec, .. }
                        | ExpNode::IndElim { indspec, .. }
                        | ExpNode::IndCase { indspec, .. } => self.inductive(indspec),
                        ExpNode::ReflectedProgramCase { indspec, .. } => self.datatype(indspec),
                        ExpNode::Meta { .. }
                        | ExpNode::BoxType { .. }
                        | ExpNode::BoxProgram { .. }
                        | ExpNode::ForceBox { .. } => false,
                        _ => true,
                    };
                } else {
                    stable = false;
                }
                None
            });
            Term::Logical(expression).walk(arena, 0, &mut visitor);
            stable
        });
        self.argument_sets.insert(arguments.to_vec(), stable);
        stable
    }

    pub(crate) fn item(&mut self, item: &ModuleItem) -> bool {
        match item {
            ModuleItem::Definition { definition, .. } => self.definition(*definition),
            ModuleItem::Inductive {
                inductive,
                associated_definitions,
                ..
            }
            | ModuleItem::Record {
                inductive,
                associated_definitions,
                ..
            } => {
                self.inductive(*inductive)
                    && associated_definitions
                        .iter()
                        .all(|(_, id)| self.definition(*id))
            }
            ModuleItem::ProgramInductive { .. } => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::raw::exp::ExpNode;

    #[test]
    fn closed_arguments_reject_references_with_hidden_local_contexts() {
        use crate::raw::{exp::ExpContextEntry, sort::Sort};
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let context = vec![ExpContextEntry {
            var: SymbolId::ANONYMOUS,
            ty: env.arena().sort(Sort::Set(0)),
        }];
        let module = env.add_modules_in_scope(root, context, 1).unwrap()[0];
        let reference = env
            .arena()
            .alloc(ExpNode::DefinedConstant(DefId { module, index: 0 }));
        assert!(env.arena().core.max_loose_bound(reference.0).is_none());
        let parameter = ModuleParamId {
            module: root,
            position: 0,
        };
        let arguments = vec![(parameter, ModuleArgument::Pts(reference))];
        assert!(!env.namespace_arguments_shareable(&arguments));
        assert!(!env.namespace_arguments_shareable(&arguments));
        assert_eq!(
            env.namespace_shareability.borrow().get(&reference),
            Some(&false)
        );
    }

    #[test]
    fn closed_namespace_copies_compare_by_provenance_without_loading_bodies() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let source = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().sort(Sort::SetKind(0)),
                    body: env.arena().sort(Sort::Set(0)),
                },
            )
            .unwrap();
        let namespaces = env.add_modules_in_scope(root, vec![], 2).unwrap();
        let remapping = env.store_remapping(DeclarationRemapping::default());
        let mut copies = Vec::new();
        for namespace in namespaces {
            let copy = env.reserve_lazy_definition(namespace, source, vec![], vec![]);
            env.add_namespace_binding(
                root,
                root,
                namespace,
                vec![],
                std::collections::HashMap::from([(copy, source)]),
                remapping,
            );
            copies.push(env.arena().alloc(ExpNode::DefinedConstant(copy)));
        }
        let registered_before = env.kernel_definitions.borrow().len();
        assert_ne!(copies[0], copies[1]);
        assert!(env.namespace_terms_equal(copies[0], copies[1]));
        assert_eq!(env.kernel_definitions.borrow().len(), registered_before);
        let unrelated = env.arena().alloc(ExpNode::DefinedConstant(DefId {
            module: root,
            index: source.index + 1,
        }));
        assert!(!env.namespace_syntax_equal(copies[0], unrelated));
    }

    #[test]
    fn closed_alias_chains_reuse_syntax_without_kernel_registration() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let ty = env.arena().sort(Sort::SetKind(0));
        let source = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty,
                    body: env.arena().sort(Sort::Set(0)),
                },
            )
            .unwrap();
        let original = env.arena().alloc(ExpNode::DefinedConstant(source));
        let mut alias = original;
        for _ in 0..4 {
            let id = env
                .add_definition(root, DefinedConstant::Pts { ty, body: alias })
                .unwrap();
            alias = env.arena().alloc(ExpNode::DefinedConstant(id));
        }
        let registered = env.kernel_definitions.borrow().len();
        assert!(env.namespace_terms_equal(alias, original));
        assert!(env.namespace_syntax_equal(
            env.namespace_alias_head(alias),
            env.namespace_alias_head(original)
        ));
        assert_eq!(env.kernel_definitions.borrow().len(), registered);
    }

    #[test]
    fn alias_heads_leave_lazy_definitions_for_their_binding_scope() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let source = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().sort(Sort::SetKind(0)),
                    body: env.arena().sort(Sort::Set(0)),
                },
            )
            .unwrap();
        let lazy = env.reserve_lazy_definition(root, source, vec![], vec![]);
        let term = env.arena().alloc(ExpNode::DefinedConstant(lazy));
        assert!(env.materialized_definition(lazy).is_none());
        assert_eq!(env.namespace_alias_head(term), term);
        assert!(env.materialized_definition(lazy).is_none());
    }

    #[test]
    fn closed_aliases_to_parameters_compare_without_registering_definitions() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let ty = env.arena().sort(Sort::Set(0));
        for _ in 0..2 {
            env.add_module_parameter(
                root,
                ModuleParameter {
                    name: SymbolId::ANONYMOUS,
                    kind: ModuleParameterKind::Pts { ty },
                },
            );
        }
        let first = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 0,
        });
        let second = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 1,
        });
        let definition = env
            .add_definition(root, DefinedConstant::Pts { ty, body: first })
            .unwrap();
        let alias = env.arena().alloc(ExpNode::DefinedConstant(definition));
        let registered = env.kernel_definitions.borrow().len();
        let parameter = ModuleParamId {
            module: root,
            position: 0,
        };
        assert!(env.namespace_arguments_rigidly_differ(
            &[(parameter, ModuleArgument::Pts(first))],
            &[(parameter, ModuleArgument::Pts(second))]
        ));
        assert!(!env.namespace_arguments_rigidly_differ(
            &[(parameter, ModuleArgument::Pts(alias))],
            &[(parameter, ModuleArgument::Pts(first))]
        ));
        assert!(env.namespace_terms_equal(alias, first));
        assert!(!env.namespace_terms_equal(alias, second));
        assert_eq!(
            env.namespace_conversion_cache
                .borrow()
                .get(&(alias, second)),
            Some(&false)
        );
        assert!(!env.namespace_terms_equal(first, second));
        assert_eq!(
            env.namespace_conversion_cache
                .borrow()
                .get(&(first, second)),
            Some(&false)
        );
        assert!(env.namespace_terms_equal(alias, first));
        let left = [(parameter, ModuleArgument::Pts(alias))];
        let equal = [(parameter, ModuleArgument::Pts(first))];
        let different = [(parameter, ModuleArgument::Pts(second))];
        assert!(env.namespace_arguments_equal(&left, &equal));
        assert!(!env.namespace_arguments_equal(&left, &different));
        assert_eq!(env.namespace_argument_cache.borrow().comparisons.len(), 2);
        assert!(env.namespace_arguments_equal(&equal, &left));
        assert!(!env.namespace_arguments_equal(&different, &left));
        assert_eq!(env.kernel_definitions.borrow().len(), registered);
    }

    #[test]
    fn closed_lambda_alias_applications_compare_without_kernel_registration() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let ty = env.arena().sort(Sort::Set(0));
        for _ in 0..2 {
            env.add_module_parameter(
                root,
                ModuleParameter {
                    name: SymbolId::ANONYMOUS,
                    kind: ModuleParameterKind::Pts { ty },
                },
            );
        }
        let first = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 0,
        });
        let second = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 1,
        });
        let identity = env.arena().alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty,
            body: env.arena().exp_bound(0),
        });
        let id = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().alloc(ExpNode::Prod {
                        var: SymbolId::ANONYMOUS,
                        ty,
                        body: ty,
                    }),
                    body: identity,
                },
            )
            .unwrap();
        let alias = env.arena().alloc(ExpNode::DefinedConstant(id));
        let application = env.arena().alloc(ExpNode::App {
            func: alias,
            arg: first,
        });
        let annotated = env.arena().alloc(ExpNode::Ascribe {
            term: application,
            ty,
        });
        let registered = env.kernel_definitions.borrow().len();
        assert!(env.namespace_terms_equal(annotated, first));
        assert!(!env.namespace_terms_equal(annotated, second));
        assert_eq!(env.kernel_definitions.borrow().len(), registered);
    }

    #[test]
    fn aliases_inside_namespace_argument_lambdas_compare_without_kernel_registration() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let ty = env.arena().sort(Sort::Set(0));
        for _ in 0..2 {
            env.add_module_parameter(
                root,
                ModuleParameter {
                    name: SymbolId::ANONYMOUS,
                    kind: ModuleParameterKind::Pts { ty },
                },
            );
        }
        let first = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 0,
        });
        let second = env.arena().exp_module_param(ModuleParamId {
            module: root,
            position: 1,
        });
        let identity = env.arena().alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty,
            body: env.arena().exp_bound(0),
        });
        let id = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().alloc(ExpNode::Prod {
                        var: SymbolId::ANONYMOUS,
                        ty,
                        body: ty,
                    }),
                    body: identity,
                },
            )
            .unwrap();
        let application = env.arena().alloc(ExpNode::App {
            func: env.arena().alloc(ExpNode::DefinedConstant(id)),
            arg: first,
        });
        let left = env.arena().alloc(ExpNode::Lam {
            var: SymbolId(1),
            ty,
            body: application,
        });
        let right = env.arena().alloc(ExpNode::Lam {
            var: SymbolId(2),
            ty,
            body: first,
        });
        let different = env.arena().alloc(ExpNode::Lam {
            var: SymbolId(3),
            ty,
            body: second,
        });
        let registered = env.kernel_definitions.borrow().len();
        assert!(env.namespace_terms_equal(left, right));
        assert!(!env.namespace_syntax_equal(left, different));
        assert_eq!(env.kernel_definitions.borrow().len(), registered);
    }

    #[test]
    fn unresolved_argument_comparisons_are_not_cached() {
        use crate::raw::sort::Sort;
        let env = CrateEnv::new();
        let parameter = ModuleParamId {
            module: env.root_module(),
            position: 0,
        };
        // Structural translation cannot supply this unsupported open context.
        let unresolved = env.arena().exp_bound(100_001);
        let body = env.arena().sort(Sort::Set(0));
        let left = [(parameter, ModuleArgument::Pts(unresolved))];
        let right = [(parameter, ModuleArgument::Pts(body))];
        assert!(!env.namespace_arguments_equal(&left, &right));
        assert!(env.namespace_argument_cache.borrow().comparisons.is_empty());
        assert!(!env.namespace_arguments_equal(&right, &left));
        assert!(env.namespace_argument_cache.borrow().comparisons.is_empty());
    }

    #[test]
    fn renamed_binders_do_not_materialize_referenced_declarations() {
        let env = CrateEnv::new();
        // A source declaration can still be lazy when its argument syntax is
        // compared. Alpha equality needs its identity, not its definition.
        let declaration = DefId {
            module: env.root_module(),
            index: 99,
        };
        let domain = env.arena().alloc(ExpNode::DefinedConstant(declaration));
        let body = env.arena().exp_bound(0);
        let left = env.arena().alloc(ExpNode::Lam {
            var: SymbolId(1),
            ty: domain,
            body,
        });
        let right = env.arena().alloc(ExpNode::Lam {
            var: SymbolId(2),
            ty: domain,
            body,
        });
        assert_ne!(left, right);
        let kernel_terms_before = env.kernel.borrow().arena().len();
        assert!(env.namespace_terms_equal(left, right));
        assert_eq!(
            env.namespace_conversion_cache.borrow().get(&(left, right)),
            Some(&true)
        );
        assert_eq!(
            env.namespace_conversion_cache.borrow().get(&(right, left)),
            Some(&true)
        );
        assert!(env.namespace_terms_equal(right, left));
        assert_eq!(env.kernel.borrow().arena().len(), kernel_terms_before);
    }
}

#[cfg(test)]
mod substitution_tests {
    use super::super::exp::ExpNode;
    use super::*;

    #[test]
    fn namespace_substitution_cache_tracks_remapping_and_caller_arguments() {
        let env = CrateEnv::new();
        let source = DefId {
            module: env.root_module(),
            index: 0,
        };
        let first = DefId { index: 1, ..source };
        let second = DefId { index: 2, ..source };
        let parameter = ModuleParamId {
            module: env.root_module(),
            position: 0,
        };
        let variable = env.arena().exp_module_param(parameter);
        let reference = env.arena().alloc(ExpNode::DefinedConstant(source));
        let expression = env.arena().alloc(ExpNode::App {
            func: reference,
            arg: variable,
        });
        let a = env.arena().exp_bound(0);
        let b = env.arena().exp_bound(1);
        let mut remapping = DeclarationRemapping::default();
        let apply = |argument, remapping: &DeclarationRemapping| {
            env.substitute_namespace_expression(expression, &[(parameter, argument)], remapping)
        };
        let assert_image = |result, definition, argument| {
            let function = env.arena().alloc(ExpNode::DefinedConstant(definition));
            assert_eq!(
                result,
                env.arena().alloc(ExpNode::App {
                    func: function,
                    arg: argument
                })
            );
        };
        assert_image(apply(a, &remapping), source, a);
        remapping.definition_ids.insert(source, first);
        assert_image(apply(a, &remapping), first, a);
        assert_image(apply(a, &remapping), first, a);
        remapping.definition_ids.insert(source, second);
        assert_image(apply(b, &remapping), second, b);
        remapping.definition_ids.clear();
        assert_image(apply(a, &remapping), source, a);
    }
}
