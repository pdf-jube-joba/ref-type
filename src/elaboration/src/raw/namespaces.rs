//! Front-only provenance for substitution-specialized nominal declarations.
//!
//! Namespace aliases do not confer identity. Only the original declaration and
//! its arguments do; conversion in the kernel still compares ordinary type IDs.
use super::{environment::*, exp::Exp, ids::*, program::*, shared_map::IdLookup};

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) struct Specialization<I> {
    pub source: I,
    pub arguments: SharedArguments,
}

// Millions of nominal declarations share a comparatively small collection of
// telescopes. Keep their length in that shared allocation, not in every entry.
#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) struct SharedArguments(
    std::sync::Arc<std::sync::Arc<[(ModuleParamId, ModuleArgument)]>>,
);

impl From<std::sync::Arc<[(ModuleParamId, ModuleArgument)]>> for SharedArguments {
    fn from(arguments: std::sync::Arc<[(ModuleParamId, ModuleArgument)]>) -> Self {
        Self(std::sync::Arc::new(arguments))
    }
}

impl From<Vec<(ModuleParamId, ModuleArgument)>> for SharedArguments {
    fn from(arguments: Vec<(ModuleParamId, ModuleArgument)>) -> Self {
        std::sync::Arc::<[_]>::from(arguments).into()
    }
}

impl std::ops::Deref for SharedArguments {
    type Target = [(ModuleParamId, ModuleArgument)];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl SharedArguments {
    pub(crate) fn as_arc(&self) -> &std::sync::Arc<[(ModuleParamId, ModuleArgument)]> {
        &self.0
    }
}

// A namespace import updates declaration remappings as each declaration is
// canonicalized. Cache only when every global reference in the argument still
// has the same image, and substitutions of referenced parameters are unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Reference {
    Definition(DefId),
    Inductive(InductiveId),
    ProgramInductive(ProgramInductiveId),
}

type SubstitutionResult = (
    Vec<Reference>,
    Vec<(ModuleParamId, Exp)>,
    Vec<(ModuleParamId, ModuleArgument)>,
    Exp,
);

#[derive(Default, Debug)]
struct ExpressionDependencies {
    references: Vec<Reference>,
    parameters: rustc_hash::FxHashSet<ModuleParamId>,
}

#[derive(Default, Debug)]
pub(crate) struct SubstitutionCache {
    dependencies: rustc_hash::FxHashMap<Exp, ExpressionDependencies>,
    results: rustc_hash::FxHashMap<Exp, SubstitutionResult>,
}

#[derive(Debug)]
pub(crate) struct AliasHead {
    term: Exp,
    pending: Vec<DefId>,
}

pub(crate) type AliasCache = kernel::sharing::Cache<Exp, AliasHead, { 1 << 16 }>;

// Open imports share identities within one owner and exact checking telescopes.
#[derive(Debug, PartialEq, Eq, Hash)]
struct NamespaceScope {
    owner: ModuleId,
    logical: Option<std::sync::Arc<super::exp::ExpContext>>,
    program: Option<std::sync::Arc<ProgramContext>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct NamespaceScopeId(usize);

impl NamespaceScopeId {
    pub(crate) const CLOSED: Self = Self(0);
}

#[derive(Default, Debug)]
pub(crate) struct ArgumentCache {
    pub(crate) originals: rustc_hash::FxHashMap<ModuleId, SharedArguments>,
    scopes: rustc_hash::FxHashMap<NamespaceScope, NamespaceScopeId>,
    sets: rustc_hash::FxHashMap<std::sync::Arc<[(ModuleParamId, ModuleArgument)]>, usize>,
    comparisons: kernel::sharing::Cache<(usize, usize), bool, { 1 << 18 }>,
    shareability: rustc_hash::FxHashMap<usize, bool>,
    parents: Vec<usize>,
    classes: Vec<Vec<usize>>,
    arguments: Vec<std::sync::Arc<[(ModuleParamId, ModuleArgument)]>>,
    shared_arguments: Vec<SharedArguments>,
}

impl ArgumentCache {
    pub(crate) fn storage_counts(&self) -> [(&'static str, usize); 3] {
        [
            ("argument environments", self.arguments.len()),
            (
                "argument entries",
                self.arguments.iter().map(|a| a.len()).sum(),
            ),
            ("instance scopes", self.scopes.len()),
        ]
    }
    pub(crate) fn scope(
        &mut self,
        owner: ModuleId,
        logical: Option<std::sync::Arc<super::exp::ExpContext>>,
        program: Option<std::sync::Arc<ProgramContext>>,
    ) -> NamespaceScopeId {
        let next = NamespaceScopeId(self.scopes.len() + 1);
        *self
            .scopes
            .entry(NamespaceScope {
                owner,
                logical,
                program,
            })
            .or_insert(next)
    }

    fn root(&self, mut id: usize) -> usize {
        while self.parents[id] != id {
            id = self.parents[id];
        }
        id
    }

    fn known_equal(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        left == right
            || self
                .sets
                .get(left)
                .zip(self.sets.get(right))
                .is_some_and(|(&left, &right)| self.root(left) == self.root(right))
    }

    #[cfg(test)]
    pub(crate) fn equivalents(&self, id: usize) -> &[usize] {
        &self.classes[self.root(id)]
    }

    fn equate(&mut self, left: usize, right: usize) {
        let (mut left, mut right) = (self.root(left), self.root(right));
        if left == right {
            return;
        }
        if self.classes[left].len() < self.classes[right].len() {
            std::mem::swap(&mut left, &mut right);
        }
        self.parents[right] = left;
        let members = std::mem::take(&mut self.classes[right]);
        self.classes[left].extend(members);
    }

    pub(crate) fn share(
        &mut self,
        arguments: &[(ModuleParamId, ModuleArgument)],
    ) -> std::sync::Arc<[(ModuleParamId, ModuleArgument)]> {
        self.intern(arguments);
        self.sets.get_key_value(arguments).unwrap().0.clone()
    }

    pub(crate) fn intern(&mut self, arguments: &[(ModuleParamId, ModuleArgument)]) -> usize {
        if let Some(&id) = self.sets.get(arguments) {
            return id;
        }
        let id = self.sets.len();
        let arguments: std::sync::Arc<[_]> = arguments.into();
        self.sets.insert(arguments.clone(), id);
        self.shared_arguments.push(arguments.clone().into());
        self.arguments.push(arguments);
        self.parents.push(id);
        self.classes.push(vec![id]);
        id
    }

    pub(crate) fn share_compact(
        &mut self,
        arguments: &[(ModuleParamId, ModuleArgument)],
    ) -> SharedArguments {
        let id = self.intern(arguments);
        self.shared_arguments[id].clone()
    }
}

/// Failed translations are provisional. Reuse them only during one declaration's
/// candidate search, and retry after materialization or kernel registration.
#[derive(Default)]
pub(crate) struct Comparisons {
    failed: rustc_hash::FxHashMap<Exp, ComparisonVersion>,
    unresolved: rustc_hash::FxHashMap<(Exp, Exp), ComparisonVersion>,
}

#[derive(Debug, PartialEq, Eq)]
struct ComparisonVersion {
    materialized: MaterializationStats,
    kernel: (u64, usize, usize, usize, usize),
    translated: usize,
}

impl Comparisons {
    fn version(env: &CrateEnv) -> ComparisonVersion {
        ComparisonVersion {
            materialized: env.materialization_stats(),
            kernel: env.kernel.borrow().diagnostic_version(),
            translated: env.structural_expressions.borrow().len(),
        }
    }

    fn expression(&mut self, env: &CrateEnv, term: Exp) -> Option<kernel::syntax::Expression> {
        if self
            .failed
            .get(&term)
            .is_some_and(|version| *version == Self::version(env))
        {
            timing::costs::count("namespace.translation-retries-avoided", || 1);
            return None;
        }
        match crate::kernel_bridge::expression(
            env,
            super::traversal::Term::Logical(term),
            |_, e| Ok(e),
        ) {
            Ok(expression) => Some(expression),
            Err(error) => {
                let mut cause = &error;
                while let crate::error::Error::Context { source, .. } = cause {
                    cause = source;
                }
                use crate::error::{Error, Invalid};
                let label = match cause {
                    Error::UncapturedParameter { .. } => {
                        "namespace.translation-failed.uncaptured-parameter"
                    }
                    Error::ReservedDefinitionUsed { .. } => {
                        "namespace.translation-failed.reserved-definition"
                    }
                    Error::CyclicDefinition { .. } => {
                        "namespace.translation-failed.cyclic-definition"
                    }
                    Error::Invalid(Invalid::MissingDefinitionCaptures) => {
                        "namespace.translation-failed.missing-captures"
                    }
                    Error::Invalid(Invalid::DefinitionLocalContextIsOutsideReferenceScope) => {
                        "namespace.translation-failed.local-context"
                    }
                    Error::Invalid(_) => "namespace.translation-failed.invalid",
                    Error::Kernel(_) => "namespace.translation-failed.kernel",
                    _ => "namespace.translation-failed.other",
                };
                timing::costs::count(label, || {
                    if let Error::Kernel(error) = cause {
                        thread_local! {
                            static REPORTED: std::cell::RefCell<rustc_hash::FxHashSet<std::mem::Discriminant<kernel::error::Error>>> = Default::default();
                        }
                        let root = error.root();
                        if REPORTED
                            .with_borrow_mut(|seen| seen.insert(std::mem::discriminant(root)))
                        {
                            eprintln!(
                                "namespace.translation-failure sample={root} term={}",
                                super::printing::format_exp(env, term),
                            );
                        }
                    }
                    1
                });
                self.failed.insert(term, Self::version(env));
                None
            }
        }
    }
}

impl CrateEnv {
    fn namespace_term_is_rigid(&self, term: Exp) -> bool {
        matches!(
            self.arena().core.read(term.0).as_ref(),
            kernel::syntax::Node::Bound(_) | kernel::syntax::Node::Parameter(_)
        )
    }

    #[cfg(test)]
    fn namespace_syntax_equal(&self, left: Exp, right: Exp) -> bool {
        self.namespace_syntax_comparison(left, right).0
    }

    /// Also report whether the root aliases were compared, so conversion does
    /// not repeat a failed traversal of those same heads.
    fn namespace_syntax_comparison(&self, left: Exp, right: Exp) -> (bool, bool) {
        let _cost = timing::costs::Scope::enter("namespace.compare-syntax");
        use super::exp::ExpNode;
        fn compare(
            env: &CrateEnv,
            left: Exp,
            right: Exp,
            seen: &mut rustc_hash::FxHashSet<(Exp, Exp)>,
            compared_heads: Option<&mut bool>,
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
                if let Some(compared) = compared_heads {
                    *compared = true;
                }
                let left_head = env.namespace_alias_head(left);
                let right_head = env.namespace_alias_head(right);
                if left_head != left || right_head != right {
                    return compare(env, left_head, right_head, seen, None);
                }
                if declarations.is_some() {
                    return false;
                }
            }
            if let Some((l, r)) = declarations {
                // A closed declaration's identity is its source plus its
                // specialization arguments. Ambient local contexts require the
                // ordinary conversion path, which explicitly applies captures.
                let left_args = env.definition_specialization_arguments(l);
                let right_args = env.definition_specialization_arguments(r);
                let source = env.definition_specialization_source(l);
                if (left_args.is_empty() || right_args.is_empty())
                    && !env.namespace_arguments(source.module).is_empty()
                {
                    return false;
                }
                let known_equal = env
                    .namespace_argument_cache
                    .borrow()
                    .known_equal(&left_args, &right_args);
                if known_equal {
                    timing::costs::count("namespace.syntax-telescope-hits", || 1);
                }
                if !known_equal
                    && (left_args.len() != right_args.len()
                        || !left_args
                            .iter()
                            .zip(right_args.iter())
                            .all(|((lp, l), (rp, r))| {
                                lp == rp
                                    && match (*l, *r) {
                                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                                            compare(env, l, r, seen, None)
                                        }
                                        _ => l == r,
                                    }
                            }))
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
                    .all(|((l, ld), (r, rd))| ld == rd && compare(env, Exp(l), Exp(r), seen, None))
        }
        let mut compared_heads = false;
        let equal = compare(
            self,
            left,
            right,
            &mut rustc_hash::FxHashSet::default(),
            Some(&mut compared_heads),
        );
        (equal, compared_heads)
    }

    fn namespace_alias_head(&self, term: Exp) -> Exp {
        let _cost = timing::costs::Scope::enter("namespace.reduce-alias-head");
        if let Some(head) = self.namespace_alias_cache.borrow().get(&term)
            && head
                .pending
                .iter()
                .all(|&id| self.materialized_definition(id).is_none())
        {
            timing::costs::count("namespace.alias-head-cache-hits", || 1);
            return head.term;
        }
        timing::costs::count("namespace.alias-head-cache-misses", || 1);
        use super::exp::ExpNode;
        fn head(env: &CrateEnv, mut term: Exp, fuel: &mut usize, pending: &mut Vec<DefId>) -> Exp {
            // This only visits already materialized, closed definitions. The
            // shared budget also bounds beta reduction in application spines.
            while *fuel > 0 {
                *fuel -= 1;
                match env.arena().get(term) {
                    ExpNode::Ascribe { term: value, .. } => term = value,
                    ExpNode::App { func, arg } => {
                        let function = head(env, func, fuel, pending);
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
                        let definition = env.materialized_definition(id);
                        if definition.is_none() {
                            pending.push(id);
                        }
                        let Some(DefinedConstant::Pts { body, .. }) = definition else {
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
        // Completed definitions are immutable. Only an unavailable definition
        // visited by this bounded reduction can change its result later.
        let mut pending = Vec::new();
        let result = head(self, term, &mut 32, &mut pending);
        self.namespace_alias_cache.borrow_mut().insert(
            term,
            AliasHead {
                term: result,
                pending,
            },
        );
        result
    }

    #[cfg(test)]
    pub(crate) fn namespace_terms_equal(&self, left: Exp, right: Exp) -> bool {
        self.namespace_terms_equal_with(left, right, &mut Comparisons::default())
    }

    fn namespace_terms_equal_with(
        &self,
        left: Exp,
        right: Exp,
        comparisons: &mut Comparisons,
    ) -> bool {
        let _cost = timing::costs::Scope::enter("namespace.compare-term");
        if left == right {
            return true;
        }
        if let Some(&equal) = self.namespace_conversion_cache.borrow().get(&(left, right)) {
            timing::costs::count("namespace.term-cache-hits", || 1);
            return equal;
        }
        if comparisons
            .unresolved
            .get(&(left, right))
            .is_some_and(|version| *version == Comparisons::version(self))
        {
            timing::costs::count("namespace.comparison-retries-avoided", || 1);
            return false;
        }
        // Distinct normal heads cannot become equal as imported definitions
        // are materialized. Check before recursively comparing their children.
        if self.namespace_term_is_rigid(left) && self.namespace_term_is_rigid(right) {
            self.cache_namespace_equality(left, right, false);
            return false;
        }
        // The source and kernel share an expression arena. Binder renaming is
        // already decidable on that syntax; it does not require materializing
        // the declarations mentioned by a namespace argument.
        let alpha_equal = {
            let _cost = timing::costs::Scope::enter("namespace.compare-alpha");
            kernel::calculus::alpha_equal(&self.arena().core, left.0, right.0)
        };
        if alpha_equal {
            self.cache_namespace_equality(left, right, true);
            return true;
        }
        let (syntax_equal, compared_heads) = self.namespace_syntax_comparison(left, right);
        if syntax_equal {
            self.cache_namespace_equality(left, right, true);
            return true;
        }
        let left_alias = self.namespace_alias_head(left);
        let right_alias = self.namespace_alias_head(right);
        if !compared_heads
            && (left_alias != left || right_alias != right)
            && self.namespace_syntax_comparison(left_alias, right_alias).0
        {
            self.cache_namespace_equality(left, right, true);
            return true;
        }
        // Avoid registering an entire captured declaration graph merely to
        // reject normal heads exposed by alias reduction.
        if self.namespace_term_is_rigid(left_alias) && self.namespace_term_is_rigid(right_alias) {
            self.cache_namespace_equality(left, right, false);
            return false;
        }
        let equal = (|| {
            let left = comparisons.expression(self, left)?;
            let right = comparisons.expression(self, right)?;
            kernel::reduction::convertible(&self.kernel.borrow(), left, right).ok()
        })();
        let Some(equal) = equal else {
            comparisons
                .unresolved
                .insert((left, right), Comparisons::version(self));
            timing::costs::count("namespace.unresolved-comparisons", || 1);
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
        self.namespace_arguments_shared(module).to_vec()
    }

    pub(crate) fn namespace_arguments_shared(&self, module: ModuleId) -> SharedArguments {
        if let Some(arguments) = self
            .namespace_argument_cache
            .borrow()
            .originals
            .get(&module)
        {
            return arguments.clone();
        }
        let _cost = timing::costs::Scope::enter("namespace.collect-arguments");
        let mut ancestors = Vec::new();
        let mut current = Some(module);
        while let Some(id) = current {
            ancestors.push(id);
            current = self.module(id).parent();
        }
        ancestors.reverse();
        let arguments: Vec<_> = ancestors
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
            .collect();
        let mut cache = self.namespace_argument_cache.borrow_mut();
        let arguments = cache.share_compact(&arguments);
        cache.originals.insert(module, arguments.clone());
        arguments
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
                    ModuleArgument::Pts(e) => {
                        ModuleArgument::Pts(self.substitute_namespace_expression(
                            e,
                            substitutions,
                            reflected,
                            remapping,
                        ))
                    }
                    ModuleArgument::ProgramType(t) => ModuleArgument::ProgramType(
                        crate::raw::remapping::subst_value_type_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_value_type_global_ids(
                                self.arena(),
                                t,
                                &remapping.definitions(self),
                                &remapping.datatypes(self),
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
                                &remapping.definitions(self),
                                &remapping.datatypes(self),
                                &remapping.inductives(self),
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
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> Exp {
        use super::exp::ExpNode;
        use super::traversal::{Memoized, Term};
        let mut cache = self.namespace_substitution_cache.borrow_mut();
        let dependencies = cache.dependencies.entry(expression).or_insert_with(|| {
            let mut references = rustc_hash::FxHashSet::default();
            let mut parameters = rustc_hash::FxHashSet::default();
            Term::Logical(expression).walk(
                self.arena(),
                0,
                &mut Memoized::new(|term: Term, _: usize| {
                    let reference = match term {
                        Term::Logical(e) => match self.arena().get(e) {
                            ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => {
                                parameters.insert(id);
                                None
                            }
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
                            ValueTypeNode::ModuleParam(id) => {
                                parameters.insert(id);
                                None
                            }
                            ValueTypeNode::Inductive { indspec, .. } => {
                                Some(Reference::ProgramInductive(indspec))
                            }
                            _ => None,
                        },
                        Term::Value(v) => match self.arena().get(v) {
                            ValueTermNode::ModuleParam(id) => {
                                parameters.insert(id);
                                None
                            }
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
            ExpressionDependencies {
                references: references.into_iter().collect(),
                parameters,
            }
        });
        let substitutions: Vec<_> = substitutions
            .iter()
            .copied()
            .filter(|(id, _)| dependencies.parameters.contains(id))
            .collect();
        let reflected: Vec<_> = reflected
            .iter()
            .copied()
            .filter(|(id, _)| dependencies.parameters.contains(id))
            .collect();
        let images: Vec<_> = dependencies
            .references
            .iter()
            .map(|reference| match *reference {
                Reference::Definition(id) => {
                    Reference::Definition(remapping.definitions(self).resolve(&id).unwrap_or(id))
                }
                Reference::Inductive(id) => {
                    Reference::Inductive(remapping.inductives(self).resolve(&id).unwrap_or(id))
                }
                Reference::ProgramInductive(id) => Reference::ProgramInductive(
                    remapping.datatypes(self).resolve(&id).unwrap_or(id),
                ),
            })
            .collect();
        if let Some((old_images, old_reflected, old_substitutions, result)) =
            cache.results.get(&expression)
            && *old_images == images
            && *old_reflected == reflected
            && *old_substitutions == substitutions
        {
            timing::costs::count("namespace.substitution-cache-hits", || 1);
            return *result;
        }
        timing::costs::count("namespace.substitution-cache-misses", || 1);
        let remapped = crate::raw::remapping::remap_all_global_ids(
            self.arena(),
            expression,
            &remapping.definitions(self),
            &remapping.inductives(self),
            &remapping.datatypes(self),
        );
        let Term::Logical(result) =
            Term::Logical(remapped).substitute(self.arena(), &substitutions, &reflected)
        else {
            unreachable!()
        };
        cache
            .results
            .insert(expression, (images, reflected, substitutions, result));
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
        self.namespace_arguments_equal_with(left, right, &mut Comparisons::default())
    }

    pub(crate) fn namespace_arguments_equal_with(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
        comparisons: &mut Comparisons,
    ) -> bool {
        let _cost = timing::costs::Scope::enter("namespace.compare-arguments");
        if left == right {
            return true;
        }
        let key = {
            let mut cache = self.namespace_argument_cache.borrow_mut();
            let left = cache.intern(left);
            let right = cache.intern(right);
            if cache.root(left) == cache.root(right) {
                timing::costs::count("namespace.argument-equivalence-hits", || 1);
                return true;
            }
            (left.min(right), left.max(right))
        };
        if let Some(&equal) = self.namespace_argument_cache.borrow().comparisons.get(&key) {
            timing::costs::count("namespace.argument-comparison-cache-hits", || 1);
            return equal;
        }
        timing::costs::count("namespace.argument-comparison-cache-misses", || 1);
        // A later opaque argument can rule out the whole telescope before an
        // expensive (or still unresolved) comparison of its shared prefix.
        if self.namespace_arguments_rigidly_differ(left, right) {
            self.namespace_argument_cache
                .borrow_mut()
                .comparisons
                .insert(key, false);
            return false;
        }
        let equal = left.len() == right.len()
            && left.iter().zip(right).all(|((lp, l), (rp, r))| {
                lp == rp
                    && match (*l, *r) {
                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                            self.namespace_terms_equal_with(l, r, comparisons)
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
                                    (Ok(l), Ok(r)) => {
                                        self.namespace_terms_equal_with(l, r, comparisons)
                                    }
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
        if equal {
            // Conversion of a telescope is independent of the declaration using
            // it. Reuse the established equality across all specialization tables.
            self.namespace_argument_cache
                .borrow_mut()
                .equate(key.0, key.1);
        }
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
        let _cost = timing::costs::Scope::enter("namespace.compare-rigid-arguments");
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
                self.namespace_term_is_rigid(l) && self.namespace_term_is_rigid(r)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::raw::exp::ExpNode;

    #[test]
    fn telescope_equivalence_classes_preserve_all_prior_specialization_keys() {
        let env = CrateEnv::new();
        let parameter = ModuleParamId {
            module: env.root_module(),
            position: 0,
        };
        let mut cache = ArgumentCache::default();
        let ids: Vec<_> = (0..4)
            .map(|index| {
                cache.intern(&[(parameter, ModuleArgument::Pts(env.arena().exp_bound(index)))])
            })
            .collect();
        cache.equate(ids[0], ids[1]);
        cache.equate(ids[2], ids[3]);
        cache.equate(ids[1], ids[3]);
        for id in ids {
            let mut members = cache.equivalents(id).to_vec();
            members.sort_unstable();
            assert_eq!(members, [0, 1, 2, 3]);
        }
    }

    #[test]
    fn transitive_telescope_equalities_survive_comparison_cache_recycling() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let parameter = ModuleParamId {
            module: root,
            position: 0,
        };
        let mut arguments = Vec::new();
        for _ in 0..3 {
            let alias = env
                .add_definition(
                    root,
                    DefinedConstant::Pts {
                        ty: env.arena().sort(Sort::SetKind(0)),
                        body: env.arena().sort(Sort::Set(0)),
                    },
                )
                .unwrap();
            arguments.push(vec![(
                parameter,
                ModuleArgument::Pts(env.arena().alloc(ExpNode::DefinedConstant(alias))),
            )]);
        }
        assert!(env.namespace_arguments_equal(&arguments[0], &arguments[1]));
        assert!(env.namespace_arguments_equal(&arguments[1], &arguments[2]));
        env.namespace_argument_cache
            .borrow_mut()
            .comparisons
            .clear();
        env.namespace_conversion_cache.borrow_mut().clear();
        assert!(env.namespace_arguments_equal(&arguments[0], &arguments[2]));
        assert!(env.namespace_argument_cache.borrow().comparisons.is_empty());
        assert!(env.namespace_conversion_cache.borrow().is_empty());
        assert!(
            env.namespace_argument_cache
                .borrow()
                .known_equal(&arguments[0], &arguments[2])
        );
    }

    #[test]
    fn specialization_telescopes_share_the_interned_allocation() {
        let env = CrateEnv::new();
        let parameter = ModuleParamId {
            module: env.root_module(),
            position: 0,
        };
        let arguments = [(parameter, ModuleArgument::Pts(env.arena().exp_bound(0)))];
        let mut cache = ArgumentCache::default();
        let first = cache.share(&arguments);
        let second = cache.share(&arguments);
        assert!(std::sync::Arc::ptr_eq(&first, &second));
        assert_eq!(cache.intern(&arguments), 0);
        let compact = cache.share_compact(&arguments);
        let repeated = cache.share_compact(&arguments);
        assert!(std::sync::Arc::ptr_eq(&compact.0, &repeated.0));
        assert!(std::sync::Arc::ptr_eq(&first, compact.as_arc()));
        assert_eq!(
            std::mem::size_of::<SharedArguments>(),
            std::mem::size_of::<usize>()
        );
        assert_eq!(std::mem::size_of::<Specialization<DefId>>(), 16);
    }

    #[test]
    fn provisional_translation_failures_follow_environment_progress() {
        let env = CrateEnv::new();
        let unsupported = env.arena().exp_bound(100_001);
        let mut comparisons = Comparisons::default();
        assert!(comparisons.expression(&env, unsupported).is_none());
        assert!(comparisons.expression(&env, unsupported).is_none());
        assert_eq!(comparisons.failed.len(), 1);
        assert!(env.structural_expressions.borrow().is_empty());
        let set = env.arena().sort(crate::raw::sort::Sort::Set(0));
        assert!(!env.namespace_terms_equal_with(unsupported, set, &mut comparisons));
        assert!(!env.namespace_terms_equal_with(unsupported, set, &mut comparisons));
        assert_eq!(comparisons.unresolved.len(), 1);
        let valid = env.arena().exp_bound(0);
        assert!(comparisons.expression(&env, valid).is_some());
        assert_ne!(comparisons.failed[&unsupported], Comparisons::version(&env));
        assert!(comparisons.expression(&env, unsupported).is_none());
        assert_eq!(comparisons.failed[&unsupported], Comparisons::version(&env));
        assert_ne!(
            comparisons.unresolved[&(unsupported, set)],
            Comparisons::version(&env)
        );
        assert!(!env.namespace_terms_equal_with(unsupported, set, &mut comparisons));
        assert_eq!(
            comparisons.unresolved[&(unsupported, set)],
            Comparisons::version(&env)
        );
        assert!(Comparisons::default().failed.is_empty());
        assert!(env.namespace_conversion_cache.borrow().is_empty());
    }

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
    fn alias_heads_retry_when_a_dependency_is_materialized() {
        use crate::raw::sort::Sort;
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let set = env.arena().sort(Sort::Set(0));
        let source = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().sort(Sort::SetKind(0)),
                    body: set,
                },
            )
            .unwrap();
        let copy = env.reserve_lazy_definition(root, source, vec![], vec![]);
        let reference = env.arena().alloc(ExpNode::DefinedConstant(copy));
        let function = env.arena().alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty: set,
            body: reference,
        });
        let applied = env.arena().alloc(ExpNode::App {
            func: function,
            arg: env.arena().alloc(ExpNode::Bound(0)),
        });
        assert_eq!(env.namespace_alias_head(applied), reference);
        assert_eq!(env.namespace_alias_head(applied), reference);
        env.resolve_definition(copy).unwrap();
        assert_eq!(env.namespace_alias_head(applied), set);
        assert_eq!(env.namespace_alias_head(applied), set);
    }

    #[test]
    fn alias_heads_keep_the_reduction_budget_on_cache_hits() {
        use crate::raw::sort::Sort;
        let env = CrateEnv::new();
        let set = env.arena().sort(Sort::Set(0));
        let mut term = set;
        for _ in 0..40 {
            term = env.arena().alloc(ExpNode::Ascribe { term, ty: set });
        }
        let reduced = env.namespace_alias_head(term);
        assert_ne!(reduced, set);
        assert_eq!(env.namespace_alias_head(term), reduced);
        assert_eq!(env.namespace_alias_head(reduced), set);
        assert_eq!(env.namespace_alias_head(term), reduced);
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
    fn rigid_suffix_rejects_arguments_before_lowering_an_unresolved_prefix() {
        use crate::raw::sort::Sort;
        let env = CrateEnv::new();
        let first = ModuleParamId {
            module: env.root_module(),
            position: 0,
        };
        let second = ModuleParamId {
            module: env.root_module(),
            position: 1,
        };
        let left = [
            (first, ModuleArgument::Pts(env.arena().exp_bound(100_001))),
            (
                second,
                ModuleArgument::Pts(env.arena().exp_module_param(first)),
            ),
        ];
        let right = [
            (first, ModuleArgument::Pts(env.arena().sort(Sort::Set(0)))),
            (
                second,
                ModuleArgument::Pts(env.arena().exp_module_param(second)),
            ),
        ];
        assert!(!env.namespace_arguments_equal(&left, &right));
        assert!(!env.namespace_arguments_equal(&right, &left));
        assert_eq!(env.namespace_argument_cache.borrow().comparisons.len(), 1);
        assert!(env.namespace_conversion_cache.borrow().is_empty());
        assert!(env.kernel_definitions.borrow().is_empty());
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
            env.substitute_namespace_expression(
                expression,
                &[],
                &[(parameter, argument)],
                remapping,
            )
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
        let unused = ModuleParamId {
            position: 1,
            ..parameter
        };
        let result = env.substitute_namespace_expression(
            expression,
            &[],
            &[(unused, b), (parameter, a)],
            &remapping,
        );
        assert_image(result, source, a);
        assert_eq!(
            env.namespace_substitution_cache.borrow().results[&expression].1,
            [(parameter, a)],
        );

        // Reflected parameters beneath binders also belong to the dependency
        // key, and caller variables must still be shifted under that binder.
        let reflected = env.arena().alloc(ExpNode::ReflectedProgramParam(parameter));
        let lambda = env.arena().alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty: env.arena().sort(crate::raw::sort::Sort::Set(0)),
            body: reflected,
        });
        for argument in [a, b] {
            assert_eq!(
                env.substitute_namespace_expression(
                    lambda,
                    &[],
                    &[(parameter, argument)],
                    &remapping
                ),
                super::super::remapping::exp_subst_map(
                    env.arena(),
                    lambda,
                    &[(parameter, argument)]
                ),
            );
        }
    }
}
