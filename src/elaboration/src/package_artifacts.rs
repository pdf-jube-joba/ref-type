//! Portable package identities shared by the resolver and checking workspace.
use super::*;
use artifact::{Error, Identity, Relocate, Relocation};
use std::collections::{BTreeMap, BTreeSet};

pub type ArtifactOwner = [u8; 32];

/// Source allocation ordinals have exact compact identities; structural values
/// retain full SHA-256 labels. The variant separates the two identity domains.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
enum Label {
    Digest([u8; 32]),
    Resolver { space: u8, ordinal: u64 },
    BindingSymbol { space: u8, ordinal: u64, index: u32 },
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
struct Reference {
    owner: ArtifactOwner,
    local: Label,
}

/// The active dependency closure's correspondence between portable and live IDs.
/// Saving it with a checkpoint preserves the same ownership boundary on resume.
#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct ArtifactCatalog {
    runtime: BTreeMap<Identity, BTreeSet<Reference>>,
    portable: BTreeMap<Reference, Identity>,
    packages: BTreeSet<ArtifactOwner>,
    dependencies: BTreeMap<ArtifactOwner, BTreeSet<ArtifactOwner>>,
    sources: BTreeMap<Reference, ArtifactOwner>,
}
impl ArtifactCatalog {
    pub fn contains(&self, owner: &ArtifactOwner) -> bool {
        self.packages.contains(owner)
    }
    fn reference(
        &self,
        identity: &Identity,
        owners: &BTreeSet<ArtifactOwner>,
    ) -> Option<&Reference> {
        self.runtime
            .get(identity)?
            .iter()
            .find(|reference| owners.contains(&reference.owner))
    }
    fn register(&mut self, reference: Reference, runtime: Identity) -> artifact::Result<()> {
        if self
            .portable
            .get(&reference)
            .is_some_and(|old| old != &runtime)
        {
            return Err(Error(
                "package identity registered with conflicting runtime ID".into(),
            ));
        }
        self.runtime
            .entry(runtime.clone())
            .or_default()
            .insert(reference);
        self.portable.insert(reference, runtime);
        Ok(())
    }
}

pub struct ArtifactBoundary {
    resolution: resolve::PackageBoundary,
    workspace: crate::elaborator::exports::Boundary,
    steps: usize,
}

/// Independent store objects. Environment bytes include the one shared raw and
/// kernel expression graph; result-only clients need neither object.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct PackageArtifact {
    pub resolver: Vec<u8>,
    pub environment: Vec<u8>,
}

impl PackageArtifact {
    fn header(&self) -> artifact::Result<ArtifactHeader> {
        if self.resolver.len() > MAX_PACKAGE_BYTES {
            return Err(Error("package object size limit exceeded".into()));
        }
        let (header, _): (ArtifactHeader, _) =
            postcard::take_from_bytes(&self.resolver).map_err(error)?;
        if header.version != 3 {
            return Err(Error("unsupported resolver artifact version".into()));
        }
        Ok(header)
    }

    pub fn owner(&self) -> artifact::Result<ArtifactOwner> {
        Ok(self.header()?.owner)
    }
    pub fn dependencies(&self) -> artifact::Result<Vec<ArtifactOwner>> {
        Ok(self.header()?.dependencies)
    }
}

/// Prefix decoding reads dependency metadata without allocating resolver tables.
/// Field order matches the beginning of ResolverObject's postcard representation.
#[derive(serde::Deserialize)]
struct ArtifactHeader {
    version: u32,
    owner: ArtifactOwner,
    #[serde(rename = "input")]
    _input: ArtifactOwner,
    dependencies: Vec<ArtifactOwner>,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct ResolverObject {
    version: u32,
    owner: ArtifactOwner,
    input: ArtifactOwner,
    dependencies: Vec<ArtifactOwner>,
    pending: bool,
    completed_steps: usize,
    checked_steps: Vec<usize>,
    references: Vec<(Identity, Reference)>,
    resolver: resolve::PackageExport,
}

fn builtin(identity: &Identity) -> bool {
    matches!(identity, Identity::Scalar { space, value }
        if ((space == "resolve.module" || space == "raw.module" || space == "raw.remapping" || space == "raw.remapping.snapshot") && *value == 0)
            || (space == "symbol" && *value < 2))
}
fn identity_of_expression(expression: kernel::syntax::Expression) -> Identity {
    Identity::scalar("expression", expression.index() as u64)
}
fn error(error: impl std::fmt::Display) -> Error {
    Error(error.to_string())
}

impl PackageChecker {
    pub fn artifact_boundary(&self) -> ArtifactBoundary {
        ArtifactBoundary {
            resolution: self.resolution.boundary(),
            workspace: self.workspace.artifact_boundary(),
            steps: self.steps,
        }
    }

    pub fn export_artifact(
        &self,
        owner: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        if self.pending {
            return Err(Error("cannot publish a pending package as verified".into()));
        }
        self.export_package_state(owner, owner, boundary, catalog)
    }

    pub fn export_resume(
        &self,
        owner: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        if !self.pending {
            return Err(Error("resume export requires a pending package".into()));
        }
        self.export_package_state(owner, owner, boundary, catalog)
    }

    pub fn export_artifact_for_input(
        &self,
        owner: ArtifactOwner,
        input: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        if self.pending {
            return Err(Error("cannot publish pending package".into()));
        }
        self.export_package_state(owner, input, boundary, catalog)
    }
    pub fn export_resume_for_input(
        &self,
        owner: ArtifactOwner,
        input: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        if !self.pending {
            return Err(Error("resume requires pending package".into()));
        }
        self.export_package_state(owner, input, boundary, catalog)
    }
    fn export_package_state(
        &self,
        owner: ArtifactOwner,
        input: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        State {
            resolution: &self.resolution,
            workspace: &self.workspace,
            steps: self.steps,
            pending: self.pending,
            completed: &self.completed,
        }
        .export_package_state(owner, input, boundary, catalog)
    }

    /// Validate and publish all three environments together. A failed import
    /// leaves both the live checker and its ownership catalog unchanged.
    pub fn import_artifact(
        &mut self,
        package: &PackageArtifact,
        catalog: &mut ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> artifact::Result<()> {
        self.import_package_state(package, catalog, sources, false)
    }

    pub fn import_resume(
        &mut self,
        package: &PackageArtifact,
        catalog: &mut ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> artifact::Result<()> {
        self.import_package_state(package, catalog, sources, true)
    }

    /// Import into a disposable checker without copying its dependency closure.
    /// Failure consumes both values; success returns their updated state.
    pub fn import_artifact_owned(
        self,
        package: &PackageArtifact,
        catalog: ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> artifact::Result<(Self, ArtifactCatalog)> {
        self.import_package_state_owned(package, catalog, sources, false)
    }

    /// Resume in a disposable checker, preserving the dependency-only catalog.
    pub fn import_resume_owned(
        self,
        package: &PackageArtifact,
        catalog: ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> artifact::Result<(Self, ArtifactCatalog)> {
        self.import_package_state_owned(package, catalog, sources, true)
    }

    fn import_package_state(
        &mut self,
        package: &PackageArtifact,
        catalog: &mut ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
        resume: bool,
    ) -> artifact::Result<()> {
        // Keep the borrowed API transactional for callers retaining this checker.
        // Dependency loading uses the consuming API and avoids this copy.
        let bytes = self.checkpoint().map_err(error)?;
        let staged = Self::restore(&bytes, &sources)
            .ok_or_else(|| Error("cannot stage package import".into()))?;
        drop(bytes);
        let (staged, updated) =
            staged.import_package_state_owned(package, catalog.clone(), sources, resume)?;
        *self = staged;
        *catalog = updated;
        Ok(())
    }

    fn import_package_state_owned(
        mut self,
        package: &PackageArtifact,
        mut catalog: ArtifactCatalog,
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
        resume: bool,
    ) -> artifact::Result<(Self, ArtifactCatalog)> {
        let _phase = crate::profiling::Phase::start("artifact.import");
        if self.pending {
            return Err(Error("cannot import into an unfinished package".into()));
        }
        if package.resolver.len() > MAX_PACKAGE_BYTES
            || package.environment.len() > MAX_PACKAGE_BYTES
        {
            return Err(Error("package object size limit exceeded".into()));
        }
        let decoding = crate::profiling::Phase::start("artifact.decode");
        let mut resolver: ResolverObject =
            postcard::from_bytes(&package.resolver).map_err(error)?;
        if resolver.version != 3 {
            return Err(Error("unsupported resolver artifact version".into()));
        }
        if resolver.pending != resume {
            return Err(Error("package artifact/checkpoint kind mismatch".into()));
        }
        if catalog.contains(&resolver.owner) {
            return Ok((self, catalog));
        }
        let mut workspace: crate::elaborator::exports::Export =
            postcard::from_bytes(&package.environment).map_err(error)?;
        drop(decoding);
        // Owned expression labels are a pure function of the topological graph
        // and its external references. Reconstruct them instead of persisting a
        // random 32-byte digest alongside every already stored expression node.
        identity::restore_expression_references(
            &workspace.graph,
            resolver.input,
            &mut resolver.references,
        )?;
        let mut relocation = Relocation::default();
        for (space, value) in [
            ("resolve.module", 0),
            ("raw.module", 0),
            ("raw.remapping", 0),
            ("raw.remapping.snapshot", 0),
            ("symbol", 0),
            ("symbol", 1),
        ] {
            relocation.insert(space, value, value)?;
        }
        let mut seen = BTreeSet::new();
        for (identity, reference) in &resolver.references {
            if !seen.insert(identity.clone()) {
                return Err(Error("duplicate portable identity".into()));
            }
            if let Some(runtime) = catalog.portable.get(reference) {
                relocation.insert_identity(identity.clone(), runtime.clone())?;
            } else if reference.owner != resolver.input {
                return Err(Error("missing dependency artifact identity".into()));
            }
        }
        let mut own_order = resolver.resolver.order().to_vec();
        self.resolution
            .reserve_import(&resolver.resolver, &mut relocation)?;
        own_order.relocate(&mut relocation)?;
        self.workspace
            .reserve_artifact(&mut workspace, &mut relocation)?;
        self.workspace.import_artifact(workspace, &mut relocation)?;
        self.resolution
            .import_package(resolver.resolver, &mut relocation)?;
        self.resolution
            .restore_sources(&sources)
            .ok_or_else(|| Error("artifact source missing from snapshot".into()))?;
        let project = self.resolution.project();
        self.workspace.restore_artifact_analysis(&project);
        let end = project.order.len();
        let start = own_order
            .first()
            .and_then(|first| project.order.iter().position(|step| step == first))
            .unwrap_or(end);
        if project.order.get(start..start + own_order.len()) != Some(own_order.as_slice()) {
            return Err(Error(
                "package checking order does not match imported resolver".into(),
            ));
        }
        for position in resolver.checked_steps {
            if position >= own_order.len() {
                return Err(Error("checked step outside package coverage".into()));
            }
            self.completed.insert(start + position);
        }
        if resolver.completed_steps > own_order.len()
            || (!resume && resolver.completed_steps != own_order.len())
        {
            return Err(Error("invalid completed checkpoint step count".into()));
        }
        self.steps = if resume {
            start + resolver.completed_steps
        } else {
            end
        };
        self.pending = resume;
        let dependencies = resolver
            .references
            .iter()
            .map(|(_, reference)| reference.owner)
            .filter(|owner| *owner != resolver.input)
            .collect();
        for (identity, reference) in resolver.references {
            let runtime = relocation
                .lookup(&identity)
                .ok_or_else(|| Error(format!("unreserved exported identity {identity:?}")))?
                .clone();
            if !resume {
                if reference.owner == resolver.input {
                    catalog.sources.insert(reference, resolver.owner);
                }
                catalog.register(reference, runtime)?;
            }
        }
        if !resume {
            catalog.packages.insert(resolver.owner);
            catalog.dependencies.insert(resolver.input, dependencies);
        }
        Ok((self, catalog))
    }
}

/// Borrow the live checkpoint boundary without serializing its dependencies.
pub(super) struct State<'a> {
    pub(super) resolution: &'a resolve::Session,
    pub(super) workspace: &'a GlobalEnvironment,
    pub(super) steps: usize,
    pub(super) pending: bool,
    pub(super) completed: &'a BTreeSet<usize>,
}

impl State<'_> {
    pub(super) fn export_package_state(
        &self,
        owner: ArtifactOwner,
        input: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
    ) -> artifact::Result<PackageArtifact> {
        if catalog.contains(&owner) {
            return Err(Error("package already exported".into()));
        }
        let _export_phase = crate::profiling::Phase::start("artifact.export");
        let snapshots = self.workspace.crate_env.snapshot_transaction();
        let mut resolver = self.resolution.export_package(&boundary.resolution)?;
        let mut resolver_inventory = Relocation::collecting();
        resolver.relocate(&mut resolver_inventory)?;
        let mut dependencies: BTreeSet<_> = resolver_inventory
            .into_identities()
            .into_iter()
            .flat_map(|identity| {
                catalog
                    .runtime
                    .get(&identity)
                    .into_iter()
                    .flatten()
                    .map(|reference| reference.owner)
            })
            .collect();
        dependencies.remove(&input);
        let mut pending: Vec<_> = dependencies.iter().copied().collect();
        while let Some(owner) = pending.pop() {
            for dependency in catalog.dependencies.get(&owner).into_iter().flatten() {
                if dependencies.insert(*dependency) {
                    pending.push(*dependency);
                }
            }
        }
        let workspace_phase = crate::profiling::Phase::start("artifact.export-workspace");
        let mut workspace = self.workspace.export_artifact(
            &boundary.workspace,
            |expression| {
                catalog
                    .reference(&identity_of_expression(expression), &dependencies)
                    .is_some()
            },
            self.pending,
            |snapshot| {
                catalog
                    .reference(&identity::identity(&snapshot), &dependencies)
                    .is_some()
            },
        )?;
        drop(workspace_phase);
        let mut inventory = Relocation::collecting();
        resolver.relocate(&mut inventory)?;
        workspace.relocate(&mut inventory)?;
        let mut identities = inventory.into_identities();
        // Kernel nominal numbers encode the owning raw module and declaration
        // index. Include the module reference even when only a type is reachable.
        let nominal_modules: Vec<_> = identities
            .iter()
            .filter_map(|identity| match identity {
                Identity::Scalar { space, value }
                    if matches!(space.as_str(), "inductive" | "datatype" | "parameter") =>
                {
                    Some(Identity::scalar("raw.module", value >> 32))
                }
                _ => None,
            })
            .collect();
        identities.extend(nominal_modules);
        let labels_phase = crate::profiling::Phase::start("artifact.identity-labels");
        let semantic = identity::labels(
            &mut workspace,
            self.workspace,
            &resolver,
            &identities,
            catalog,
            &dependencies,
            input,
            owner,
        )?;
        drop(labels_phase);
        let mut depths = rustc_hash::FxHashMap::default();
        for (expression, node) in &workspace.graph.nodes {
            let mut depth = 0usize;
            node.try_for_each_child::<Error>(|child, _| {
                depth = depth.max(depths.get(&child).copied().unwrap_or(0));
                Ok(())
            })?;
            depths.insert(*expression, depth + 1);
        }
        workspace.graph.nodes.sort_by_cached_key(|(expression, _)| {
            (
                depths[expression],
                semantic[&identity_of_expression(*expression)],
            )
        });
        workspace.raw.symbols.sort_by_cached_key(|(symbol, _, _)| {
            semantic
                .get(&Identity::scalar("symbol", symbol.0 as u64))
                .copied()
        });
        drop(depths);
        let mut references: Vec<_> = semantic.into_iter().collect();
        let exact_dependencies: Vec<_> = references
            .iter()
            .filter(|(_, reference)| reference.owner != input)
            .filter_map(|(_, reference)| catalog.sources.get(reference).copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        // Canonical IDs depend only on portable references, never previous
        // runtime allocations or a consuming package's location.
        references.sort_by(|(a, ar), (b, br)| a.space().cmp(b.space()).then_with(|| ar.cmp(br)));
        let mut relocation = Relocation::default();
        for identity in identities.iter().filter(|identity| builtin(identity)) {
            relocation.insert_identity(identity.clone(), identity.clone())?;
        }
        drop(identities);
        let mut next: BTreeMap<String, u64> = BTreeMap::new();
        for (identity, _) in &references {
            if matches!(identity, Identity::Scalar{space,..} if matches!(space.as_str(), "inductive"|"datatype"|"parameter"))
            {
                continue;
            }
            let index = next.entry(identity.space().into()).or_insert(2);
            let normalized = match identity {
                Identity::Scalar { space, .. } => Identity::scalar(space, *index),
                Identity::Pair { space, .. } => {
                    Identity::pair(space, (1, u32::try_from(*index).map_err(error)?))
                }
            };
            *index += 1;
            relocation.insert_identity(identity.clone(), normalized)?;
        }
        for (identity, _) in &references {
            if let Identity::Scalar { space, value } = identity
                && matches!(space.as_str(), "inductive" | "datatype" | "parameter")
            {
                let module = relocation.id("raw.module", value >> 32)?;
                relocation.insert(space, *value, (module << 32) | (value & 0xffff_ffff))?;
            }
        }
        resolver.relocate(&mut relocation)?;
        workspace.relocate(&mut relocation)?;
        let source_modules: Vec<_> = resolver
            .owned_ids()
            .into_iter()
            .filter_map(|identity| {
                let Identity::Scalar { space, value } = identity else {
                    return None;
                };
                (space == "resolve.module")
                    .then(|| {
                        workspace
                            .modules
                            .get(&resolve::hir::ModuleId(value as u32))
                            .copied()
                    })
                    .flatten()
            })
            .collect();
        workspace.canonicalize(&source_modules)?;
        let mut header: Vec<_> = references
            .iter()
            .filter(|(identity, reference)| {
                identity.space() != "expression" || reference.owner != input
            })
            .map(|(identity, reference)| {
                (
                    relocation
                        .lookup(identity)
                        .expect("all exported IDs normalized")
                        .clone(),
                    *reference,
                )
            })
            .collect();
        drop(relocation);
        header.sort_by(|(a, _), (b, _)| a.cmp(b));
        let serialization_phase = crate::profiling::Phase::start("artifact.serialize");
        let resolver_bytes = artifact::canonical::to_vec_detailed(
            &ResolverObject {
                version: 3,
                owner,
                input,
                dependencies: exact_dependencies,
                pending: self.pending,
                completed_steps: self
                    .steps
                    .checked_sub(boundary.steps)
                    .ok_or_else(|| Error("invalid checkpoint step boundary".into()))?,
                checked_steps: self
                    .completed
                    .range(boundary.steps..)
                    .map(|step| step - boundary.steps)
                    .collect(),
                references: header,
                resolver,
            },
            MAX_PACKAGE_BYTES,
        )
        .map_err(|error| Error(format!("resolver artifact serialization: {error}")))?;
        let environment = artifact::canonical::to_vec_detailed(&workspace, MAX_PACKAGE_BYTES)
            .map_err(|error| Error(format!("workspace artifact serialization: {error}")))?;
        drop(workspace);
        drop(serialization_phase);
        if !self.pending {
            // Validate the delta before publication. Cloning the catalog copies
            // the identities of every dependency at each package boundary.
            let mut additions = BTreeMap::new();
            for (runtime, reference) in &references {
                let previous = catalog
                    .portable
                    .get(reference)
                    .or_else(|| additions.insert(*reference, runtime));
                if previous.is_some_and(|old| old != runtime) {
                    return Err(Error(
                        "package identity registered with conflicting runtime ID".into(),
                    ));
                }
            }
            drop(additions);
            for (runtime, reference) in references {
                if reference.owner == input {
                    catalog.sources.insert(reference, owner);
                }
                catalog.register(reference, runtime)?;
            }
            catalog.packages.insert(owner);
            catalog.dependencies.insert(input, dependencies);
            snapshots.commit();
        }
        Ok(PackageArtifact {
            resolver: resolver_bytes,
            environment,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_references_reconstruct_the_complete_identity_catalog() {
        let mut checker = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        let artifact = export(&mut checker, &mut catalog, A, 1);
        let resolver: ResolverObject = postcard::from_bytes(&artifact.resolver).unwrap();
        let workspace: crate::elaborator::exports::Export =
            postcard::from_bytes(&artifact.environment).unwrap();
        assert!(!workspace.graph.nodes.is_empty());
        assert!(
            resolver
                .references
                .iter()
                .all(|(id, _)| id.space() != "expression")
        );
        let mut references = resolver.references;
        identity::restore_expression_references(&workspace.graph, resolver.input, &mut references)
            .unwrap();
        assert_eq!(
            references
                .iter()
                .map(|(_, reference)| *reference)
                .collect::<BTreeSet<_>>(),
            catalog.portable.keys().copied().collect(),
        );
        // A duplicate graph entry must not silently change the catalog.
        let mut graph = workspace.graph;
        graph.nodes.push(graph.nodes[0].clone());
        let mut header = references
            .into_iter()
            .filter(|(id, _)| id.space() != "expression")
            .collect();
        assert!(
            identity::restore_expression_references(&graph, resolver.input, &mut header).is_err()
        );
    }

    const A: &str = r"\module A {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \definition identity[x: Nat]: Nat := x;
        \macro identity($x) := $x;
        \module Box(T: \Set) { \definition apply[x: T]: T := x; }
    }";
    const NOISE: &str = r"\module Noise {
        \definition proof[P: \Prop][p: P]: P := p;
    }";
    const B: &str = r"\module B {
        \import \root.A[] \as A;
        \import \root.A[].Box[T := A.Nat] \as Box;
        \definition b: A.Nat := A.identity A.Nat::zero;
        \definition boxed: A.Nat := Box.apply b;
    }";
    const C: &str = r"\module C {
        \import \root.A[] \as A;
        \import \root.A[].Box[T := A.Nat] \as Box;
        \use A.identity \as identity;
        \definition c: A.Nat := identity!{A.Nat::zero};
        \definition boxed: A.Nat := Box.apply c;
    }";
    fn append(checker: &mut PackageChecker, source: &str) {
        let module = syntax::parse::str_parse_modules(source).unwrap().remove(0);
        checker.append(&module, |_| {}).unwrap();
    }
    fn export(
        checker: &mut PackageChecker,
        catalog: &mut ArtifactCatalog,
        source: &str,
        key: u8,
    ) -> PackageArtifact {
        let boundary = checker.artifact_boundary();
        append(checker, source);
        checker
            .export_artifact([key; 32], &boundary, catalog)
            .unwrap()
    }
    #[test]
    fn query_output_order_survives_import_and_resume_across_varint_boundaries() {
        let mut text = r"\module Queries { \inductive Unit: \Set := | unit: Unit;".to_string();
        text.extend(std::iter::repeat_n(' ', 250 - text.len()));
        text.push_str(r"\infer Unit;");
        text.extend(std::iter::repeat_n(' ', 270 - text.len()));
        text.push_str(r"\infer Unit::unit; \module Later { \infer Unit; } }");
        let source = Arc::new(SourceFile {
            id: SourceId("/artifact-query-order.ref".into()),
            text,
        });
        let mut module = syntax::parse::str_parse_modules(&source.text)
            .unwrap()
            .remove(0);
        fn attach(module: &mut syntax::syntax::Module, source: &Arc<SourceFile>) {
            module.source = Some(source.clone());
            module.header_source = Some(source.clone());
            if let syntax::syntax::ModuleBody::Inline(items) = &mut module.body {
                for item in items {
                    if let syntax::syntax::ModuleItem::ChildModule { module } = item {
                        attach(module, source);
                    }
                }
            }
        }
        attach(&mut module, &source);
        let observations = |checker: &PackageChecker| {
            checker
                .analysis()
                .outputs
                .iter()
                .map(|output| {
                    (
                        output.module.clone(),
                        output.location.span.start,
                        output.text.clone(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut cold = PackageChecker::default();
        let boundary = cold.artifact_boundary();
        let mut checkpoints = Vec::new();
        cold.append_with_checkpoints(&module, Some(Duration::ZERO), |event| {
            if let PackageProgress::Checkpoint { bytes, .. } = event {
                checkpoints.push(bytes.unwrap());
            }
        })
        .unwrap();
        let analysis = |checker: &PackageChecker| {
            let value = checker.analysis();
            let declarations = value
                .declarations
                .iter()
                .map(|d| {
                    (
                        d.module.clone(),
                        d.name.clone(),
                        d.location.span.start,
                        d.ty.clone(),
                    )
                })
                .collect::<Vec<_>>();
            let references = value
                .references
                .iter()
                .map(|r| {
                    (
                        r.module.clone(),
                        r.location.span.start,
                        r.target_module.clone(),
                        r.target_name.clone(),
                    )
                })
                .collect::<Vec<_>>();
            (declarations, references)
        };
        let expected_analysis = analysis(&cold);
        assert!(!expected_analysis.0.is_empty());
        assert!(!expected_analysis.1.is_empty());
        let expected = observations(&cold);
        assert_eq!(expected.len(), 3);
        assert_eq!(expected[0].1, 250);
        assert_eq!(expected[1].1, 270);
        let artifact = cold
            .export_artifact([83; 32], &boundary, &mut ArtifactCatalog::default())
            .unwrap();
        let (imported, _) = PackageChecker::default()
            .import_artifact_owned(&artifact, ArtifactCatalog::default(), |_| {
                Some(source.clone())
            })
            .unwrap();
        assert_eq!(observations(&imported), expected);
        assert_eq!(analysis(&imported), expected_analysis);
        assert!(!checkpoints.is_empty());
        for checkpoint in checkpoints {
            let pending = PackageChecker::restore(&checkpoint, |_| Some(source.clone())).unwrap();
            let artifact = pending
                .export_resume([83; 32], &boundary, &mut ArtifactCatalog::default())
                .unwrap();
            let (mut resumed, _) = PackageChecker::default()
                .import_resume_owned(&artifact, ArtifactCatalog::default(), |_| {
                    Some(source.clone())
                })
                .unwrap();
            resumed.append(&module, |_| {}).unwrap();
            assert_eq!(observations(&resumed), expected);
            assert_eq!(analysis(&resumed), expected_analysis);
        }
    }

    #[test]
    fn temporary_checkpoints_release_snapshots_and_failed_exports_roll_back() {
        let mut checker = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        export(&mut checker, &mut catalog, A, 1);
        let boundary = checker.artifact_boundary();
        append(&mut checker, B);
        let baseline = checker.workspace.crate_env.snapshot_count();
        let pending = State {
            resolution: &checker.resolution,
            workspace: &checker.workspace,
            steps: checker.steps,
            pending: true,
            completed: &checker.completed,
        };
        let mut first: Option<PackageArtifact> = None;
        for _ in 0..32 {
            let artifact = pending
                .export_package_state([2; 32], [2; 32], &boundary, &mut catalog)
                .unwrap();
            assert_eq!(checker.workspace.crate_env.snapshot_count(), baseline);
            assert!(!catalog.contains(&[2; 32]));
            if let Some(previous) = &first {
                assert!(previous.environment == artifact.environment);
            } else {
                first = Some(artifact);
            }
        }
        let invalid = State {
            steps: 0,
            pending: false,
            ..pending
        };
        assert!(
            invalid
                .export_package_state([2; 32], [2; 32], &boundary, &mut catalog)
                .is_err()
        );
        assert_eq!(checker.workspace.crate_env.snapshot_count(), baseline);
        checker
            .export_artifact([2; 32], &boundary, &mut catalog)
            .unwrap();
        assert!(catalog.contains(&[2; 32]));
        assert!(checker.workspace.crate_env.snapshot_count() > baseline);
    }

    #[test]
    fn portable_package_objects_join_independent_diamond_branches() {
        let mut origin = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        let a = export(&mut origin, &mut catalog, A, 1);
        let b = export(&mut origin, &mut catalog, B, 2);
        let mut alternate = PackageChecker::default();
        let mut alternate_catalog = ArtifactCatalog::default();
        export(&mut alternate, &mut alternate_catalog, NOISE, 4);
        alternate
            .import_artifact(&a, &mut alternate_catalog, |_| None)
            .unwrap();
        let c = export(&mut alternate, &mut alternate_catalog, C, 3);
        let mut target = PackageChecker::default();
        let mut target_catalog = ArtifactCatalog::default();
        for artifact in [&a, &c, &b] {
            (target, target_catalog) = target
                .import_artifact_owned(artifact, target_catalog, |_| None)
                .unwrap();
        }
        append(
            &mut target,
            r"\module D {
            \import \root.A[] \as A;
            \import \root.B[] \as B;
            \import \root.C[] \as C;
            \definition left: A.Nat := B.b;
            \definition right: A.Nat := C.c;
        }",
        );
        assert_eq!(target.resolution.project().modules.len(), 4);
    }
    #[test]
    fn exports_are_identical_after_unrelated_package_allocations() {
        let mut direct = PackageChecker::default();
        let mut direct_catalog = ArtifactCatalog::default();
        let a = export(&mut direct, &mut direct_catalog, A, 1);
        let mut shifted = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        export(&mut shifted, &mut catalog, NOISE, 4);
        let shifted_a = export(&mut shifted, &mut catalog, A, 1);
        assert!(
            a.resolver == shifted_a.resolver,
            "resolver objects differ after unrelated allocations"
        );
        assert!(
            a.environment == shifted_a.environment,
            "environment objects differ after unrelated allocations"
        );
        let c = export(&mut direct, &mut direct_catalog, C, 3);
        let shifted_c = export(&mut shifted, &mut catalog, C, 3);
        assert!(
            c.resolver == shifted_c.resolver,
            "dependency references must be independent of unrelated interned nodes"
        );
        assert!(
            c.environment == shifted_c.environment,
            "shared primitive ownership must be chosen from actual dependencies"
        );
    }
    #[test]
    fn package_checkpoint_resumes_after_dependency_relocation() {
        let source = r"\module Pending {
            \module First { \import \root.A[] \as A; \definition x: A.Nat := A.Nat::zero; }
            \module Second { \import \root.A[] \as A; \definition y: A.Nat := A.Nat::zero; }
        }";
        let module = syntax::parse::str_parse_modules(source).unwrap().remove(0);
        let mut original = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        let a = export(&mut original, &mut catalog, A, 1);
        let boundary = original.artifact_boundary();
        let mut checkpoints = Vec::new();
        original
            .append_with_checkpoints(&module, Some(Duration::ZERO), |event| {
                if let PackageProgress::Checkpoint {
                    bytes: Ok(bytes), ..
                } = event
                {
                    checkpoints.push(bytes);
                }
            })
            .unwrap();
        assert!(!checkpoints.is_empty());
        let mut legacy = Vec::new();
        for checkpoint in checkpoints {
            let pending = PackageChecker::restore(&checkpoint, |_| None).unwrap();
            let artifact = pending
                .export_resume([9; 32], &boundary, &mut catalog.clone())
                .unwrap();
            legacy.push(artifact);
        }
        let (mut direct, mut direct_catalog) = PackageChecker::default()
            .import_artifact_owned(&a, ArtifactCatalog::default(), |_| None)
            .unwrap();
        let direct_boundary = direct.artifact_boundary();
        let mut checkpoints = Vec::new();
        direct
            .append_selected_with_artifact_checkpoints(
                &module,
                &BTreeSet::from([
                    vec!["Pending".into(), "First".into()],
                    vec!["Pending".into(), "Second".into()],
                ]),
                Some(Duration::ZERO),
                [9; 32],
                [9; 32],
                &direct_boundary,
                &mut direct_catalog,
                |event| {
                    if let PackageProgress::ArtifactCheckpoint { artifact, .. } = event {
                        checkpoints.push(artifact.unwrap());
                    }
                },
            )
            .unwrap();
        assert_eq!(legacy.len(), checkpoints.len());
        for (expected, artifact) in legacy.iter().zip(&checkpoints) {
            assert!(
                expected.resolver == artifact.resolver,
                "borrowed checkpoint resolver differs"
            );
            assert!(
                expected.environment == artifact.environment,
                "borrowed checkpoint environment differs"
            );
        }
        for artifact in checkpoints {
            let mut target = PackageChecker::default();
            let mut target_catalog = ArtifactCatalog::default();
            export(&mut target, &mut target_catalog, NOISE, 4);
            target
                .import_artifact(&a, &mut target_catalog, |_| None)
                .unwrap();
            let target_boundary = target.artifact_boundary();
            target
                .import_resume(&artifact, &mut target_catalog, |_| None)
                .unwrap();
            assert!(target.is_pending());
            target.append(&module, |_| {}).unwrap();
            assert!(!target.is_pending());
            target
                .export_artifact([9; 32], &target_boundary, &mut target_catalog)
                .unwrap();
        }
    }

    #[test]
    fn partial_artifacts_merge_in_both_orders_and_keep_missing_scopes_pending() {
        let source = r"\module Parts {
            \inductive T: \Set := | zero: T;
            \module Box(A: \Set) { \definition apply[x: A]: A := x; }
            \import Box[A := T] \as Common;
            \module Left { \definition left: T := Common.apply T::zero; }
            \module Right {
                \import \root.Parts[].Box[A := T] \as Extra;
                \definition right: T := Extra.apply T::zero;
            }
            \module Later { \definition later: T := Common.apply T::zero; }
        }";
        let module = syntax::parse::str_parse_modules(source).unwrap().remove(0);
        let make = |name: &str, owner: u8| {
            let mut checker = PackageChecker::default();
            let boundary = checker.artifact_boundary();
            let paths = BTreeSet::from([
                vec!["Parts".into(), name.into()],
                vec!["Parts".into(), "Box".into()],
            ]);
            checker
                .append_selected_with_checkpoints(&module, &paths, None, |_| {})
                .unwrap();
            checker
                .export_artifact_for_input(
                    [owner; 32],
                    [8; 32],
                    &boundary,
                    &mut ArtifactCatalog::default(),
                )
                .unwrap()
        };
        let left = make("Left", 5);
        let right = make("Right", 6);
        let (mut earlier, mut earlier_catalog) = PackageChecker::default()
            .import_artifact_owned(&left, ArtifactCatalog::default(), |_| None)
            .unwrap();
        let consumer = export(
            &mut earlier,
            &mut earlier_catalog,
            r"\module Uses {
            \import \root.Parts[] \as P;
            \import \root.Parts[].Left[] \as Left;
            \definition value: P.T := Left.left;
        }",
            10,
        );
        for partials in [[&left, &right], [&right, &left]] {
            let mut target = PackageChecker::default();
            let mut target_catalog = ArtifactCatalog::default();
            for partial in partials {
                (target, target_catalog) = target
                    .import_artifact_owned(partial, target_catalog, |_| None)
                    .unwrap();
            }
            (target, target_catalog) = target
                .import_artifact_owned(&consumer, target_catalog, |_| None)
                .unwrap();
            assert!(target_catalog.contains(&[10; 32]));
            append(
                &mut target,
                r"\module Last {
                \import \root.Parts[] \as P;
                \import \root.Uses[] \as U;
                \definition value: P.T := U.value;
            }",
            );
        }
        let mut interleaved = PackageChecker::default();
        let mut interleaved_catalog = ArtifactCatalog::default();
        interleaved
            .import_artifact(&left, &mut interleaved_catalog, |_| None)
            .unwrap();
        export(&mut interleaved, &mut interleaved_catalog, NOISE, 4);
        interleaved
            .import_artifact(&right, &mut interleaved_catalog, |_| None)
            .unwrap();
        assert_eq!(
            interleaved.steps,
            interleaved.resolution.project().order.len()
        );
        let mut unions: Vec<PackageArtifact> = Vec::new();
        for artifacts in [[&left, &right], [&right, &left]] {
            let mut checker = PackageChecker::default();
            let boundary = checker.artifact_boundary();
            let mut catalog = ArtifactCatalog::default();
            for artifact in artifacts {
                checker
                    .import_artifact(artifact, &mut catalog, |_| None)
                    .unwrap();
            }
            let both = BTreeSet::from([
                vec!["Parts".into(), "Left".into()],
                vec!["Parts".into(), "Right".into()],
            ]);
            let mut checked = 0;
            checker
                .append_selected_with_checkpoints(&module, &both, None, |event| {
                    if matches!(event, PackageProgress::Step(CheckStepProgress::Started(_))) {
                        checked += 1;
                    }
                })
                .unwrap();
            assert_eq!(checked, 0, "already verified scopes must be shared");
            let union = checker
                .export_artifact_for_input([7; 32], [8; 32], &boundary, &mut catalog)
                .unwrap();
            assert!(union.dependencies().unwrap().is_empty());
            if let Some(previous) = unions.first() {
                assert!(
                    previous.resolver == union.resolver,
                    "resolver bytes depend on partial import order"
                );
                assert!(
                    previous.environment == union.environment,
                    "environment bytes depend on partial import order"
                );
            }
            unions.push(union.clone());
            let mut restored = PackageChecker::default();
            restored
                .import_artifact(&union, &mut ArtifactCatalog::default(), |_| None)
                .unwrap();
            let mut later = 0;
            restored
                .append_selected_with_checkpoints(
                    &module,
                    &BTreeSet::from([vec!["Parts".into(), "Later".into()]]),
                    None,
                    |event| {
                        if matches!(event, PackageProgress::Step(CheckStepProgress::Started(_))) {
                            later += 1;
                        }
                    },
                )
                .unwrap();
            assert!(later > 0, "uncovered scopes must remain pending");
        }
    }
}

#[path = "package_identity.rs"]
mod identity;
