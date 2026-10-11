//! Package-owned declarations and the shared raw/kernel expression graph.
//!
//! IDs in an export are explicit handles. The package layer assigns their
//! persistent identities, supplies dependency mappings, and relocates metadata
//! after reserving declarations and importing the expression graph.
use crate::{
    environment::{Datatype, Definition, Environment, InductiveSpec},
    ids::{DefinitionId, InductiveId, ParameterId, ProgramInductiveId},
    syntax::{Arena, Expression, Node},
};
use artifact::{Error, Identity, Relocate, Relocation, Result};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeSet;

/// Raw declaration atoms share the arena's Meta node representation. Allocate
/// fresh sessions for those owned atoms while keeping mapped dependency atoms.
pub fn reserve_metas(
    relocation: &mut Relocation,
    identities: impl IntoIterator<Item = artifact::Identity>,
) -> Result<()> {
    let mut sessions = rustc_hash::FxHashMap::default();
    for identity in identities {
        if let artifact::Identity::Pair {
            space,
            arena,
            index,
        } = identity
            && space == "meta"
            && relocation.get_pair("meta", (arena, index)).is_none()
        {
            let session = *sessions
                .entry(arena)
                .or_insert_with(crate::ids::fresh_identity);
            relocation.insert_pair("meta", (arena, index), (session, index))?;
        }
    }
    Ok(())
}

/// Declaration ownership boundary. Bodies and arena nodes are never copied.
#[derive(Debug, Clone)]
pub struct Boundary {
    identity: u64,
    definitions: usize,
    parameters: FxHashSet<ParameterId>,
    inductives: FxHashSet<InductiveId>,
    datatypes: FxHashSet<ProgramInductiveId>,
    reflected: FxHashSet<DefinitionId>,
    program_parameters: FxHashSet<DefinitionId>,
}

/// Only declarations created after a package's ownership boundary.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Relocate)]
pub struct EnvironmentExport {
    pub definitions: Vec<(DefinitionId, Definition)>,
    pub parameters: Vec<(ParameterId, Expression)>,
    pub inductives: Vec<(InductiveId, InductiveSpec)>,
    pub datatypes: Vec<(ProgramInductiveId, Datatype)>,
    pub reflected: Vec<(DefinitionId, DefinitionId)>,
    pub program_parameters: Vec<(DefinitionId, Vec<bool>)>,
}

/// One node per reachable expression, ordered with children before parents.
/// Imported dependency nodes remain external references.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Relocate)]
pub struct ExpressionGraph {
    pub nodes: Vec<(Expression, Node)>,
}

enum Metadata<'a> {
    Definition(&'a Definition),
    Parameter(&'a Expression),
    Inductive(&'a InductiveSpec),
    Datatype(&'a Datatype),
}

/// Reuse this traversal across frontend/kernel reachability fixed points.
/// Each owned declaration and expression node is inspected at most once.
pub struct Reachability<'a> {
    arena: &'a Arena,
    metadata: FxHashMap<Identity, Metadata<'a>>,
    reflections: FxHashMap<Identity, Vec<Identity>>,
    visited: FxHashSet<Identity>,
}

fn definition_identity(id: DefinitionId) -> Identity {
    Identity::pair("definition", (id.arena, id.index))
}

impl Reachability<'_> {
    pub fn extend(
        &mut self,
        reachable: &mut BTreeSet<Identity>,
        external: &mut impl FnMut(Expression) -> bool,
    ) -> Result<()> {
        fn collect<T: Clone + Relocate>(value: &T) -> Result<BTreeSet<Identity>> {
            let mut collector = Relocation::collecting();
            value.clone().relocate(&mut collector)?;
            Ok(collector.into_identities())
        }
        let mut pending: Vec<_> = reachable
            .iter()
            .filter(|id| !self.visited.contains(*id))
            .cloned()
            .collect();
        while let Some(id) = pending.pop() {
            if !self.visited.insert(id.clone()) {
                continue;
            }
            let mut references = match self.metadata.get(&id) {
                Some(Metadata::Definition(value)) => collect(*value)?,
                Some(Metadata::Parameter(value)) => collect(*value)?,
                Some(Metadata::Inductive(value)) => collect(*value)?,
                Some(Metadata::Datatype(value)) => collect(*value)?,
                None => BTreeSet::new(),
            };
            if let Some(reflections) = self.reflections.get(&id) {
                references.extend(reflections.iter().cloned());
            }
            if let Identity::Scalar { space, value } = &id
                && space == "expression"
            {
                let expression = Expression::from_index(
                    u32::try_from(*value)
                        .map_err(|_| Error("expression identity overflow".into()))?,
                );
                if !external(expression) {
                    if !self.arena.is_live(expression) {
                        return Err(Error("invalid reachable expression".into()));
                    }
                    references.extend(collect(self.arena.read(expression).as_ref())?);
                }
            }
            for reference in references {
                if reachable.insert(reference.clone()) {
                    pending.push(reference);
                }
            }
        }
        Ok(())
    }
}

impl Environment {
    pub fn boundary(&self) -> Boundary {
        Boundary {
            identity: self.identity,
            definitions: self.definitions.len(),
            parameters: self.parameters.keys().copied().collect(),
            inductives: self.inductives.keys().copied().collect(),
            datatypes: self.datatypes.keys().copied().collect(),
            reflected: self.reflected.keys().copied().collect(),
            program_parameters: self.program_parameters.keys().copied().collect(),
        }
    }

    pub fn export_since(&self, boundary: &Boundary) -> Result<EnvironmentExport> {
        if self.identity != boundary.identity || boundary.definitions > self.definitions.len() {
            return Err(Error(
                "kernel ownership boundary belongs to another environment".into(),
            ));
        }
        let mut export = EnvironmentExport {
            definitions: self
                .definitions
                .iter()
                .enumerate()
                .skip(boundary.definitions)
                .map(|(index, definition)| {
                    (
                        DefinitionId {
                            arena: self.identity,
                            index: index as u32,
                        },
                        definition.clone(),
                    )
                })
                .collect(),
            parameters: self
                .parameters
                .iter()
                .filter(|(id, _)| !boundary.parameters.contains(id))
                .map(|(id, ty)| (*id, *ty))
                .collect(),
            inductives: self
                .inductives
                .iter()
                .filter(|(id, _)| !boundary.inductives.contains(id))
                .map(|(id, spec)| (*id, spec.clone()))
                .collect(),
            datatypes: self
                .datatypes
                .iter()
                .filter(|(id, _)| !boundary.datatypes.contains(id))
                .map(|(id, spec)| (*id, spec.clone()))
                .collect(),
            reflected: self
                .reflected
                .iter()
                .filter(|(id, _)| !boundary.reflected.contains(id))
                .map(|(id, reflected)| (*id, *reflected))
                .collect(),
            program_parameters: self
                .program_parameters
                .iter()
                .filter(|(id, _)| !boundary.program_parameters.contains(id))
                .map(|(id, modes)| (*id, modes.clone()))
                .collect(),
        };
        export.parameters.sort_by_key(|(id, _)| id.0);
        export.inductives.sort_by_key(|(id, _)| id.0);
        export.datatypes.sort_by_key(|(id, _)| id.0);
        export.reflected.sort_by_key(|(id, _)| (id.arena, id.index));
        export
            .program_parameters
            .sort_by_key(|(id, _)| (id.arena, id.index));
        for root in export.expression_roots() {
            if !self.arena.is_live(root) || self.arena.contains_meta(root) {
                return Err(Error(
                    "unfinished kernel declaration in package export".into(),
                ));
            }
        }
        Ok(export)
    }

    /// Publish relocated metadata after validating every reference. Failure
    /// leaves the environment's declarations and caches unchanged.
    pub fn import_export(&mut self, export: EnvironmentExport) -> Result<()> {
        export.validate(self)?;
        for (id, value) in export.definitions {
            if id.index as usize == self.definitions.len() {
                self.definitions.push(value);
            }
        }
        self.parameters.extend(export.parameters);
        self.inductives.extend(export.inductives);
        self.datatypes.extend(export.datatypes);
        self.reflected.extend(export.reflected);
        self.program_parameters.extend(export.program_parameters);
        Ok(())
    }
}

impl EnvironmentExport {
    pub fn reachability<'a>(&'a self, arena: &'a Arena) -> Reachability<'a> {
        let mut metadata = FxHashMap::default();
        for (id, value) in &self.definitions {
            metadata.insert(definition_identity(*id), Metadata::Definition(value));
        }
        for (id, value) in &self.parameters {
            metadata.insert(
                Identity::scalar("parameter", id.0),
                Metadata::Parameter(value),
            );
        }
        for (id, value) in &self.inductives {
            metadata.insert(
                Identity::scalar("inductive", id.0),
                Metadata::Inductive(value),
            );
        }
        for (id, value) in &self.datatypes {
            metadata.insert(
                Identity::scalar("datatype", id.0),
                Metadata::Datatype(value),
            );
        }
        let mut reflections: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for (source, reflected) in &self.reflected {
            let source = definition_identity(*source);
            let reflected = definition_identity(*reflected);
            reflections
                .entry(source.clone())
                .or_default()
                .push(reflected.clone());
            reflections.entry(reflected).or_default().push(source);
        }
        Reachability {
            arena,
            metadata,
            reflections,
            visited: FxHashSet::default(),
        }
    }

    pub fn reachable(
        &self,
        arena: &Arena,
        roots: &BTreeSet<Identity>,
        external: &mut impl FnMut(Expression) -> bool,
    ) -> Result<BTreeSet<Identity>> {
        let mut reachable = roots.clone();
        self.reachability(arena).extend(&mut reachable, external)?;
        Ok(reachable)
    }

    pub fn retain_reachable(&mut self, reachable: &BTreeSet<Identity>) {
        self.definitions
            .retain(|(id, _)| reachable.contains(&definition_identity(*id)));
        self.parameters
            .retain(|(id, _)| reachable.contains(&Identity::scalar("parameter", id.0)));
        self.inductives
            .retain(|(id, _)| reachable.contains(&Identity::scalar("inductive", id.0)));
        self.datatypes
            .retain(|(id, _)| reachable.contains(&Identity::scalar("datatype", id.0)));
        self.reflected
            .retain(|(id, _)| reachable.contains(&definition_identity(*id)));
        self.program_parameters
            .retain(|(id, _)| reachable.contains(&definition_identity(*id)));
    }

    /// Order keyed tables after their IDs have been normalized for storage.
    pub fn canonicalize(&mut self) {
        self.definitions.sort_by_key(|(id, _)| (id.arena, id.index));
        self.parameters.sort_by_key(|(id, _)| id.0);
        self.inductives.sort_by_key(|(id, _)| id.0);
        self.datatypes.sort_by_key(|(id, _)| id.0);
        self.reflected.sort_by_key(|(id, _)| (id.arena, id.index));
        self.program_parameters
            .sort_by_key(|(id, _)| (id.arena, id.index));
    }

    pub fn expression_roots(&self) -> Vec<Expression> {
        let mut roots = Vec::new();
        for (_, definition) in &self.definitions {
            roots.extend([definition.ty, definition.body]);
            roots.extend(definition.context.iter().map(|binding| binding.ty));
        }
        roots.extend(self.parameters.iter().map(|(_, ty)| *ty));
        for (_, spec) in &self.inductives {
            roots.push(spec.arity);
            roots.extend(&spec.constructors);
            roots.extend(spec.parameters.iter().map(|binding| binding.ty));
        }
        for (_, datatype) in &self.datatypes {
            roots.extend(datatype.parameters.iter().map(|binding| binding.ty));
            for fields in &datatype.constructors {
                roots.extend(fields.iter().map(|binding| binding.ty));
            }
        }
        roots
    }

    /// Reserve all mutually referring definitions before importing any nodes.
    pub fn reserve_definitions(
        &self,
        destination: &Environment,
        relocation: &mut Relocation,
    ) -> Result<()> {
        // A reflected definition has the same stable owner as its source.
        // Partial exports may pre-map only the raw source declaration.
        for (source, reflected) in &self.reflected {
            if let Some((arena, index)) =
                relocation.get_pair("definition", (source.arena, source.index))
                && let Some(target) = destination.reflected.get(&DefinitionId { arena, index })
            {
                relocation.insert_pair(
                    "definition",
                    (reflected.arena, reflected.index),
                    (target.arena, target.index),
                )?;
            }
        }
        let mut seen = FxHashSet::default();
        let mut next = destination.definitions.len();
        for (id, _) in &self.definitions {
            if !seen.insert(*id) {
                return Err(Error("duplicate exported definition identity".into()));
            }
            if let Some((arena, index)) = relocation.get_pair("definition", (id.arena, id.index)) {
                if arena != destination.identity || index as usize > next {
                    return Err(Error("invalid existing definition reservation".into()));
                }
                if index as usize == next {
                    next += 1;
                }
            } else {
                let index = u32::try_from(next)
                    .map_err(|_| Error("definition identity overflow".into()))?;
                relocation.insert_pair(
                    "definition",
                    (id.arena, id.index),
                    (destination.identity, index),
                )?;
                next += 1;
            }
        }
        Ok(())
    }

    /// Supply fresh nominal identities for declarations not already mapped by
    /// the frontend. Existing mappings are shared with raw module identities.
    pub fn reserve_nominals(
        &self,
        destination: &Environment,
        relocation: &mut Relocation,
    ) -> Result<()> {
        for (space, ids, occupied) in [
            (
                "inductive",
                self.inductives
                    .iter()
                    .map(|(id, _)| id.0)
                    .collect::<Vec<_>>(),
                destination
                    .inductives
                    .keys()
                    .map(|id| id.0)
                    .collect::<FxHashSet<_>>(),
            ),
            (
                "datatype",
                self.datatypes.iter().map(|(id, _)| id.0).collect(),
                destination.datatypes.keys().map(|id| id.0).collect(),
            ),
            (
                "parameter",
                self.parameters.iter().map(|(id, _)| id.0).collect(),
                destination.parameters.keys().map(|id| id.0).collect(),
            ),
        ] {
            let mut reserved = occupied;
            let mut seen = FxHashSet::default();
            let mut targets = FxHashSet::default();
            for id in ids {
                if !seen.insert(id) {
                    return Err(Error(format!("duplicate exported {space} identity")));
                }
                let new = match relocation.id(space, id) {
                    Ok(id) => id,
                    Err(_) => {
                        let mut fresh = crate::ids::fresh_identity();
                        while reserved.contains(&fresh) {
                            fresh = crate::ids::fresh_identity();
                        }
                        relocation.insert(space, id, fresh)?;
                        fresh
                    }
                };
                reserved.insert(new);
                if !targets.insert(new) {
                    return Err(Error(format!("duplicate imported {space} identity")));
                }
            }
        }
        Ok(())
    }

    fn validate(&self, destination: &Environment) -> Result<()> {
        let mut definitions = rustc_hash::FxHashMap::default();
        let mut end = destination.definitions.len();
        for (id, value) in &self.definitions {
            if id.arena != destination.identity || definitions.insert(*id, value).is_some() {
                return Err(Error("invalid reserved definition identity".into()));
            }
            if (id.index as usize) < destination.definitions.len() {
                if &destination.definitions[id.index as usize] != value {
                    return Err(Error("overlapping definition contents disagree".into()));
                }
            } else {
                if id.index as usize != end {
                    return Err(Error("invalid reserved definition order".into()));
                }
                end += 1;
            }
        }
        let valid_definition =
            |id: DefinitionId| id.arena == destination.identity && (id.index as usize) < end;
        fn validate_entries<T: Copy + Eq + std::hash::Hash, V: PartialEq>(
            entries: &[(T, V)],
            existing: &rustc_hash::FxHashMap<T, V>,
        ) -> Result<FxHashSet<T>> {
            let mut seen = FxHashSet::default();
            for (id, value) in entries {
                if !seen.insert(*id) {
                    return Err(Error("duplicate imported nominal identity".into()));
                }
                if existing.get(id).is_some_and(|previous| previous != value) {
                    return Err(Error(
                        "overlapping nominal declaration contents disagree".into(),
                    ));
                }
            }
            Ok(seen)
        }
        let parameters = validate_entries(&self.parameters, &destination.parameters)?;
        let inductives = validate_entries(&self.inductives, &destination.inductives)?;
        let datatypes = validate_entries(&self.datatypes, &destination.datatypes)?;
        let valid_inductive =
            |id: InductiveId| inductives.contains(&id) || destination.inductives.contains_key(&id);
        let valid_datatype = |id: ProgramInductiveId| {
            datatypes.contains(&id) || destination.datatypes.contains_key(&id)
        };
        let mut mirrors: FxHashSet<_> = destination
            .datatypes
            .values()
            .map(|datatype| datatype.reflected)
            .collect();
        for (id, datatype) in &self.datatypes {
            if !valid_inductive(datatype.reflected) {
                return Err(Error("missing reflected inductive".into()));
            }
            if !destination.datatypes.contains_key(id) && !mirrors.insert(datatype.reflected) {
                return Err(Error("duplicate datatype mirror identity".into()));
            }
        }
        let mut reflection_keys = FxHashSet::default();
        for (id, reflected) in &self.reflected {
            if !valid_definition(*id)
                || !valid_definition(*reflected)
                || destination
                    .reflected
                    .get(id)
                    .is_some_and(|old| old != reflected)
                || !reflection_keys.insert(*id)
            {
                return Err(Error("invalid reflected definition".into()));
            }
        }
        let mut mode_keys = FxHashSet::default();
        for (id, modes) in &self.program_parameters {
            if !valid_definition(*id)
                || destination
                    .program_parameters
                    .get(id)
                    .is_some_and(|old| old != modes)
                || !mode_keys.insert(*id)
            {
                return Err(Error("invalid Program parameter modes".into()));
            }
            let definition = if (id.index as usize) < destination.definitions.len() {
                &destination.definitions[id.index as usize]
            } else {
                definitions[id]
            };
            if modes.len() != definition.context.len() {
                return Err(Error("invalid Program parameter mode count".into()));
            }
        }
        if reflection_keys != mode_keys {
            return Err(Error(
                "reflected definition and parameter mode tables disagree".into(),
            ));
        }
        let mut pending = self.expression_roots();
        let mut visited = FxHashSet::default();
        while let Some(expression) = pending.pop() {
            if !visited.insert(expression) {
                continue;
            }
            if !destination.arena.is_live(expression) {
                return Err(Error("invalid imported expression reference".into()));
            }
            let node = destination.arena.read(expression);
            let valid = match node.as_ref() {
                Node::Meta { .. } => false,
                Node::Definition { id, .. } => valid_definition(*id),
                Node::Parameter(id) => {
                    parameters.contains(id) || destination.parameters.contains_key(id)
                }
                Node::IndType { inductive, .. }
                | Node::IndCtor { inductive, .. }
                | Node::IndElim { inductive, .. }
                | Node::Case { inductive, .. } => valid_inductive(*inductive),
                Node::Inductive { inductive, .. }
                | Node::InductiveConstructor { inductive, .. }
                | Node::SetCase { inductive, .. }
                | Node::ProgramCase { inductive, .. } => valid_datatype(*inductive),
                _ => true,
            };
            if !valid {
                return Err(Error(
                    "invalid imported kernel declaration reference".into(),
                ));
            }
            node.try_for_each_child(|child, _| {
                pending.push(child);
                Ok(())
            })?;
        }
        Ok(())
    }
}

impl Arena {
    /// Traverse shared roots once. A dependency-owned expression is referenced
    /// externally and neither it nor its children are copied into this graph.
    pub fn export_graph(
        &self,
        roots: impl IntoIterator<Item = Expression>,
        mut is_external: impl FnMut(Expression) -> bool,
    ) -> Result<ExpressionGraph> {
        let mut visited = FxHashSet::default();
        let mut nodes = Vec::new();
        for root in roots {
            let mut pending = vec![(root, false)];
            while let Some((expression, expanded)) = pending.pop() {
                if expanded {
                    nodes.push((expression, self.get(expression)));
                    continue;
                }
                if !visited.insert(expression) || is_external(expression) {
                    continue;
                }
                if !self.is_live(expression) {
                    return Err(Error("invalid export expression root".into()));
                }
                pending.push((expression, true));
                let children = self.children(expression);
                pending.extend(children.into_iter().rev().map(|(child, _)| (child, false)));
            }
        }
        Ok(ExpressionGraph { nodes })
    }

    /// Import a topological graph using explicit mappings for external nodes
    /// and declarations. Both allocations and mappings roll back on error.
    pub fn import_graph(&self, graph: ExpressionGraph, relocation: &mut Relocation) -> Result<()> {
        let mark = self.scratch_mark();
        let mut staged = relocation.clone();
        let result = (|| {
            let mut own = FxHashSet::default();
            for (old, mut node) in graph.nodes {
                if !own.insert(old) {
                    return Err(Error("duplicate imported expression identity".into()));
                }
                node.relocate(&mut staged)?;
                node.try_for_each_child(|child, _| {
                    if !self.is_live(child) {
                        return Err(Error("invalid imported expression child".into()));
                    }
                    Ok(())
                })?;
                if let Some(existing) = staged.get("expression", old.index() as u64) {
                    let existing = Expression::from_index(
                        u32::try_from(existing)
                            .map_err(|_| Error("expression identity overflow".into()))?,
                    );
                    if !self.is_live(existing) || self.get(existing) != node {
                        return Err(Error("overlapping expression contents disagree".into()));
                    }
                    continue;
                }
                if self.scratch_mark() >= u32::MAX as usize {
                    return Err(Error("expression arena exhausted".into()));
                }
                let expression = self.alloc(node);
                staged.insert("expression", old.index() as u64, expression.index() as u64)?;
            }
            Ok(())
        })();
        if result.is_err() {
            self.rollback_import(mark);
        } else {
            *relocation = staged;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ids::SymbolId,
        metavariables::MetaContext,
        sort::{BaseSort, Sort},
        syntax::Binding,
    };

    fn identity(environment: &mut Environment, body: Option<Expression>) -> DefinitionId {
        let arena = &environment.arena;
        let set = arena.sort(Sort::Base(BaseSort::Set(0)));
        let definition = Definition {
            context: vec![
                Binding {
                    var: SymbolId::ANONYMOUS,
                    ty: set,
                },
                Binding {
                    var: SymbolId::ANONYMOUS,
                    ty: arena.bound(0),
                },
            ],
            ty: arena.bound(1),
            body: body.unwrap_or_else(|| arena.bound(0)),
        };
        environment
            .register_definition(&mut MetaContext::new(), definition)
            .unwrap()
    }

    fn import(
        source: &Environment,
        mut export: EnvironmentExport,
        destination: &mut Environment,
        mapping: &mut Relocation,
    ) {
        let graph = source
            .arena
            .export_graph(export.expression_roots(), |expression| {
                mapping
                    .get("expression", expression.index() as u64)
                    .is_some()
            })
            .unwrap();
        export.reserve_definitions(destination, mapping).unwrap();
        export.reserve_nominals(destination, mapping).unwrap();
        destination.arena.import_graph(graph, mapping).unwrap();
        export.relocate(mapping).unwrap();
        destination.import_export(export).unwrap();
    }

    fn relocated(mut id: DefinitionId, mapping: &mut Relocation) -> DefinitionId {
        id.relocate(mapping).unwrap();
        id
    }

    fn mapping() -> Relocation {
        let mut mapping = Relocation::default();
        mapping.insert("symbol", 0, 0).unwrap();
        mapping
    }

    #[test]
    fn reachable_definitions_follow_bodies_and_skip_detached_metadata() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        let dependency = identity(&mut source, None);
        let dependency_reference = source
            .reference(
                dependency,
                vec![source.arena.bound(1), source.arena.bound(0)],
            )
            .unwrap();
        let retained = identity(&mut source, Some(dependency_reference));
        let detached = identity(&mut source, None);
        let mut export = source.export_since(&boundary).unwrap();
        let roots = BTreeSet::from([definition_identity(retained)]);
        let reachable = export
            .reachable(&source.arena, &roots, &mut |_| false)
            .unwrap();
        assert!(reachable.contains(&definition_identity(dependency)));
        assert!(!reachable.contains(&definition_identity(detached)));
        export.retain_reachable(&reachable);
        assert_eq!(export.definitions.len(), 2);

        let mut traversal = export.reachability(&source.arena);
        let mut reachable = roots;
        let mut visited = 0;
        traversal
            .extend(&mut reachable, &mut |_| {
                visited += 1;
                false
            })
            .unwrap();
        let first = visited;
        traversal
            .extend(&mut reachable, &mut |_| {
                visited += 1;
                false
            })
            .unwrap();
        assert!(first > 0);
        assert_eq!(visited, first);
    }

    #[test]
    fn reachability_stops_at_dependency_expression_roots() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        let dependency = identity(&mut source, None);
        let expression = source
            .reference(
                dependency,
                vec![source.arena.bound(1), source.arena.bound(0)],
            )
            .unwrap();
        let mut export = source.export_since(&boundary).unwrap();
        let roots = BTreeSet::from([Identity::scalar("expression", expression.index() as u64)]);
        let reachable = export
            .reachable(&source.arena, &roots, &mut |node| node == expression)
            .unwrap();
        assert_eq!(reachable, roots);
        export.retain_reachable(&reachable);
        assert!(export.definitions.is_empty());
    }

    #[test]
    fn independent_definitions_import_into_nonempty_arena() {
        let mut left = Environment::new();
        let boundary = left.boundary();
        let left_id = identity(&mut left, None);
        let left_export = left.export_since(&boundary).unwrap();
        let mut right = Environment::new();
        let boundary = right.boundary();
        let right_id = identity(&mut right, None);
        let right_export = right.export_since(&boundary).unwrap();
        let mut destination = Environment::new();
        let original = identity(&mut destination, None);
        destination.arena.bound(500);
        let mut left_mapping = mapping();
        import(&left, left_export, &mut destination, &mut left_mapping);
        let mut right_mapping = mapping();
        import(&right, right_export, &mut destination, &mut right_mapping);
        let left_id = relocated(left_id, &mut left_mapping);
        let right_id = relocated(right_id, &mut right_mapping);
        assert_ne!(left_id, right_id);
        assert_ne!(left_id, original);
        assert_eq!(destination.definitions.len(), 3);
        for id in [left_id, right_id] {
            let reference = destination
                .reference(
                    id,
                    vec![destination.arena.bound(1), destination.arena.bound(0)],
                )
                .unwrap();
            assert_eq!(
                destination.whnf(reference).unwrap(),
                destination.arena.bound(0)
            );
        }
    }

    #[test]
    fn diamond_exports_reference_shared_dependency_without_its_body() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        let a = identity(&mut source, None);
        let a_export = source.export_since(&boundary).unwrap();
        let boundary = source.boundary();
        let a_reference = source
            .reference(a, vec![source.arena.bound(1), source.arena.bound(0)])
            .unwrap();
        let b = identity(&mut source, Some(a_reference));
        let b_export = source.export_since(&boundary).unwrap();
        let boundary = source.boundary();
        let c = identity(&mut source, Some(a_reference));
        let c_export = source.export_since(&boundary).unwrap();
        assert_eq!(b_export.definitions.len(), 1);
        assert_eq!(c_export.definitions.len(), 1);
        let mut destination = Environment::new();
        let mut relocation = mapping();
        import(&source, a_export, &mut destination, &mut relocation);
        // Reverse the source's sibling visit order.
        import(&source, c_export, &mut destination, &mut relocation);
        import(&source, b_export, &mut destination, &mut relocation);
        assert_eq!(destination.definitions.len(), 3);
        let a = relocated(a, &mut relocation);
        for id in [b, c] {
            let id = relocated(id, &mut relocation);
            let body = destination.definition(id).unwrap().body;
            assert!(matches!(destination.arena.get(body), Node::Definition { id, .. } if id == a));
        }
    }

    #[test]
    fn same_nominal_numbers_from_independent_exports_remain_distinct() {
        let mut destination = Environment::new();
        let mut imported = Vec::new();
        for _ in 0..2 {
            let mut source = Environment::new();
            let boundary = source.boundary();
            let set = source.arena.sort(Sort::Base(BaseSort::Set(0)));
            source
                .register_inductive(
                    InductiveId(7),
                    InductiveSpec {
                        parameters: vec![],
                        arity: set,
                        constructors: vec![],
                        sort: Sort::Upper(BaseSort::Set(0)),
                    },
                )
                .unwrap();
            source.register_parameter(ParameterId(7), set).unwrap();
            let export = source.export_since(&boundary).unwrap();
            let mut relocation = mapping();
            import(&source, export, &mut destination, &mut relocation);
            imported.push((
                relocation.get("inductive", 7).unwrap(),
                relocation.get("parameter", 7).unwrap(),
            ));
        }
        assert_ne!(imported[0].0, imported[1].0);
        assert_ne!(imported[0].1, imported[1].1);
        assert_eq!(destination.inductives.len(), 2);
        assert_eq!(destination.parameters.len(), 2);
    }

    #[test]
    fn program_datatype_and_definition_keep_reflection_mappings() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        source
            .register_datatype(
                ProgramInductiveId(10),
                Datatype {
                    parameters: vec![],
                    level: 0,
                    constructors: vec![vec![]],
                    reflected: InductiveId(11),
                },
            )
            .unwrap();
        let arena = &source.arena;
        let value = arena.sort(Sort::Base(BaseSort::Value(0)));
        let body = arena.alloc(Node::Lambda {
            mode: crate::syntax::Mode::Computation,
            var: SymbolId::ANONYMOUS,
            domain: arena.bound(0),
            body: arena.alloc(Node::Return {
                value: arena.bound(0),
            }),
        });
        let ty = arena.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain: arena.bound(0),
            body: arena.alloc(Node::ReturnType {
                value_ty: arena.bound(1),
            }),
        });
        let id = source
            .register_definition(
                &mut MetaContext::new(),
                Definition {
                    context: vec![Binding {
                        var: SymbolId::ANONYMOUS,
                        ty: value,
                    }],
                    ty,
                    body,
                },
            )
            .unwrap();
        let export = source.export_since(&boundary).unwrap();
        let mut destination = Environment::new();
        identity(&mut destination, None);
        let mut relocation = mapping();
        import(&source, export.clone(), &mut destination, &mut relocation);
        import(&source, export, &mut destination, &mut relocation);
        let id = relocated(id, &mut relocation);
        let reference = destination
            .reference(id, vec![destination.arena.bound(0)])
            .unwrap();
        let reflected = destination.reflect_bound(reference).unwrap();
        assert!(
            matches!(destination.arena.get(reflected), Node::Definition { id: reflected_id, .. }
            if Some(reflected_id) == destination.reflected_definition(id))
        );
        let datatype = ProgramInductiveId(relocation.get("datatype", 10).unwrap());
        let mirror = InductiveId(relocation.get("inductive", 11).unwrap());
        assert_eq!(destination.datatype(datatype).unwrap().reflected, mirror);
        assert_eq!(destination.inductive(mirror).unwrap().constructors.len(), 1);
    }

    #[test]
    fn graph_is_shared_topological_and_allows_mapped_raw_atoms() {
        let source = Arena::new();
        let leaf = source.bound(0);
        let shared = source.alloc(Node::Equal {
            left: leaf,
            right: leaf,
        });
        let mut metas = MetaContext::new();
        let atom = metas.fresh(&source, vec![], None);
        let root = source.alloc(Node::Equal {
            left: shared,
            right: atom,
        });
        let graph = source.export_graph([root, shared], |_| false).unwrap();
        assert_eq!(graph.nodes.len(), 4);
        let mut inventory = Relocation::collecting();
        graph.clone().relocate(&mut inventory).unwrap();
        let mut relocation = mapping();
        reserve_metas(&mut relocation, inventory.identities().cloned()).unwrap();
        let destination = Arena::new();
        destination.bound(999);
        destination.import_graph(graph, &mut relocation).unwrap();
        let mut root = root;
        root.relocate(&mut relocation).unwrap();
        assert!(destination.contains_meta(root));
        let Node::Equal { left, .. } = destination.get(root) else {
            panic!()
        };
        let Node::Equal { left, right } = destination.get(left) else {
            panic!()
        };
        assert_eq!(left, right);
    }

    #[test]
    fn overlapping_partial_exports_merge_and_validate_existing_declarations() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        let a = identity(&mut source, None);
        let partial = source.export_since(&boundary).unwrap();
        let body = source
            .reference(a, vec![source.arena.bound(1), source.arena.bound(0)])
            .unwrap();
        identity(&mut source, Some(body));
        let complete = source.export_since(&boundary).unwrap();
        let mut destination = Environment::new();
        let mut relocation = mapping();
        import(&source, partial, &mut destination, &mut relocation);
        import(&source, complete.clone(), &mut destination, &mut relocation);
        import(&source, complete.clone(), &mut destination, &mut relocation);
        assert_eq!(destination.definitions.len(), 2);
        let mut corrupt = complete;
        corrupt.relocate(&mut relocation).unwrap();
        corrupt.definitions[0].1.body = destination.arena.bound(1);
        assert!(destination.import_export(corrupt).is_err());
        assert_eq!(destination.definitions.len(), 2);
    }

    #[test]
    fn overlapping_graph_nodes_are_shared_and_inconsistent_nodes_roll_back() {
        let source = Arena::new();
        let leaf = source.bound(0);
        let root = source.alloc(Node::Equal {
            left: leaf,
            right: leaf,
        });
        let graph = source.export_graph([root], |_| false).unwrap();
        let destination = Arena::new();
        let mut relocation = mapping();
        destination
            .import_graph(graph.clone(), &mut relocation)
            .unwrap();
        let count = destination.len();
        destination
            .import_graph(graph.clone(), &mut relocation)
            .unwrap();
        assert_eq!(destination.len(), count);
        let mut corrupt = graph;
        corrupt.nodes[0].1 = Node::Bound(999);
        assert!(destination.import_graph(corrupt, &mut relocation).is_err());
        assert_eq!(destination.len(), count);
    }

    #[test]
    fn malformed_graph_rolls_back_nodes_and_relocation() {
        let destination = Arena::new();
        let existing = destination.bound(42);
        let size = destination.scratch_mark();
        let graph = ExpressionGraph {
            nodes: vec![
                (Expression::from_index(0), Node::Bound(7)),
                (
                    Expression::from_index(1),
                    Node::Equal {
                        left: Expression::from_index(0),
                        right: Expression::from_index(9),
                    },
                ),
            ],
        };
        let mut relocation = mapping();
        assert!(destination.import_graph(graph, &mut relocation).is_err());
        assert_eq!(destination.scratch_mark(), size);
        assert_eq!(destination.len(), 1);
        assert_eq!(destination.get(existing), Node::Bound(42));
        assert_eq!(relocation.get("expression", 0), None);
    }

    #[test]
    fn corrupt_metadata_is_rejected_before_publication() {
        let mut source = Environment::new();
        let boundary = source.boundary();
        identity(&mut source, None);
        let mut export = source.export_since(&boundary).unwrap();
        let mut destination = Environment::new();
        let mut relocation = mapping();
        export
            .reserve_definitions(&destination, &mut relocation)
            .unwrap();
        let graph = source
            .arena
            .export_graph(export.expression_roots(), |_| false)
            .unwrap();
        destination
            .arena
            .import_graph(graph, &mut relocation)
            .unwrap();
        export.relocate(&mut relocation).unwrap();
        export.definitions[0].1.body = destination.arena.alloc(Node::Definition {
            id: DefinitionId {
                arena: destination.identity,
                index: 700,
            },
            arguments: vec![],
        });
        assert!(destination.import_export(export).is_err());
        assert!(destination.definitions.is_empty());
    }
}
