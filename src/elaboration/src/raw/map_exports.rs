//! An owned map DAG with references to dependency remapping nodes and tables.
use super::*;
use crate::raw::environment::RemappingSnapshotId;
use artifact::{Error, Relocate, Result};

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, Relocate)]
struct External {
    snapshot: RemappingSnapshotId,
    /// false follows the next map; true follows the previous map.
    path: Vec<bool>,
}
#[derive(serde::Serialize, serde::Deserialize, Relocate)]
#[serde(bound(serialize = "K: Serialize", deserialize = "K: Deserialize<'de>"))]
enum Table<K> {
    Owned(#[serde(with = "entries")] Vec<(K, K)>),
    External(External),
}
#[derive(Clone, serde::Serialize, serde::Deserialize, Relocate)]
enum Node {
    Local {
        table: usize,
        base: Option<(usize, usize)>,
    },
    External(External),
}
#[derive(serde::Deserialize, Relocate)]
pub(crate) struct Export<K> {
    tables: Vec<Table<K>>,
    nodes: Vec<Node>,
    roots: Vec<usize>,
}

impl<K> Export<K> {
    pub(crate) fn empty() -> Self {
        Self {
            tables: Vec::new(),
            nodes: Vec::new(),
            roots: Vec::new(),
        }
    }

    /// Reorder roots together with the enclosing explicit remapping IDs.
    pub(crate) fn reorder_roots(&mut self, order: &[usize]) -> Result<()> {
        if order.len() != self.roots.len() {
            return Err(Error("inconsistent exported remapping root counts".into()));
        }
        let mut seen = vec![false; order.len()];
        let mut roots = Vec::with_capacity(order.len());
        for &index in order {
            let duplicate = seen
                .get_mut(index)
                .ok_or_else(|| Error("invalid exported remapping root order".into()))?;
            if std::mem::replace(duplicate, true) {
                return Err(Error("duplicate exported remapping root order".into()));
            }
            roots.push(self.roots[index]);
        }
        self.roots = roots;
        Ok(())
    }
}

// Normalize physical sharing into structural sharing before writing. The wire
// still contains tables, topological nodes, and roots, in that order.
impl<K: Serialize> Serialize for Export<K> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        use serde::ser::{Error as _, SerializeStruct};
        let mut remaining = 256 * 1024 * 1024;
        let mut encode = |value: &Table<K>| {
            let bytes = artifact::canonical::to_vec(value, remaining).map_err(S::Error::custom)?;
            remaining -= bytes.len();
            Ok::<_, S::Error>(bytes)
        };
        let mut ordered = self
            .tables
            .iter()
            .enumerate()
            .map(|(index, table)| encode(table).map(|bytes| (bytes, index)))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        ordered.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let mut table_ids = vec![0usize; self.tables.len()];
        let mut tables = Vec::new();
        let mut previous: Option<Vec<u8>> = None;
        for (bytes, old) in ordered {
            if previous.as_ref() != Some(&bytes) {
                tables.push(&self.tables[old]);
                previous = Some(bytes);
            }
            table_ids[old] = tables.len() - 1;
        }
        let mut depths: Vec<usize> = Vec::with_capacity(self.nodes.len());
        let mut layers = std::collections::BTreeMap::<usize, Vec<usize>>::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let depth = match node {
                Node::Local { table, base } => {
                    if *table >= self.tables.len() {
                        return Err(S::Error::custom("invalid exported map table"));
                    }
                    match base {
                        Some((next, previous)) => {
                            let next = depths
                                .get(*next)
                                .ok_or_else(|| S::Error::custom("invalid exported map edge"))?;
                            let previous = depths
                                .get(*previous)
                                .ok_or_else(|| S::Error::custom("invalid exported map edge"))?;
                            next.max(previous) + 1
                        }
                        None => 0,
                    }
                }
                Node::External(_) => 0,
            };
            depths.push(depth);
            layers.entry(depth).or_default().push(index);
        }
        let mut node_ids = vec![0usize; self.nodes.len()];
        let mut nodes = Vec::new();
        for (_, layer) in layers {
            let mut ordered = Vec::new();
            for old in layer {
                let node = match &self.nodes[old] {
                    Node::Local { table, base } => Node::Local {
                        table: table_ids[*table],
                        base: base.map(|(next, previous)| (node_ids[next], node_ids[previous])),
                    },
                    Node::External(reference) => Node::External(reference.clone()),
                };
                let bytes =
                    artifact::canonical::to_vec(&node, remaining).map_err(S::Error::custom)?;
                remaining -= bytes.len();
                ordered.push((bytes, old, node));
            }
            ordered.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            let mut previous: Option<Vec<u8>> = None;
            for (bytes, old, node) in ordered {
                if previous.as_ref() != Some(&bytes) {
                    nodes.push(node);
                    previous = Some(bytes);
                }
                node_ids[old] = nodes.len() - 1;
            }
        }
        let roots = self
            .roots
            .iter()
            .map(|index| {
                node_ids
                    .get(*index)
                    .copied()
                    .ok_or_else(|| S::Error::custom("invalid exported map root"))
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let mut fields = serializer.serialize_struct("Export", 3)?;
        fields.serialize_field("tables", &tables)?;
        fields.serialize_field("nodes", &nodes)?;
        fields.serialize_field("roots", &roots)?;
        fields.end()
    }
}

mod entries {
    use serde::{
        Deserialize, Deserializer, Serialize, Serializer,
        de::{MapAccess, Visitor},
        ser::SerializeMap,
    };
    pub fn serialize<K: Serialize, S: Serializer>(
        entries: &[(K, K)],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(entries.len()))?;
        for (key, value) in entries {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
    pub fn deserialize<'de, K: Deserialize<'de>, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<(K, K)>, D::Error> {
        struct Entries<K>(std::marker::PhantomData<K>);
        impl<'de, K: Deserialize<'de>> Visitor<'de> for Entries<K> {
            type Value = Vec<(K, K)>;
            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("shared map entries")
            }
            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
                let mut entries = Vec::new();
                while let Some(entry) = map.next_entry()? {
                    entries.push(entry);
                }
                Ok(entries)
            }
        }
        deserializer.deserialize_map(Entries(std::marker::PhantomData))
    }
}

type Shape = (usize, Option<(usize, usize)>);
fn shape<K>(map: &SharedMap<K>) -> Shape {
    (
        Arc::as_ptr(&map.entries) as usize,
        map.base
            .as_ref()
            .map(|(next, previous)| (Arc::as_ptr(next) as usize, Arc::as_ptr(previous) as usize)),
    )
}
fn lookup<'a, K>(
    external: &External,
    dependencies: &FxHashMap<RemappingSnapshotId, &'a SharedMap<K>>,
) -> Result<&'a SharedMap<K>> {
    let mut map = dependencies
        .get(&external.snapshot)
        .copied()
        .ok_or_else(|| Error("missing external remapping snapshot".into()))?;
    for previous in &external.path {
        let (next, old) = map
            .base
            .as_ref()
            .ok_or_else(|| Error("invalid external map composition path".into()))?;
        map = if *previous { old } else { next };
    }
    Ok(map)
}

impl<K: Copy + Eq + Hash> Export<K> {
    pub(crate) fn capture(
        roots: &[&SharedMap<K>],
        dependencies: &[(RemappingSnapshotId, &SharedMap<K>)],
    ) -> Result<Self> {
        let mut external_nodes = FxHashMap::default();
        let mut external_tables = FxHashMap::default();
        for (id, root) in dependencies {
            let mut pending = vec![(*root, Vec::new())];
            while let Some((map, path)) = pending.pop() {
                let signature = shape(map);
                if external_nodes.contains_key(&signature) {
                    continue;
                }
                let reference = External {
                    snapshot: *id,
                    path: path.clone(),
                };
                external_nodes.insert(signature, reference.clone());
                external_tables.entry(signature.0).or_insert(reference);
                if let Some((next, previous)) = &map.base {
                    let mut old_path = path.clone();
                    old_path.push(true);
                    pending.push((previous.as_ref(), old_path));
                    let mut next_path = path;
                    next_path.push(false);
                    pending.push((next.as_ref(), next_path));
                }
            }
        }
        let mut export = Self {
            tables: Vec::new(),
            nodes: Vec::new(),
            roots: Vec::new(),
        };
        let mut nodes = FxHashMap::default();
        let mut tables = FxHashMap::default();
        for root in roots {
            let mut pending = vec![(*root, false)];
            while let Some((map, expanded)) = pending.pop() {
                let signature = shape(map);
                if nodes.contains_key(&signature) {
                    continue;
                }
                if let Some(reference) = external_nodes.get(&signature) {
                    nodes.insert(signature, export.nodes.len());
                    export.nodes.push(Node::External(reference.clone()));
                    continue;
                }
                if !expanded && let Some((next, previous)) = &map.base {
                    pending.push((map, true));
                    pending.push((previous, false));
                    pending.push((next, false));
                    continue;
                }
                let table = *tables.entry(signature.0).or_insert_with(|| {
                    let index = export.tables.len();
                    export.tables.push(match external_tables.get(&signature.0) {
                        Some(reference) => Table::External(reference.clone()),
                        None => Table::Owned(
                            map.entries
                                .iter()
                                .map(|(key, value)| (*key, *value))
                                .collect(),
                        ),
                    });
                    index
                });
                let base = map
                    .base
                    .as_ref()
                    .map(|(next, previous)| (nodes[&shape(next)], nodes[&shape(previous)]));
                nodes.insert(signature, export.nodes.len());
                export.nodes.push(Node::Local { table, base });
            }
            export.roots.push(nodes[&shape(root)]);
        }
        Ok(export)
    }

    pub(crate) fn restore(
        self,
        dependencies: &[(RemappingSnapshotId, &SharedMap<K>)],
    ) -> Result<Vec<SharedMap<K>>> {
        let dependencies: FxHashMap<_, _> = dependencies.iter().copied().collect();
        let mut tables = Vec::with_capacity(self.tables.len());
        for table in self.tables {
            tables.push(match table {
                Table::External(reference) => lookup(&reference, &dependencies)?.entries.clone(),
                Table::Owned(entries) => {
                    let mut table = FxHashMap::default();
                    for (key, value) in entries {
                        if table.insert(key, value).is_some() {
                            return Err(Error("duplicate imported shared map key".into()));
                        }
                    }
                    Arc::new(table)
                }
            });
        }
        let mut nodes: Vec<Arc<SharedMap<K>>> = Vec::with_capacity(self.nodes.len());
        for node in self.nodes {
            let map = match node {
                Node::External(reference) => lookup(&reference, &dependencies)?.clone(),
                Node::Local { table, base } => {
                    let entries = tables
                        .get(table)
                        .ok_or_else(|| Error("invalid imported shared map table".into()))?
                        .clone();
                    let base = base
                        .map(|(next, previous)| {
                            Ok((
                                nodes
                                    .get(next)
                                    .ok_or_else(|| {
                                        Error("invalid imported shared map edge".into())
                                    })?
                                    .clone(),
                                nodes
                                    .get(previous)
                                    .ok_or_else(|| {
                                        Error("invalid imported shared map edge".into())
                                    })?
                                    .clone(),
                            ))
                        })
                        .transpose()?;
                    SharedMap { entries, base }
                }
            };
            nodes.push(Arc::new(map));
        }
        self.roots
            .into_iter()
            .map(|index| {
                nodes
                    .get(index)
                    .map(|map| map.as_ref().clone())
                    .ok_or_else(|| Error("invalid imported shared map root".into()))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use artifact::Relocation;

    #[test]
    fn inherited_tables_are_external_and_keep_sharing_after_relocation() {
        let mut dependency = SharedMap::default();
        for key in 0u32..5000 {
            dependency.insert(key, key + 1);
        }
        let mut own = SharedMap::default();
        own.insert(9000, 3);
        let composed = dependency.after(&own);
        let export = Export::capture(
            &[&composed, &dependency],
            &[(RemappingSnapshotId(4), &dependency)],
        )
        .unwrap();
        assert_eq!(
            export
                .tables
                .iter()
                .map(|table| match table {
                    Table::Owned(entries) => entries.len(),
                    _ => 0,
                })
                .sum::<usize>(),
            1
        );
        let bytes = artifact::canonical::to_vec(&export, 1000).unwrap();
        assert!(bytes.len() < 100);
        let mut export: Export<u32> = postcard::from_bytes(&bytes).unwrap();
        let mut relocation = Relocation::default();
        relocation.insert("raw.remapping.snapshot", 4, 91).unwrap();
        export.relocate(&mut relocation).unwrap();
        let restored = export
            .restore(&[(RemappingSnapshotId(91), &dependency)])
            .unwrap();
        assert_eq!(restored[0].get(&9000), Some(&4));
        assert!(Arc::ptr_eq(&restored[1].entries, &dependency.entries));
        assert!(Arc::ptr_eq(
            &restored[0].base.as_ref().unwrap().0.entries,
            &dependency.entries
        ));
    }

    #[test]
    fn nested_dependency_path_resolves_without_copying_hidden_tables() {
        let mut first = SharedMap::default();
        first.insert(1u32, 2);
        let mut second = SharedMap::default();
        second.insert(2u32, 3);
        let dependency = second.after(&first);
        let inner = dependency.base.as_ref().unwrap().1.clone();
        let export = Export::capture(&[&inner], &[(RemappingSnapshotId(3), &dependency)]).unwrap();
        assert!(export.tables.is_empty());
        let restored = export
            .restore(&[(RemappingSnapshotId(3), &dependency)])
            .unwrap();
        assert_eq!(restored[0].get(&1), Some(&2));
        assert!(Arc::ptr_eq(&restored[0].entries, &inner.entries));
    }

    #[test]
    fn malformed_external_reference_is_rejected() {
        let mut dependency = SharedMap::default();
        dependency.insert(1u32, 2);
        let mut export =
            Export::capture(&[&dependency], &[(RemappingSnapshotId(3), &dependency)]).unwrap();
        let Node::External(reference) = &mut export.nodes[0] else {
            panic!()
        };
        reference.path.push(false);
        assert!(
            export
                .restore(&[(RemappingSnapshotId(3), &dependency)])
                .is_err()
        );
    }
    #[test]
    fn chain_payload_contains_only_new_tables_and_dependency_edges() {
        let mut packages: Vec<SharedMap<u32>> = Vec::new();
        let mut total_entries = 0;
        let mut total_bytes = 0;
        for index in 0..64u32 {
            let mut own = SharedMap::default();
            for key in 0..4 {
                own.insert(index * 4 + key, index * 4 + key + 1);
            }
            let root = packages
                .last()
                .map_or_else(|| own.clone(), |previous| own.after(previous));
            let dependencies: Vec<_> = packages
                .iter()
                .enumerate()
                .map(|(id, map)| (RemappingSnapshotId(id), map))
                .collect();
            let export = Export::capture(&[&root], &dependencies).unwrap();
            let entries: usize = export
                .tables
                .iter()
                .map(|table| match table {
                    Table::Owned(entries) => entries.len(),
                    _ => 0,
                })
                .sum();
            assert_eq!(entries, 4);
            total_entries += entries;
            total_bytes += artifact::canonical::to_vec(&export, 1000).unwrap().len();
            let restored = export.restore(&dependencies).unwrap();
            assert_eq!(restored[0].get(&(index * 4)), Some(&(index * 4 + 1)));
            packages.push(restored.into_iter().next().unwrap());
        }
        assert_eq!(total_entries, 64 * 4);
        assert!(total_bytes < 64 * 100);
    }
    #[test]
    fn canonical_forest_ignores_equivalent_allocation_sharing() {
        let build = || {
            let mut map = SharedMap::default();
            for key in [40u32, 2, 300] {
                map.insert(key, key + 1);
            }
            map
        };
        let first = build();
        let alias = first.clone();
        let separate = build();
        let shared = Export::capture(&[&first, &alias], &[]).unwrap();
        let independent = Export::capture(&[&first, &separate], &[]).unwrap();
        let bytes = artifact::canonical::to_vec(&shared, 10000).unwrap();
        assert_eq!(
            bytes,
            artifact::canonical::to_vec(&independent, 10000).unwrap()
        );
        let saved: Export<u32> = postcard::from_bytes(&bytes).unwrap();
        let restored = saved.restore(&[]).unwrap();
        assert!(Arc::ptr_eq(&restored[0].entries, &restored[1].entries));
    }

    #[test]
    fn partial_union_preserves_snapshot_paths_and_canonical_bytes() {
        let mut inherited = SharedMap::default();
        for key in 0u32..5000 {
            inherited.insert(key, key + 1);
        }
        let mut common = SharedMap::default();
        common.insert(8000, 8001);
        let mut left = common.after(&inherited);
        assert_eq!(left.insert(6000, 6001), None);
        let mut right = common.after(&inherited);
        assert_eq!(right.insert(7000, 7001), None);
        let snapshot = left.clone();
        let exported = Export::capture(&[&left], &[(RemappingSnapshotId(1), &snapshot)]).unwrap();
        let mut reverse = right.clone();
        left.merge_compatible(&right).unwrap();
        reverse.merge_compatible(&snapshot).unwrap();
        let restored = exported
            .restore(&[(RemappingSnapshotId(1), &snapshot)])
            .unwrap();
        assert_eq!(restored[0].get(&6000), Some(&6001));
        assert_eq!(restored[0].get(&7000), None);
        assert!(Arc::ptr_eq(
            &left.base.as_ref().unwrap().1.entries,
            &inherited.entries,
        ));
        let dependencies = [(RemappingSnapshotId(0), &inherited)];
        let forward = Export::capture(&[&left], &dependencies).unwrap();
        let reverse = Export::capture(&[&reverse], &dependencies).unwrap();
        let bytes = artifact::canonical::to_vec(&forward, 1000).unwrap();
        assert_eq!(bytes, artifact::canonical::to_vec(&reverse, 1000).unwrap());
        assert!(bytes.len() < 100);
        assert_eq!(left.insert(0, 9000), Some(1));
        assert_eq!(left.get(&0), Some(&9000));
        assert_eq!(inherited.get(&0), Some(&1));
    }
}
