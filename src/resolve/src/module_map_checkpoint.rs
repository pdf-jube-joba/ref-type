//! Encode shared namespace correspondences once per checkpoint forest.
use super::*;
use rustc_hash::FxHashMap;

pub(crate) struct MapForest<'a>(pub Vec<&'a ModuleMap>);

type MapNode = (usize, Option<usize>, Option<(usize, usize)>);
type MapForestData = (
    Vec<Arc<HashMap<ModuleId, ModuleId>>>,
    Vec<MapNode>,
    Vec<usize>,
);

impl Serialize for MapForest<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        struct Forest<'a> {
            tables: Vec<&'a HashMap<ModuleId, ModuleId>>,
            table_ids: FxHashMap<*const HashMap<ModuleId, ModuleId>, usize>,
            nodes: Vec<MapNode>,
            node_ids: FxHashMap<*const ModuleMap, usize>,
        }
        impl<'a> Forest<'a> {
            fn insert(&mut self, map: &'a ModuleMap) -> usize {
                if let Some(&id) = self.node_ids.get(&(map as *const _)) {
                    return id;
                }
                let parent = map.parent.as_ref().map(|parent| self.insert(parent));
                let base = map
                    .composition
                    .as_ref()
                    .map(|(next, previous)| (self.insert(next), self.insert(previous)));
                let table = *self
                    .table_ids
                    .entry(Arc::as_ptr(&map.entries))
                    .or_insert_with(|| {
                        let id = self.tables.len();
                        self.tables.push(&map.entries);
                        id
                    });
                let id = self.nodes.len();
                self.nodes.push((table, parent, base));
                self.node_ids.insert(map as *const _, id);
                id
            }
        }
        let mut forest = Forest {
            tables: Vec::new(),
            table_ids: FxHashMap::default(),
            nodes: Vec::new(),
            node_ids: FxHashMap::default(),
        };
        let roots: Vec<_> = self.0.iter().map(|map| forest.insert(map)).collect();
        struct Table<'a>(&'a HashMap<ModuleId, ModuleId>);
        impl Serialize for Table<'_> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeMap;
                let mut entries: Vec<_> = self.0.iter().collect();
                entries.sort_unstable_by_key(|(id, _)| id.0);
                let mut map = serializer.serialize_map(Some(entries.len()))?;
                for (key, value) in entries {
                    map.serialize_entry(key, value)?;
                }
                map.end()
            }
        }
        (
            forest.tables.into_iter().map(Table).collect::<Vec<_>>(),
            forest.nodes,
            roots,
        )
            .serialize(serializer)
    }
}

pub(crate) struct RestoredMaps(pub Vec<ModuleMap>);

impl<'de> Deserialize<'de> for RestoredMaps {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error;
        let (tables, nodes, roots): MapForestData = Deserialize::deserialize(deserializer)?;
        let mut restored: Vec<Arc<ModuleMap>> = Vec::with_capacity(nodes.len());
        for (table, parent, base) in nodes {
            let parent = parent
                .map(|index| {
                    restored
                        .get(index)
                        .cloned()
                        .ok_or_else(|| D::Error::custom("invalid namespace parent"))
                })
                .transpose()?;
            let entries = tables
                .get(table)
                .ok_or_else(|| D::Error::custom("invalid shared map table"))?
                .clone();
            let base = base
                .map(|(next, previous)| {
                    Ok((
                        restored
                            .get(next)
                            .ok_or_else(|| D::Error::custom("invalid shared map edge"))?
                            .clone(),
                        restored
                            .get(previous)
                            .ok_or_else(|| D::Error::custom("invalid shared map edge"))?
                            .clone(),
                    ))
                })
                .transpose()?;
            restored.push(Arc::new(ModuleMap {
                entries,
                parent,
                composition: base,
            }));
        }
        let maps = roots
            .into_iter()
            .map(|root| {
                let map = restored
                    .get(root)
                    .ok_or_else(|| D::Error::custom("invalid shared map root"))?;
                Ok(ModuleMap {
                    entries: map.entries.clone(),
                    parent: map.parent.clone(),
                    composition: map.composition.clone(),
                })
            })
            .collect::<Result<_, D::Error>>()?;
        Ok(Self(maps))
    }
}
