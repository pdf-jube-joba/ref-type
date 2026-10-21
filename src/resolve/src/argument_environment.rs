//! Persistent argument environments; composed values are expanded only at use.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub(super) type Values = HashMap<BindingId, Arc<SExp>>;

#[derive(artifact::Relocate, Clone)]
pub(super) enum Arguments {
    Values(Values),
    Overlay(Arc<Self>, Values),
    Apply(Arc<Self>, Arc<Self>, ModuleMap),
}
impl Default for Arguments {
    fn default() -> Self {
        Self::Values(Values::new())
    }
}
impl Arguments {
    pub(super) fn is_empty(&self) -> bool {
        match self {
            Self::Values(values) => values.is_empty(),
            Self::Overlay(base, values) => values.is_empty() && base.is_empty(),
            Self::Apply(base, arguments, _) => base.is_empty() && arguments.is_empty(),
        }
    }
    pub(super) fn get(&self, id: &BindingId) -> Option<Arc<SExp>> {
        match self {
            Self::Values(values) => values.get(id).cloned(),
            Self::Overlay(base, values) => values.get(id).cloned().or_else(|| base.get(id)),
            Self::Apply(base, arguments, map) => arguments.get(id).or_else(|| {
                base.get(id).map(|value| {
                    structures::specialize_shared(&value, &arguments.materialize(), map)
                })
            }),
        }
    }
    pub(super) fn materialize(&self) -> Values {
        match self {
            Self::Values(values) => values.clone(),
            Self::Overlay(base, values) => {
                let mut result = base.materialize();
                result.extend(values.iter().map(|(&id, value)| (id, value.clone())));
                result
            }
            Self::Apply(base, arguments, map) => {
                let mut result = arguments.materialize();
                let inherited: Vec<_> = base
                    .materialize()
                    .into_iter()
                    .filter(|(id, _)| !result.contains_key(id))
                    .map(|(id, value)| (id, structures::specialize_shared(&value, &result, map)))
                    .collect();
                result.extend(inherited);
                result
            }
        }
    }
    pub(super) fn overlay(base: Arc<Self>, values: Values) -> Arc<Self> {
        if values.is_empty() {
            base
        } else if base.is_empty() {
            Arc::new(Self::Values(values))
        } else {
            Arc::new(Self::Overlay(base, values))
        }
    }
    pub(super) fn apply(base: Arc<Self>, arguments: Arc<Self>, map: ModuleMap) -> Arc<Self> {
        if base.is_empty() {
            arguments
        } else {
            Arc::new(Self::Apply(base, arguments, map))
        }
    }
}

#[derive(Serialize, Deserialize)]
enum Node {
    Values(Vec<(BindingId, usize)>),
    Overlay(usize, Vec<(BindingId, usize)>),
    Apply(usize, usize, usize),
}
pub(super) struct Forest<'a>(pub Vec<&'a Arc<Arguments>>);
pub(super) struct Restored(pub Vec<Arc<Arguments>>);
impl Serialize for Forest<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(Default)]
        struct Builder<'a> {
            nodes: Vec<Node>,
            indices: FxHashMap<*const Arguments, usize>,
            values: Vec<&'a SExp>,
            value_ids: FxHashMap<*const SExp, usize>,
            maps: Vec<&'a ModuleMap>,
        }
        impl<'a> Builder<'a> {
            fn values(&mut self, values: &'a Values) -> Vec<(BindingId, usize)> {
                let mut entries: Vec<_> = values.iter().collect();
                entries.sort_unstable_by_key(|(id, _)| **id);
                entries
                    .into_iter()
                    .map(|(&id, value)| {
                        let index =
                            *self.value_ids.entry(Arc::as_ptr(value)).or_insert_with(|| {
                                let index = self.values.len();
                                self.values.push(value);
                                index
                            });
                        (id, index)
                    })
                    .collect()
            }
            fn insert(&mut self, value: &'a Arc<Arguments>) -> usize {
                if let Some(&index) = self.indices.get(&Arc::as_ptr(value)) {
                    return index;
                }
                let node = match value.as_ref() {
                    Arguments::Values(values) => Node::Values(self.values(values)),
                    Arguments::Overlay(base, values) => {
                        Node::Overlay(self.insert(base), self.values(values))
                    }
                    Arguments::Apply(base, arguments, map) => {
                        let (base, arguments) = (self.insert(base), self.insert(arguments));
                        let index = self.maps.len();
                        self.maps.push(map);
                        Node::Apply(base, arguments, index)
                    }
                };
                let index = self.nodes.len();
                self.nodes.push(node);
                self.indices.insert(Arc::as_ptr(value), index);
                index
            }
        }
        let mut builder = Builder::default();
        let roots: Vec<_> = self.0.iter().map(|value| builder.insert(value)).collect();
        (
            builder.values,
            crate::module_map::MapForest(builder.maps),
            builder.nodes,
            roots,
        )
            .serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for Restored {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (values, maps, nodes, roots): (
            Vec<Arc<SExp>>,
            crate::module_map::RestoredMaps,
            Vec<Node>,
            Vec<usize>,
        ) = Deserialize::deserialize(deserializer)?;
        let invalid = || serde::de::Error::custom("invalid argument environment reference");
        let entries = |entries: Vec<(BindingId, usize)>| -> Result<Values, D::Error> {
            entries
                .into_iter()
                .map(|(id, index)| Ok((id, values.get(index).ok_or_else(invalid)?.clone())))
                .collect()
        };
        let mut restored: Vec<Arc<Arguments>> = Vec::with_capacity(nodes.len());
        for node in nodes {
            let node = match node {
                Node::Values(values) => Arguments::Values(entries(values)?),
                Node::Overlay(base, values) => Arguments::Overlay(
                    restored.get(base).ok_or_else(invalid)?.clone(),
                    entries(values)?,
                ),
                Node::Apply(base, arguments, map) => Arguments::Apply(
                    restored.get(base).ok_or_else(invalid)?.clone(),
                    restored.get(arguments).ok_or_else(invalid)?.clone(),
                    maps.0.get(map).ok_or_else(invalid)?.clone(),
                ),
            };
            restored.push(Arc::new(node));
        }
        Ok(Self(
            roots
                .into_iter()
                .map(|index| restored.get(index).cloned().ok_or_else(invalid))
                .collect::<Result<_, D::Error>>()?,
        ))
    }
}
impl Serialize for Arguments {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        Forest(vec![&Arc::new(self.clone())]).serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for Arguments {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut roots = Restored::deserialize(deserializer)?.0;
        if roots.len() != 1 {
            return Err(serde::de::Error::custom(
                "expected one argument environment",
            ));
        }
        Ok(Arc::unwrap_or_clone(roots.pop().unwrap()))
    }
}
