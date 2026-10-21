//! Persistent paths retain specialization steps instead of copied argument ASTs.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

type Environment = Arc<Arguments>;

#[derive(artifact::Relocate, Clone)]
pub(super) enum Selection {
    Path(ModuleInstantiatePath),
    Append(Arc<Self>, Vec<ModuleCall>),
    Apply(Arc<Self>, Environment, ModuleMap),
}

impl Selection {
    pub(super) fn path(&self) -> ModuleInstantiatePath {
        match self {
            Self::Path(path) => path.clone(),
            Self::Append(base, calls) => {
                let mut path = base.path();
                let arguments = match &mut path {
                    ModuleInstantiatePath::FromModule { calls, .. }
                    | ModuleInstantiatePath::FromCurrent { calls, .. }
                    | ModuleInstantiatePath::FromRoot { calls }
                    | ModuleInstantiatePath::FromImport { calls, .. } => calls,
                };
                arguments.extend(calls.clone());
                path
            }
            Self::Apply(base, arguments, remapping) => {
                let mut expression = SExp::ModuleInstance {
                    path: Box::new(base.path()),
                    import_name: Identifier("<selection>".into()),
                };
                structures::substitute_in_place(&mut expression, &arguments.materialize());
                structures::remap_modules(&mut expression, remapping);
                let SExp::ModuleInstance { path, .. } = expression else {
                    unreachable!()
                };
                *path
            }
        }
    }

    pub(super) fn has_arguments(&self) -> bool {
        let (base, calls) = match self {
            Self::Path(path) => (
                None,
                match path {
                    ModuleInstantiatePath::FromModule { calls, .. }
                    | ModuleInstantiatePath::FromCurrent { calls, .. }
                    | ModuleInstantiatePath::FromRoot { calls }
                    | ModuleInstantiatePath::FromImport { calls, .. } => calls,
                },
            ),
            Self::Append(base, calls) => (Some(base), calls),
            Self::Apply(base, ..) => return base.has_arguments(),
        };
        calls.iter().any(|(_, arguments)| !arguments.is_empty())
            || base.is_some_and(|base| base.has_arguments())
    }
}

#[derive(Serialize, Deserialize)]
enum StoredSelection<P, C> {
    Path(P),
    Append(usize, C),
    Apply(usize, usize, usize),
}

pub(super) fn serialize<S: Serializer>(
    roots: &FxHashMap<ModuleId, Arc<Selection>>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    #[derive(Default)]
    struct Forest<'a> {
        nodes: Vec<StoredSelection<&'a ModuleInstantiatePath, &'a [ModuleCall]>>,
        node_ids: FxHashMap<*const Selection, usize>,
        arguments: Vec<&'a Environment>,
        argument_ids: FxHashMap<*const Arguments, usize>,
        maps: Vec<&'a ModuleMap>,
    }
    impl<'a> Forest<'a> {
        fn insert(&mut self, node: &'a Arc<Selection>) -> usize {
            let address = Arc::as_ptr(node);
            if let Some(&index) = self.node_ids.get(&address) {
                return index;
            }
            let stored = match node.as_ref() {
                Selection::Path(path) => StoredSelection::Path(path),
                Selection::Append(base, calls) => {
                    StoredSelection::Append(self.insert(base), calls.as_slice())
                }
                Selection::Apply(base, arguments, map) => {
                    let base = self.insert(base);
                    let arguments = *self
                        .argument_ids
                        .entry(Arc::as_ptr(arguments))
                        .or_insert_with(|| {
                            let index = self.arguments.len();
                            self.arguments.push(arguments);
                            index
                        });
                    let remapping = self.maps.len();
                    self.maps.push(map);
                    StoredSelection::Apply(base, arguments, remapping)
                }
            };
            let index = self.nodes.len();
            self.nodes.push(stored);
            self.node_ids.insert(address, index);
            index
        }
    }
    let mut forest = Forest::default();
    let mut roots: Vec<_> = roots.iter().collect();
    roots.sort_unstable_by_key(|(id, _)| id.0);
    let roots: Vec<_> = roots
        .into_iter()
        .map(|(id, path)| (*id, forest.insert(path)))
        .collect();
    (
        argument_environment::Forest(forest.arguments),
        crate::module_map::MapForest(forest.maps),
        forest.nodes,
        roots,
    )
        .serialize(serializer)
}

pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<FxHashMap<ModuleId, Arc<Selection>>, D::Error> {
    type Stored = StoredSelection<ModuleInstantiatePath, Vec<ModuleCall>>;
    let (arguments, maps, nodes, roots): (
        argument_environment::Restored,
        crate::module_map::RestoredMaps,
        Vec<Stored>,
        Vec<(ModuleId, usize)>,
    ) = Deserialize::deserialize(deserializer)?;
    let invalid = || serde::de::Error::custom("invalid shared selection reference");
    let mut restored: Vec<Arc<Selection>> = Vec::with_capacity(nodes.len());
    for node in nodes {
        let node = match node {
            StoredSelection::Path(path) => Selection::Path(path),
            StoredSelection::Append(base, calls) => {
                Selection::Append(restored.get(base).ok_or_else(invalid)?.clone(), calls)
            }
            StoredSelection::Apply(base, arguments_id, map) => Selection::Apply(
                restored.get(base).ok_or_else(invalid)?.clone(),
                arguments.0.get(arguments_id).ok_or_else(invalid)?.clone(),
                maps.0.get(map).ok_or_else(invalid)?.clone(),
            ),
        };
        restored.push(Arc::new(node));
    }
    roots
        .into_iter()
        .map(|(id, index)| Ok((id, restored.get(index).ok_or_else(invalid)?.clone())))
        .collect()
}
