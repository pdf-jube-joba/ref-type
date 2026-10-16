//! Store shared substitution telescopes once, including their sharing on restore.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error};

// Shared telescope ordinals follow declaration identity, never hash iteration.
fn ordered<'a, K: Serialize + 'a, V: 'a, E: serde::ser::Error>(
    entries: impl IntoIterator<Item = (&'a K, &'a V)>,
) -> Result<Vec<(&'a K, &'a V)>, E> {
    let mut ordered = entries
        .into_iter()
        .map(|(key, value)| {
            artifact::canonical::to_vec(key, 1024 * 1024)
                .map(|bytes| (bytes, key, value))
                .map_err(E::custom)
        })
        .collect::<Result<Vec<_>, _>>()?;
    ordered.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    Ok(ordered
        .into_iter()
        .map(|(_, key, value)| (key, value))
        .collect())
}

struct Slices<'a, T> {
    ids: FxHashMap<*const T, usize>,
    contents: FxHashMap<&'a [T], usize>,
    values: Vec<&'a [T]>,
}
impl<T> Default for Slices<'_, T> {
    fn default() -> Self {
        Self {
            ids: Default::default(),
            contents: Default::default(),
            values: Vec::new(),
        }
    }
}
impl<'a, T: Eq + std::hash::Hash> Slices<'a, T> {
    fn insert(&mut self, value: &'a Arc<[T]>) -> usize {
        *self.ids.entry(value.as_ptr()).or_insert_with(|| {
            *self.contents.entry(value.as_ref()).or_insert_with(|| {
                let id = self.values.len();
                self.values.push(value);
                id
            })
        })
    }
}
fn get<T, E: Error>(values: &[Arc<[T]>], id: usize) -> Result<Arc<[T]>, E> {
    values
        .get(id)
        .cloned()
        .ok_or_else(|| E::custom("invalid substitution telescope"))
}

pub(super) mod definitions {
    use super::*;
    pub fn serialize<'a, S: Serializer, T>(entries: &'a T, serializer: S) -> Result<S::Ok, S::Error>
    where
        &'a T: IntoIterator<Item = (&'a DefId, &'a LazyDefinition)>,
    {
        let _cost = timing::costs::Scope::enter("query.serialize-lazy-definitions");
        let mut arguments = Slices::default();
        let mut reflected = Slices::default();
        let entries: Vec<_> = ordered::<_, _, S::Error>(entries)?
            .into_iter()
            .map(|(&id, value)| {
                (
                    id,
                    value.source,
                    arguments.insert(&value.environment.substitutions),
                    reflected.insert(&value.environment.reflected_substitutions),
                    value.environment.remapping.get(),
                )
            })
            .collect();
        (arguments.values, reflected.values, entries).serialize(serializer)
    }
    pub fn deserialize<'de, D: Deserializer<'de>, T: FromIterator<(DefId, LazyDefinition)>>(
        deserializer: D,
    ) -> Result<T, D::Error> {
        type Data = (
            Vec<Arc<[(ModuleParamId, ModuleArgument)]>>,
            Vec<Arc<[(ModuleParamId, Exp)]>>,
            Vec<(DefId, DefId, usize, usize, RemappingId)>,
        );
        let (arguments, reflected, entries): Data = Deserialize::deserialize(deserializer)?;
        let mut environments: HashMap<(usize, usize, RemappingId), Arc<DefinitionEnvironment>> =
            HashMap::new();
        entries
            .into_iter()
            .map(|(id, source, a, r, remapping)| {
                let environment = match environments.entry((a, r, remapping)) {
                    std::collections::hash_map::Entry::Occupied(entry) => entry.get().clone(),
                    std::collections::hash_map::Entry::Vacant(entry) => entry
                        .insert(Arc::new(DefinitionEnvironment {
                            substitutions: get(&arguments, a)?,
                            reflected_substitutions: get(&reflected, r)?,
                            remapping: Cell::new(remapping),
                        }))
                        .clone(),
                };
                Ok((
                    id,
                    LazyDefinition {
                        source,
                        environment,
                    },
                ))
            })
            .collect()
    }
}

macro_rules! substitution_map {
    ($name:ident, $id:ty, $value:ident, $argument:ty) => {
        pub(super) mod $name {
            use super::*;
            pub fn serialize<S: Serializer>(
                entries: &HashMap<$id, $value>,
                serializer: S,
            ) -> Result<S::Ok, S::Error> {
                let _cost = timing::costs::Scope::enter("query.serialize-lazy-types");
                let mut arguments = Slices::default();
                let entries: Vec<_> = ordered::<_, _, S::Error>(entries)?
                    .into_iter()
                    .map(|(&id, value)| {
                        (
                            id,
                            value.source,
                            arguments.insert(&value.substitutions),
                            value.remapping,
                        )
                    })
                    .collect();
                (arguments.values, entries).serialize(serializer)
            }
            pub fn deserialize<'de, D: Deserializer<'de>>(
                deserializer: D,
            ) -> Result<HashMap<$id, $value>, D::Error> {
                type Data = (
                    Vec<Arc<[(ModuleParamId, $argument)]>>,
                    Vec<($id, $id, usize, RemappingId)>,
                );
                let (arguments, entries): Data = Deserialize::deserialize(deserializer)?;
                entries
                    .into_iter()
                    .map(|(id, source, a, remapping)| {
                        Ok((
                            id,
                            $value {
                                source,
                                substitutions: get(&arguments, a)?,
                                remapping,
                            },
                        ))
                    })
                    .collect()
            }
        }
    };
}
substitution_map!(inductives, InductiveId, LazyInductive, Exp);
substitution_map!(
    datatypes,
    ProgramInductiveId,
    LazyProgramInductive,
    ModuleArgument
);

pub(super) mod specializations {
    use super::*;
    use crate::raw::namespaces::Specialization;
    pub fn serialize<'a, I: Copy + Serialize + 'a, S: Serializer, T>(
        entries: &'a T,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        &'a T: IntoIterator<Item = (&'a I, &'a Specialization<I>)>,
    {
        let _cost = timing::costs::Scope::enter("query.serialize-specializations");
        let mut arguments = Slices::default();
        let entries: Vec<_> = ordered::<_, _, S::Error>(entries)?
            .into_iter()
            .map(|(&id, value)| (id, value.source, arguments.insert(value.arguments.as_arc())))
            .collect();
        (arguments.values, entries).serialize(serializer)
    }
    pub fn deserialize<
        'de,
        I: Copy + Eq + std::hash::Hash + Deserialize<'de>,
        D: Deserializer<'de>,
        T: FromIterator<(I, Specialization<I>)>,
    >(
        deserializer: D,
    ) -> Result<T, D::Error> {
        type Data<I> = (
            Vec<Arc<[(ModuleParamId, ModuleArgument)]>>,
            Vec<(I, I, usize)>,
        );
        let (arguments, entries): Data<I> = Deserialize::deserialize(deserializer)?;
        let arguments: Vec<crate::raw::namespaces::SharedArguments> =
            arguments.into_iter().map(Into::into).collect();
        entries
            .into_iter()
            .map(|(id, source, a)| {
                Ok((
                    id,
                    Specialization {
                        source,
                        arguments: arguments
                            .get(a)
                            .cloned()
                            .ok_or_else(|| D::Error::custom("invalid substitution telescope"))?,
                    },
                ))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(artifact::Relocate, Serialize, Deserialize)]
    struct Saved {
        #[serde(with = "definitions")]
        entries: HashMap<DefId, LazyDefinition>,
    }

    #[derive(Serialize, Deserialize)]
    struct ShardedSaved {
        #[serde(with = "definitions")]
        entries: ShardedMap<DefId, LazyDefinition>,
    }

    #[test]
    fn sharded_specializations_keep_the_legacy_checkpoint_format() {
        #[derive(Serialize, Deserialize)]
        struct Legacy {
            #[serde(with = "specializations")]
            entries: HashMap<DefId, super::super::super::namespaces::Specialization<DefId>>,
        }
        #[derive(Serialize, Deserialize)]
        struct Sharded {
            #[serde(with = "specializations")]
            entries: ShardedMap<DefId, super::super::super::namespaces::Specialization<DefId>>,
        }
        let arguments: Arc<[(ModuleParamId, ModuleArgument)]> = Arc::from([]);
        let entries = (0..1024)
            .map(|index| {
                let id = DefId {
                    module: ModuleId(index % 31),
                    index,
                };
                (
                    id,
                    super::super::super::namespaces::Specialization {
                        source: id,
                        arguments: arguments.clone().into(),
                    },
                )
            })
            .collect();
        let legacy = Legacy { entries };
        let bytes = postcard::to_allocvec(&legacy).unwrap();
        let restored: Sharded = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(restored.entries.len(), legacy.entries.len());
        assert_eq!(postcard::to_allocvec(&restored).unwrap(), bytes);
        for (&id, value) in &restored.entries {
            assert_eq!(value.source, id);
            assert!(value.arguments.is_empty());
        }
    }

    #[test]
    fn checkpoint_retains_shared_telescopes_without_repeating_their_contents() {
        let env = CrateEnv::new();
        let module = env.root_module();
        let arguments: Arc<[_]> = (0..100)
            .map(|position| {
                (
                    ModuleParamId { module, position },
                    ModuleArgument::Pts(env.arena().exp_bound(position as usize)),
                )
            })
            .collect();
        let reflected: Arc<[_]> = arguments
            .iter()
            .map(|&(id, value)| {
                let ModuleArgument::Pts(value) = value else {
                    unreachable!()
                };
                (id, value)
            })
            .collect();
        let environment = Arc::new(DefinitionEnvironment {
            substitutions: arguments.clone(),
            reflected_substitutions: reflected.clone(),
            remapping: Cell::new(RemappingId(0)),
        });
        let saved = Saved {
            entries: (0..1000)
                .map(|index| {
                    let id = DefId { module, index };
                    (
                        id,
                        LazyDefinition {
                            source: id,
                            environment: environment.clone(),
                        },
                    )
                })
                .collect(),
        };
        let bytes = postcard::to_allocvec(&saved).unwrap();
        assert!(bytes.len() < 20_000, "{} bytes", bytes.len());
        let sharded: ShardedSaved = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(postcard::to_allocvec(&sharded).unwrap(), bytes);
        assert_eq!(sharded.entries.len(), saved.entries.len());
        let shared = &sharded.entries[&DefId { module, index: 0 }].environment;
        for (_, value) in &sharded.entries {
            assert!(Arc::ptr_eq(shared, &value.environment));
        }
        let restored: Saved = postcard::from_bytes(&bytes).unwrap();
        let first = &restored.entries[&DefId { module, index: 0 }];
        for value in restored.entries.values() {
            assert_eq!(value.environment.substitutions, arguments);
            assert_eq!(value.environment.reflected_substitutions, reflected);
            assert!(Arc::ptr_eq(&first.environment, &value.environment));
            assert!(Arc::ptr_eq(
                &first.environment.substitutions,
                &value.environment.substitutions
            ));
            assert!(Arc::ptr_eq(
                &first.environment.reflected_substitutions,
                &value.environment.reflected_substitutions
            ));
        }
    }
    #[test]
    fn checkpoint_restores_shared_environments_from_legacy_rows() {
        let module = ModuleId(0);
        let arguments: Vec<Arc<[(ModuleParamId, ModuleArgument)]>> = vec![Arc::from([])];
        let reflected: Vec<Arc<[(ModuleParamId, Exp)]>> = vec![Arc::from([])];
        let rows: Vec<_> = (0..3)
            .map(|index| {
                let id = DefId { module, index };
                (id, id, 0usize, 0usize, RemappingId(usize::from(index == 1)))
            })
            .collect();
        let bytes = postcard::to_allocvec(&(arguments, reflected, rows)).unwrap();
        let restored: Saved = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(postcard::to_allocvec(&restored).unwrap(), bytes);
        let first = &restored.entries[&DefId { module, index: 0 }].environment;
        let other = &restored.entries[&DefId { module, index: 1 }].environment;
        let shared = &restored.entries[&DefId { module, index: 2 }].environment;
        assert!(Arc::ptr_eq(first, shared));
        assert!(!Arc::ptr_eq(first, other));
        first.remapping.set(RemappingId(2));
        assert_eq!(shared.remapping.get(), RemappingId(2));
        assert_eq!(other.remapping.get(), RemappingId(1));
    }

    #[test]
    fn shared_telescope_bytes_ignore_hash_order_and_allocation_aliasing() {
        let env = CrateEnv::new();
        let module = env.root_module();
        let arguments: Arc<[_]> = vec![(
            ModuleParamId {
                module,
                position: 0,
            },
            ModuleArgument::Pts(env.arena().exp_bound(0)),
        )]
        .into();
        let build = |reverse: bool, share: bool| {
            let ids: Vec<_> = if reverse {
                (0..10).rev().collect()
            } else {
                (0..10).collect()
            };
            Saved {
                entries: ids
                    .into_iter()
                    .map(|index| {
                        let id = DefId { module, index };
                        (
                            id,
                            LazyDefinition {
                                source: id,
                                environment: Arc::new(DefinitionEnvironment {
                                    substitutions: if share {
                                        arguments.clone()
                                    } else {
                                        arguments.to_vec().into()
                                    },
                                    reflected_substitutions: Arc::from([]),
                                    remapping: Cell::new(RemappingId(0)),
                                }),
                            },
                        )
                    })
                    .collect(),
            }
        };
        let encode = |value: &Saved| artifact::canonical::to_vec(value, 10000).unwrap();
        assert_eq!(encode(&build(false, true)), encode(&build(true, false)));
    }
}
