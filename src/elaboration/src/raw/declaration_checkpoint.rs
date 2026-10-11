//! Store shared substitution telescopes once, including their sharing on restore.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error};

// Shared telescope ordinals follow declaration identity, never hash iteration.
fn ordered<K: Serialize, V, E: serde::ser::Error>(
    entries: &HashMap<K, V>,
) -> Result<Vec<(&K, &V)>, E> {
    let mut ordered = entries
        .iter()
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
    pub fn serialize<S: Serializer>(
        entries: &HashMap<DefId, LazyDefinition>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let _cost = timing::costs::Scope::enter("query.serialize-lazy-definitions");
        let mut arguments = Slices::default();
        let mut reflected = Slices::default();
        let entries: Vec<_> = ordered::<_, _, S::Error>(entries)?
            .into_iter()
            .map(|(&id, value)| {
                (
                    id,
                    value.source,
                    arguments.insert(&value.substitutions),
                    reflected.insert(&value.reflected_substitutions),
                    value.remapping,
                )
            })
            .collect();
        (arguments.values, reflected.values, entries).serialize(serializer)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<HashMap<DefId, LazyDefinition>, D::Error> {
        type Data = (
            Vec<Arc<[(ModuleParamId, ModuleArgument)]>>,
            Vec<Arc<[(ModuleParamId, Exp)]>>,
            Vec<(DefId, DefId, usize, usize, RemappingId)>,
        );
        let (arguments, reflected, entries): Data = Deserialize::deserialize(deserializer)?;
        entries
            .into_iter()
            .map(|(id, source, a, r, remapping)| {
                Ok((
                    id,
                    LazyDefinition {
                        source,
                        substitutions: get(&arguments, a)?,
                        reflected_substitutions: get(&reflected, r)?,
                        remapping,
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
    pub fn serialize<I: Copy + Serialize, S: Serializer>(
        entries: &HashMap<I, Specialization<I>>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let _cost = timing::costs::Scope::enter("query.serialize-specializations");
        let mut arguments = Slices::default();
        let entries: Vec<_> = ordered::<_, _, S::Error>(entries)?
            .into_iter()
            .map(|(&id, value)| (id, value.source, arguments.insert(&value.arguments)))
            .collect();
        (arguments.values, entries).serialize(serializer)
    }
    pub fn deserialize<
        'de,
        I: Copy + Eq + std::hash::Hash + Deserialize<'de>,
        D: Deserializer<'de>,
    >(
        deserializer: D,
    ) -> Result<HashMap<I, Specialization<I>>, D::Error> {
        type Data<I> = (
            Vec<Arc<[(ModuleParamId, ModuleArgument)]>>,
            Vec<(I, I, usize)>,
        );
        let (arguments, entries): Data<I> = Deserialize::deserialize(deserializer)?;
        entries
            .into_iter()
            .map(|(id, source, a)| {
                Ok((
                    id,
                    Specialization {
                        source,
                        arguments: get(&arguments, a)?,
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
        let saved = Saved {
            entries: (0..1000)
                .map(|index| {
                    let id = DefId { module, index };
                    (
                        id,
                        LazyDefinition {
                            source: id,
                            substitutions: arguments.clone(),
                            reflected_substitutions: reflected.clone(),
                            remapping: RemappingId(0),
                        },
                    )
                })
                .collect(),
        };
        let bytes = postcard::to_allocvec(&saved).unwrap();
        assert!(bytes.len() < 20_000, "{} bytes", bytes.len());
        let restored: Saved = postcard::from_bytes(&bytes).unwrap();
        let first = &restored.entries[&DefId { module, index: 0 }];
        for value in restored.entries.values() {
            assert_eq!(value.substitutions, arguments);
            assert_eq!(value.reflected_substitutions, reflected);
            assert!(Arc::ptr_eq(&first.substitutions, &value.substitutions));
            assert!(Arc::ptr_eq(
                &first.reflected_substitutions,
                &value.reflected_substitutions
            ));
        }
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
                                substitutions: if share {
                                    arguments.clone()
                                } else {
                                    arguments.to_vec().into()
                                },
                                reflected_substitutions: Arc::from([]),
                                remapping: RemappingId(0),
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
