//! Preserve the map-of-vectors wire format and share equal immutable captures.
use serde::{
    Deserialize, Deserializer,
    de::{MapAccess, Visitor},
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    marker::PhantomData,
    sync::Arc,
};

pub(super) fn deserialize<'de, D, K, T>(
    deserializer: D,
) -> Result<HashMap<K, Arc<Vec<T>>>, D::Error>
where
    D: Deserializer<'de>,
    K: Deserialize<'de> + Eq + Hash,
    T: Deserialize<'de> + Eq + Hash,
{
    struct SharedVectors<K, T>(PhantomData<(K, T)>);
    impl<'de, K, T> Visitor<'de> for SharedVectors<K, T>
    where
        K: Deserialize<'de> + Eq + Hash,
        T: Deserialize<'de> + Eq + Hash,
    {
        type Value = HashMap<K, Arc<Vec<T>>>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a map of immutable capture vectors")
        }

        fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
            let mut entries = HashMap::new();
            let mut values: HashSet<Arc<Vec<T>>> = HashSet::new();
            while let Some((key, value)) = map.next_entry::<K, Vec<T>>()? {
                let shared = match values.get(&value) {
                    Some(previous) => previous.clone(),
                    None => {
                        let shared = Arc::new(value);
                        values.insert(shared.clone());
                        shared
                    }
                };
                entries.insert(key, shared);
            }
            Ok(entries)
        }
    }
    deserializer.deserialize_map(SharedVectors(PhantomData))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Serialize;

    #[derive(Serialize, Deserialize)]
    struct Shared {
        #[serde(deserialize_with = "deserialize")]
        entries: HashMap<u32, Arc<Vec<u32>>>,
    }

    #[derive(Serialize, Deserialize)]
    struct Legacy {
        entries: HashMap<u32, Vec<u32>>,
    }

    #[test]
    fn legacy_capture_bytes_restore_shared_vectors_and_keep_distinct_values() {
        let legacy = Legacy {
            entries: HashMap::from([(1, vec![2, 3]), (4, vec![2, 3]), (5, vec![2, 6])]),
        };
        let bytes = postcard::to_allocvec(&legacy).unwrap();
        let shared: Shared = postcard::from_bytes(&bytes).unwrap();
        assert!(Arc::ptr_eq(&shared.entries[&1], &shared.entries[&4]));
        assert!(!Arc::ptr_eq(&shared.entries[&1], &shared.entries[&5]));
        let restored: Legacy =
            postcard::from_bytes(&postcard::to_allocvec(&shared).unwrap()).unwrap();
        assert_eq!(restored.entries, legacy.entries);

        let one = Shared {
            entries: HashMap::from([(1, shared.entries[&1].clone())]),
        };
        let old = Legacy {
            entries: HashMap::from([(1, vec![2, 3])]),
        };
        assert_eq!(
            postcard::to_allocvec(&one).unwrap(),
            postcard::to_allocvec(&old).unwrap()
        );
    }
}
