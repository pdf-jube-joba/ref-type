//! Share source namespace paths across reference occurrences after restoration.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer, ser::SerializeSeq};

pub(super) fn serialize<S: Serializer>(
    references: &RefCell<Vec<Reference>>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let references = references.borrow();
    let mut paths = Vec::new();
    let mut indices = FxHashMap::default();
    for reference in references.iter() {
        for path in [&reference.module, &reference.target_module] {
            if !indices.contains_key(path.as_ref()) {
                indices.insert(path.as_ref(), paths.len());
                paths.push(path);
            }
        }
    }
    struct Rows<'a> {
        references: &'a [Reference],
        indices: &'a FxHashMap<&'a Vec<String>, usize>,
    }
    impl Serialize for Rows<'_> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let mut rows = serializer.serialize_seq(Some(self.references.len()))?;
            for reference in self.references {
                rows.serialize_element(&(
                    self.indices[reference.module.as_ref()],
                    &reference.location,
                    self.indices[reference.target_module.as_ref()],
                    &reference.target_name,
                ))?;
            }
            rows.end()
        }
    }
    (
        paths,
        Rows {
            references: &references,
            indices: &indices,
        },
    )
        .serialize(serializer)
}
pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<RefCell<Vec<Reference>>, D::Error> {
    type Row = (usize, SourceLocation, usize, String);
    let (paths, rows): (Vec<Arc<Vec<String>>>, Vec<Row>) = Deserialize::deserialize(deserializer)?;
    let path = |index| {
        paths
            .get(index)
            .cloned()
            .ok_or_else(|| serde::de::Error::custom("invalid reference namespace path"))
    };
    Ok(RefCell::new(
        rows.into_iter()
            .map(|(module, location, target, target_name)| {
                Ok(Arc::new(ReferenceData {
                    module: path(module)?,
                    location,
                    target_module: path(target)?,
                    target_name,
                }))
            })
            .collect::<Result<_, D::Error>>()?,
    ))
}
