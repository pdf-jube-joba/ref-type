//! Store import correspondences as one shared forest, in binding-ID order.
use crate::{
    Import,
    hir::{BindingId, ModuleId},
    module_map::{MapForest, RestoredMaps},
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{collections::HashMap, sync::Arc};

pub(crate) fn serialize<S: Serializer>(
    imports: &HashMap<BindingId, Import>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut entries: Vec<_> = imports.iter().collect();
    entries.sort_unstable_by_key(|(id, _)| id.0);
    let maps = MapForest(
        entries
            .iter()
            .map(|(_, import)| &import.remapping)
            .collect(),
    );
    let rows: Vec<_> = entries
        .iter()
        .map(|(id, import)| (**id, import.owner, &import.name, import.target))
        .collect();
    (maps, rows).serialize(serializer)
}

pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Arc<HashMap<BindingId, Import>>, D::Error> {
    type Row = (BindingId, ModuleId, String, ModuleId);
    let (maps, rows): (RestoredMaps, Vec<Row>) = Deserialize::deserialize(deserializer)?;
    if maps.0.len() != rows.len() {
        return Err(serde::de::Error::custom(
            "inconsistent import correspondence count",
        ));
    }
    let mut imports = HashMap::with_capacity(rows.len());
    for ((id, owner, name, target), remapping) in rows.into_iter().zip(maps.0) {
        if imports
            .insert(
                id,
                Import {
                    owner,
                    name,
                    target,
                    remapping,
                },
            )
            .is_some()
        {
            return Err(serde::de::Error::custom("duplicate imported binding"));
        }
    }
    Ok(Arc::new(imports))
}
