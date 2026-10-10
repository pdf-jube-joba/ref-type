//! Preserve sharing between the namespace maps of different specializations.
use super::{
    environment::DeclarationRemapping,
    ids::*,
    shared_map::{MapForest, RestoredMaps},
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub fn serialize<S: Serializer>(
    maps: &[DeclarationRemapping],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    (
        MapForest(maps.iter().map(|map| &map.module_ids).collect()),
        MapForest(maps.iter().map(|map| &map.definition_ids).collect()),
        MapForest(maps.iter().map(|map| &map.inductive_ids).collect()),
        MapForest(maps.iter().map(|map| &map.program_inductive_ids).collect()),
    )
        .serialize(serializer)
}

pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<DeclarationRemapping>, D::Error> {
    let (modules, definitions, inductives, datatypes): (
        RestoredMaps<ModuleId>,
        RestoredMaps<DefId>,
        RestoredMaps<InductiveId>,
        RestoredMaps<ProgramInductiveId>,
    ) = Deserialize::deserialize(deserializer)?;
    if [definitions.0.len(), inductives.0.len(), datatypes.0.len()]
        .into_iter()
        .any(|length| length != modules.0.len())
    {
        return Err(serde::de::Error::custom("inconsistent remapping roots"));
    }
    Ok(modules
        .0
        .into_iter()
        .zip(definitions.0)
        .zip(inductives.0)
        .zip(datatypes.0)
        .map(
            |(((module_ids, definition_ids), inductive_ids), program_inductive_ids)| {
                DeclarationRemapping {
                    module_ids,
                    definition_ids,
                    inductive_ids,
                    program_inductive_ids,
                }
            },
        )
        .collect())
}
