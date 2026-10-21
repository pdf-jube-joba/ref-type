//! Preserve shared resolver environments and macro templates across restoration.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::SeqAccess, ser::SerializeSeq};

#[derive(Serialize, Deserialize)]
struct StoredMacro {
    name: Identifier,
    definition: usize,
    instance: ModuleId,
    declaration_order: (usize, usize),
    introduction_location: Option<SourceLocation>,
}
impl StoredMacro {
    fn capture(
        value: &MacroBinding,
        definitions: &FxHashMap<*const MacroDefinition, usize>,
    ) -> Self {
        Self {
            name: value.name.clone(),
            definition: definitions[&Arc::as_ptr(&value.definition)],
            instance: value.instance,
            declaration_order: value.declaration_order,
            introduction_location: value.introduction_location.clone(),
        }
    }
    fn restore<E: serde::de::Error>(
        self,
        definitions: &[Arc<MacroDefinition>],
    ) -> Result<MacroBinding, E> {
        Ok(MacroBinding {
            name: self.name,
            definition: definitions
                .get(self.definition)
                .ok_or_else(|| E::custom("invalid macro template reference"))?
                .clone(),
            instance: self.instance,
            declaration_order: self.declaration_order,
            introduction_location: self.introduction_location,
        })
    }
}

struct Rows<'a> {
    scopes: &'a [Scope],
    definitions: &'a FxHashMap<*const MacroDefinition, usize>,
}
impl Serialize for Rows<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut sequence = serializer.serialize_seq(Some(self.scopes.len()))?;
        let mut tables = [
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
        ];
        for (index, source) in self.scopes.iter().enumerate() {
            let mut scope = source.clone();
            scope.remapping = ModuleMap::default();
            let mut references = [None; 4];
            macro_rules! table {
                ($slot:expr, $field:ident) => {
                    let pointer = Arc::as_ptr(&source.$field) as usize;
                    if let Some(&previous) = tables[$slot].get(&pointer) {
                        references[$slot] = Some(previous);
                        scope.$field = Arc::default();
                    } else {
                        tables[$slot].insert(pointer, index);
                    }
                };
            }
            table!(0, names);
            scope.substitutions = Arc::default();
            table!(2, children);
            table!(3, import_ids);
            let macros: Vec<_> = scope
                .macros
                .iter()
                .map(|value| StoredMacro::capture(value, self.definitions))
                .collect();
            let used: Vec<_> = scope
                .used
                .iter()
                .map(|value| StoredMacro::capture(value, self.definitions))
                .collect();
            scope.macros.clear();
            scope.used.clear();
            sequence.serialize_element(&(scope, references, macros, used))?;
        }
        sequence.end()
    }
}

struct StoredScope {
    scope: Scope,
    macros: Vec<StoredMacro>,
    used: Vec<StoredMacro>,
}
struct RestoredRows(Vec<StoredScope>);
impl<'de> Deserialize<'de> for RestoredRows {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visitor;
        impl<'de> serde::de::Visitor<'de> for Visitor {
            type Value = RestoredRows;
            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("shared resolver scopes")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let mut scopes: Vec<StoredScope> = Vec::new();
                while let Some((mut scope, references, macros, used)) = seq.next_element::<(
                    Scope,
                    [Option<usize>; 4],
                    Vec<StoredMacro>,
                    Vec<StoredMacro>,
                )>()? {
                    macro_rules! table {
                        ($slot:expr, $field:ident) => {
                            if let Some(index) = references[$slot] {
                                scope.$field = scopes
                                    .get(index)
                                    .ok_or_else(|| {
                                        serde::de::Error::custom("invalid shared scope reference")
                                    })?
                                    .scope
                                    .$field
                                    .clone();
                            }
                        };
                    }
                    table!(0, names);
                    scope.substitutions = Arc::default();
                    table!(2, children);
                    table!(3, import_ids);
                    scopes.push(StoredScope {
                        scope,
                        macros,
                        used,
                    });
                }
                Ok(RestoredRows(scopes))
            }
        }
        deserializer.deserialize_seq(Visitor)
    }
}

pub(super) fn serialize<S: Serializer>(scopes: &[Scope], serializer: S) -> Result<S::Ok, S::Error> {
    let mut definitions = Vec::new();
    let mut indices = FxHashMap::default();
    for binding in scopes
        .iter()
        .flat_map(|scope| scope.macros.iter().chain(&scope.used))
    {
        indices
            .entry(Arc::as_ptr(&binding.definition))
            .or_insert_with(|| {
                let id = definitions.len();
                definitions.push(binding.definition.as_ref());
                id
            });
    }
    (
        crate::module_map::MapForest(scopes.iter().map(|scope| &scope.remapping).collect()),
        definitions,
        argument_environment::Forest(scopes.iter().map(|scope| &scope.substitutions).collect()),
        Rows {
            scopes,
            definitions: &indices,
        },
    )
        .serialize(serializer)
}

pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<Scope>, D::Error> {
    let (maps, definitions, arguments, RestoredRows(scopes)): (
        crate::module_map::RestoredMaps,
        Vec<Arc<MacroDefinition>>,
        argument_environment::Restored,
        RestoredRows,
    ) = Deserialize::deserialize(deserializer)?;
    if maps.0.len() != scopes.len() || arguments.0.len() != scopes.len() {
        return Err(serde::de::Error::custom(
            "inconsistent resolver scope count",
        ));
    }
    scopes
        .into_iter()
        .zip(maps.0.into_iter().zip(arguments.0))
        .map(
            |(
                StoredScope {
                    mut scope,
                    macros,
                    used,
                },
                (map, arguments),
            )| {
                scope.substitutions = arguments;
                scope.remapping = map;
                scope.macros = macros
                    .into_iter()
                    .map(|value| value.restore(&definitions))
                    .collect::<Result<_, D::Error>>()?;
                scope.used = used
                    .into_iter()
                    .map(|value| value.restore(&definitions))
                    .collect::<Result<_, D::Error>>()?;
                Ok(scope)
            },
        )
        .collect()
}
