//! Preserve shared resolver environments and macro templates across restoration.
use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::SeqAccess, ser::SerializeSeq};

#[derive(artifact::Relocate, Serialize, Deserialize)]
pub(super) struct StoredMacro {
    name: Identifier,
    definition: usize,
    instance: ModuleId,
    declaration_order: (usize, usize),
    introduction_location: Option<SourceLocation>,
}
impl StoredMacro {
    pub(super) fn capture(value: &MacroBinding, definition: usize) -> Self {
        Self {
            name: value.name.clone(),
            definition,
            instance: value.instance,
            declaration_order: value.declaration_order,
            introduction_location: value.introduction_location.clone(),
        }
    }
    pub(super) fn restore(
        self,
        definitions: &[Arc<MacroDefinition>],
    ) -> artifact::Result<MacroBinding> {
        Ok(MacroBinding {
            name: self.name,
            definition: definitions
                .get(self.definition)
                .ok_or_else(|| artifact::Error("invalid macro template reference".into()))?
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
        let capture = |binding: &MacroBinding| {
            StoredMacro::capture(binding, self.definitions[&Arc::as_ptr(&binding.definition)])
        };
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
            let macros: Vec<_> = scope.macros.iter().map(capture).collect();
            let used: Vec<_> = scope.used.iter().map(capture).collect();
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
                    .map(|value| {
                        value
                            .restore(&definitions)
                            .map_err(serde::de::Error::custom)
                    })
                    .collect::<Result<_, D::Error>>()?;
                scope.used = used
                    .into_iter()
                    .map(|value| {
                        value
                            .restore(&definitions)
                            .map_err(serde::de::Error::custom)
                    })
                    .collect::<Result<_, D::Error>>()?;
                Ok(scope)
            },
        )
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reconnect_preserves_specialized_captures_and_binding_locations() {
        fn file(name: &str, text: &str) -> Arc<SourceFile> {
            Arc::new(SourceFile {
                id: SourceId(name.into()),
                text: text.into(),
            })
        }
        let old_definition = file("macros.ref", "");
        let old_use = file("use.ref", "");
        let definition = file("macros.ref", "definition");
        let introduction = file("use.ref", "alias1 alias2");
        let span = |start| SourceSpan {
            start,
            end: start + 1,
        };
        let binding = |capture| MacroBinding {
            name: Identifier("chosen".into()),
            definition: Arc::new(MacroDefinition {
                id: MacroDefinitionId(7),
                kind: MacroKind::Named,
                pattern: vec![],
                template: SExp::ProgramValueReference {
                    access: LocalAccess::Resolved {
                        span: span(2),
                        module: ModuleId(3),
                        access: Name("value".into(), Some(BindingId(capture))),
                        display: "value".into(),
                    },
                },
                definition_scope: ModuleId(3),
                definition_name: "chosen".into(),
                prepared: true,
                location: Some(SourceLocation {
                    source: old_definition.clone(),
                    span: span(0),
                }),
            }),
            instance: ModuleId(3),
            declaration_order: (0, 0),
            introduction_location: None,
        };
        let make_session = || {
            let mut session = Session::default();
            let first = binding(41);
            let second = binding(42);
            session.resolver.scopes.push(Scope {
                macros: vec![first.clone(), second.clone()],
                ..Scope::default()
            });
            let used = [first, second]
                .into_iter()
                .enumerate()
                .map(|(i, mut alias)| {
                    alias.introduction_location = Some(SourceLocation {
                        source: old_use.clone(),
                        span: span(i),
                    });
                    alias
                })
                .collect();
            session.resolver.scopes.push(Scope {
                used,
                ..Scope::default()
            });
            session
        };
        for missing in [&definition.id, &introduction.id] {
            let mut session = make_session();
            assert!(
                session
                    .restore_sources(|id| (id != missing).then(|| {
                        if *id == definition.id {
                            definition.clone()
                        } else {
                            introduction.clone()
                        }
                    }))
                    .is_none()
            );
        }
        let mut session = make_session();
        let lookups = Cell::new(0);
        session
            .restore_sources(|id| {
                if *id == definition.id {
                    lookups.set(lookups.get() + 1);
                    Some(definition.clone())
                } else {
                    (*id == introduction.id).then(|| introduction.clone())
                }
            })
            .unwrap();
        assert_eq!(lookups.get(), 2);
        let original = &session.resolver.scopes[0].macros;
        let aliases = &session.resolver.scopes[1].used;
        assert_eq!(original[0].id, original[1].id);
        assert!(!Arc::ptr_eq(
            &original[0].definition,
            &original[1].definition
        ));
        for (index, alias) in aliases.iter().enumerate() {
            assert!(Arc::ptr_eq(&original[index].definition, &alias.definition));
            let location = alias.location.as_ref().unwrap();
            assert!(Arc::ptr_eq(&location.source, &definition));
            assert_eq!(location.span, span(0));
            let location = alias.introduction_location.as_ref().unwrap();
            assert!(Arc::ptr_eq(&location.source, &introduction));
            assert_eq!(location.span, span(index));
            let SExp::ProgramValueReference {
                access: LocalAccess::Resolved { access, .. },
            } = &alias.template
            else {
                panic!("missing capture")
            };
            assert_eq!(access.1, Some(BindingId(41 + index as u64)));
        }
    }
}
