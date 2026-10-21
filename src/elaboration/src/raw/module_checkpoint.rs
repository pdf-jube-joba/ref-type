//! Restore immutable namespace tables with the sharing used by live imports.
use super::*;
use serde::{
    Deserializer,
    de::{SeqAccess, Visitor},
};

/// Serialize shared immutable member indices once. References point backwards,
/// so restoring the tables uses bounded temporary memory and preserves sharing.
#[allow(clippy::vec_box)]
pub(super) fn serialize<S: serde::Serializer>(
    modules: &[Box<ModuleEnv>],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeSeq;
    let mut sequence = serializer.serialize_seq(Some(modules.len()))?;
    let mut tables = [
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
    ];
    for (index, module) in modules.iter().enumerate() {
        let mut module = module.as_ref().clone();
        let mut references = [None; 4];
        macro_rules! table {
            ($slot:expr, $field:ident) => {
                let pointer = Arc::as_ptr(&module.$field) as usize;
                if let Some(&previous) = tables[$slot].get(&pointer) {
                    references[$slot] = Some(previous);
                    module.$field = Default::default();
                } else {
                    tables[$slot].insert(pointer, index);
                }
            };
        }
        table!(0, items);
        table!(1, names);
        table!(2, hir_names);
        table!(3, hir_items);
        sequence.serialize_element(&(module, references))?;
    }
    sequence.end()
}

#[allow(clippy::vec_box)]
pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<Box<ModuleEnv>>, D::Error> {
    struct Modules;
    impl<'de> Visitor<'de> for Modules {
        type Value = Vec<Box<ModuleEnv>>;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("namespace modules")
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
            let mut modules: Vec<Box<ModuleEnv>> = Vec::new();
            while let Some((mut module, references)) =
                seq.next_element::<(Box<ModuleEnv>, [Option<usize>; 4])>()?
            {
                macro_rules! table {
                    ($slot:expr, $field:ident) => {
                        if let Some(index) = references[$slot] {
                            let source = modules.get(index).ok_or_else(|| {
                                serde::de::Error::custom("invalid namespace table reference")
                            })?;
                            module.$field = source.$field.clone();
                        }
                    };
                }
                table!(0, items);
                table!(1, names);
                table!(2, hir_names);
                table!(3, hir_items);
                modules.push(module);
            }
            Ok(modules)
        }
    }
    deserializer.deserialize_seq(Modules)
}
