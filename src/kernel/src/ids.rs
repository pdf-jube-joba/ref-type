//! Stable identifiers shared by expressions and the environment.

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Handle into the owning environment's immutable definition arena.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefinitionId {
    #[serde(deserialize_with = "deserialize_identity")]
    pub(crate) arena: u64,
    pub(crate) index: u32,
}

/// Opaque nominal identity of a logical inductive type.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InductiveId(pub u64);

/// Opaque nominal identity of a Program datatype.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProgramInductiveId(pub u64);

/// Rigid parameter identity used while closing a module declaration.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParameterId(pub u64);

static NEXT_IDENTITY: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

pub(crate) fn fresh_identity() -> u64 {
    NEXT_IDENTITY.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

pub(crate) fn deserialize_identity<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<u64, D::Error> {
    let identity = <u64 as serde::Deserialize>::deserialize(d)?;
    let next = identity
        .checked_add(1)
        .ok_or_else(|| serde::de::Error::custom("identity overflow"))?;
    NEXT_IDENTITY.fetch_max(next, std::sync::atomic::Ordering::Relaxed);
    Ok(identity)
}
