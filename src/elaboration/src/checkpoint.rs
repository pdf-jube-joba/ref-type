//! Bounded serialization of a checking environment.
use postcard::Result;
use serde::Serialize;

pub const MAX_ENVIRONMENT_BYTES: usize = 16 * 1024 * 1024;

#[cfg(target_arch = "wasm32")]
#[path = "checkpoint/deflate.rs"]
mod compression;
#[cfg(not(target_arch = "wasm32"))]
#[path = "checkpoint/zstd.rs"]
mod compression;
use compression::Buffer;
mod segments;
pub(crate) use compression::decompress;

pub(crate) fn deserialize_bounded<T: serde::de::DeserializeOwned, const LIMIT: usize>(
    bytes: &[u8],
) -> Option<T> {
    if bytes.starts_with(segments::MAGIC) {
        return segments::deserialize(bytes, kernel::graph_store::current()?);
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        compression::deserialize::<T, LIMIT>(bytes)
    }
    #[cfg(target_arch = "wasm32")]
    {
        postcard::from_bytes(&decompress::<LIMIT>(bytes)?).ok()
    }
}

pub(crate) fn serialize(value: &impl Serialize) -> Result<Vec<u8>> {
    serialize_bounded::<MAX_ENVIRONMENT_BYTES>(value)
}

pub(crate) fn serialize_bounded<const LIMIT: usize>(value: &impl Serialize) -> Result<Vec<u8>> {
    // Feed serialization straight into the compressor. The live environment
    // coexists only with a fixed input chunk and the compressed checkpoint.
    let _phase = crate::profiling::Phase::start("environment.serialize-compress");
    if LIMIT == crate::package::MAX_PACKAGE_BYTES
        && let Some(store) = kernel::graph_store::current()
    {
        return postcard::serialize_with_flavor(value, segments::Buffer::new(store));
    }
    postcard::serialize_with_flavor(value, Buffer::<LIMIT>::new()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    const CHUNK_BYTES: usize = 32 * 1024;

    #[test]
    fn checkpoint_decoding_rejects_truncation_and_expansion_past_the_budget() {
        let bytes = serialize(&vec![0_u8; 4096]).unwrap();
        assert!(decompress::<1024>(&bytes).is_none());
        assert!(decompress::<MAX_ENVIRONMENT_BYTES>(&bytes[..bytes.len() - 1]).is_none());
        assert!(decompress::<MAX_ENVIRONMENT_BYTES>(&[]).is_none());
    }

    #[test]
    fn streaming_checkpoints_cross_input_and_output_chunk_boundaries() {
        assert!(serialize_bounded::<64>(&vec![0_u8; 1024]).is_err());
        let mut state = 42_u32;
        let random: Vec<u8> = (0..CHUNK_BYTES * 5)
            .map(|_| {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                state as u8
            })
            .collect();
        for bytes in [vec![], vec![0; CHUNK_BYTES * 5], random] {
            let compressed = serialize(&bytes).unwrap();
            let restored = decompress::<MAX_ENVIRONMENT_BYTES>(&compressed).unwrap();
            assert_eq!(postcard::from_bytes::<Vec<u8>>(&restored).unwrap(), bytes);
        }
    }

    #[test]
    fn arena_properties_are_rebuilt_when_restoring_a_checkpoint() {
        use kernel::{
            ids::SymbolId,
            metavariables::MetaContext,
            sort::{BaseSort, Sort},
            syntax::{Arena, Node},
        };

        let arena = Arena::new();
        let set = arena.sort(Sort::Base(BaseSort::Set(0)));
        let hole = MetaContext::new().fresh(&arena, vec![], Some(set));
        let open = arena.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain: hole,
            body: arena.bound(3),
        });
        let bytes = decompress::<MAX_ENVIRONMENT_BYTES>(&serialize(&arena).unwrap()).unwrap();
        let restored: Arena = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(restored.max_loose_bound(set), None);
        assert!(!restored.contains_meta(set));
        assert_eq!(restored.max_loose_bound(open), Some(2));
        assert!(restored.contains_meta(open));
        let extended = restored.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain: set,
            body: open,
        });
        assert_eq!(restored.max_loose_bound(extended), Some(1));
        assert!(restored.contains_meta(extended));
    }
}
