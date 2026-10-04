//! Bounded serialization of a checking environment.
use postcard::{Error, Result, ser_flavors::Flavor};
use serde::Serialize;

pub const MAX_ENVIRONMENT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Default)]
struct Buffer(Vec<u8>);
impl Flavor for Buffer {
    type Output = Vec<u8>;

    fn try_push(&mut self, byte: u8) -> Result<()> {
        self.try_extend(&[byte])
    }

    fn try_extend(&mut self, bytes: &[u8]) -> Result<()> {
        if bytes.len() > MAX_ENVIRONMENT_BYTES - self.0.len() {
            return Err(Error::SerializeBufferFull);
        }
        self.0
            .try_reserve(bytes.len())
            .map_err(|_| Error::SerializeBufferFull)?;
        self.0.extend_from_slice(bytes);
        Ok(())
    }

    fn finalize(self) -> Result<Self::Output> {
        Ok(self.0)
    }
}

pub(crate) fn serialize(value: &impl Serialize) -> Result<Vec<u8>> {
    let bytes: Vec<u8> = {
        let _phase = crate::profiling::Phase::start("environment.serialize");
        postcard::serialize_with_flavor(value, Buffer::default())?
    };
    let compressed = {
        let _phase = crate::profiling::Phase::start("environment.compress");
        miniz_oxide::deflate::compress_to_vec(&bytes, 1)
    };
    if compressed.len() > MAX_ENVIRONMENT_BYTES {
        return Err(Error::SerializeBufferFull);
    }
    Ok(compressed)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let bytes = miniz_oxide::inflate::decompress_to_vec_with_limit(
            &serialize(&arena).unwrap(),
            MAX_ENVIRONMENT_BYTES,
        )
        .unwrap();
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

    #[test]
    fn serialization_stops_at_the_checkpoint_budget() {
        let data = vec![0_u8; MAX_ENVIRONMENT_BYTES];
        assert_eq!(serialize(&data), Err(Error::SerializeBufferFull));
        let small = vec![1_u8, 2, 3];
        assert_eq!(
            postcard::from_bytes::<Vec<u8>>(
                &miniz_oxide::inflate::decompress_to_vec_with_limit(
                    &serialize(&small).unwrap(),
                    MAX_ENVIRONMENT_BYTES
                )
                .unwrap()
            )
            .unwrap(),
            small
        );
    }
}
