//! Bounded serialization of a checking environment.
use postcard::{Error, Result, ser_flavors::Flavor};
use serde::Serialize;

pub const MAX_ENVIRONMENT_BYTES: usize = 16 * 1024 * 1024;

const CHUNK_BYTES: usize = 32 * 1024;

struct Buffer<const LIMIT: usize> {
    compressor: miniz_oxide::deflate::core::CompressorOxide,
    input: Vec<u8>,
    compressed: Vec<u8>,
    uncompressed: usize,
}

impl<const LIMIT: usize> Buffer<LIMIT> {
    fn new() -> Result<Self> {
        let mut input = Vec::new();
        input
            .try_reserve_exact(CHUNK_BYTES)
            .map_err(|_| Error::SerializeBufferFull)?;
        Ok(Self {
            compressor: miniz_oxide::deflate::core::CompressorOxide::new(
                miniz_oxide::deflate::core::create_comp_flags_from_zip_params(1, 0, 0),
            ),
            input,
            compressed: Vec::new(),
            uncompressed: 0,
        })
    }

    fn flush(&mut self, finish: bool) -> Result<()> {
        use miniz_oxide::deflate::core::{TDEFLFlush, TDEFLStatus, compress};
        let mut output = [0; CHUNK_BYTES];
        let mut position = 0;
        loop {
            let (status, consumed, produced) = compress(
                &mut self.compressor,
                &self.input[position..],
                &mut output,
                if finish {
                    TDEFLFlush::Finish
                } else {
                    TDEFLFlush::None
                },
            );
            position += consumed;
            if produced > LIMIT - self.compressed.len() {
                return Err(Error::SerializeBufferFull);
            }
            self.compressed
                .try_reserve(produced)
                .map_err(|_| Error::SerializeBufferFull)?;
            self.compressed.extend_from_slice(&output[..produced]);
            match status {
                TDEFLStatus::Done if finish => break,
                TDEFLStatus::Okay if !finish && position == self.input.len() => break,
                TDEFLStatus::Okay if consumed != 0 || produced != 0 => {}
                _ => return Err(Error::SerializeBufferFull),
            }
        }
        self.input.clear();
        Ok(())
    }
}

impl<const LIMIT: usize> Flavor for Buffer<LIMIT> {
    type Output = Vec<u8>;

    fn try_push(&mut self, byte: u8) -> Result<()> {
        self.try_extend(&[byte])
    }

    fn try_extend(&mut self, mut bytes: &[u8]) -> Result<()> {
        if bytes.len() > LIMIT - self.uncompressed {
            return Err(Error::SerializeBufferFull);
        }
        self.uncompressed += bytes.len();
        while !bytes.is_empty() {
            let count = bytes.len().min(CHUNK_BYTES - self.input.len());
            self.input.extend_from_slice(&bytes[..count]);
            bytes = &bytes[count..];
            if self.input.len() == CHUNK_BYTES {
                self.flush(false)?;
            }
        }
        Ok(())
    }

    fn finalize(mut self) -> Result<Self::Output> {
        self.flush(true)?;
        Ok(self.compressed)
    }
}

pub(crate) fn serialize(value: &impl Serialize) -> Result<Vec<u8>> {
    serialize_bounded::<MAX_ENVIRONMENT_BYTES>(value)
}

pub(crate) fn serialize_bounded<const LIMIT: usize>(value: &impl Serialize) -> Result<Vec<u8>> {
    // Feed serialization straight into the compressor. The live environment
    // coexists only with a fixed input chunk and the compressed checkpoint.
    let _phase = crate::profiling::Phase::start("environment.serialize-compress");
    postcard::serialize_with_flavor(value, Buffer::<LIMIT>::new()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streaming_checkpoints_cross_input_and_output_chunk_boundaries() {
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
            let restored = miniz_oxide::inflate::decompress_to_vec_with_limit(
                &compressed,
                MAX_ENVIRONMENT_BYTES,
            )
            .unwrap();
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
