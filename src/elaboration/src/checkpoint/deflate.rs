//! Portable checkpoint compression for WebAssembly.
use postcard::{Error, Result, ser_flavors::Flavor};

const CHUNK_BYTES: usize = 32 * 1024;

pub(super) struct Buffer<const LIMIT: usize> {
    compressor: miniz_oxide::deflate::core::CompressorOxide,
    input: Vec<u8>,
    compressed: Vec<u8>,
    uncompressed: usize,
}

impl<const LIMIT: usize> Buffer<LIMIT> {
    pub(super) fn new() -> Result<Self> {
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

pub(crate) fn decompress<const LIMIT: usize>(bytes: &[u8]) -> Option<Vec<u8>> {
    miniz_oxide::inflate::decompress_to_vec_with_limit(bytes, LIMIT).ok()
}
