//! Streaming native checkpoints with bounded compressed and decoded buffers.
use postcard::{Error, Result, ser_flavors::Flavor};
use std::io::{self, Write};

const CHUNK_BYTES: usize = 32 * 1024;

#[derive(Default)]
struct BoundedBytes<const LIMIT: usize>(Vec<u8>);

impl<const LIMIT: usize> Write for BoundedBytes<LIMIT> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > LIMIT - self.0.len() {
            return Err(io::Error::other("checkpoint size limit exceeded"));
        }
        self.0.try_reserve(bytes.len()).map_err(io::Error::other)?;
        self.0.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(super) struct Buffer<const LIMIT: usize> {
    encoder: zstd::stream::write::Encoder<'static, BoundedBytes<LIMIT>>,
    input: Vec<u8>,
    uncompressed: usize,
}

impl<const LIMIT: usize> Buffer<LIMIT> {
    pub(super) fn new() -> Result<Self> {
        let mut input = Vec::new();
        input
            .try_reserve_exact(CHUNK_BYTES)
            .map_err(|_| Error::SerializeBufferFull)?;
        // Favor checkpoint throughput while keeping the compressed size bounded.
        let encoder = zstd::stream::write::Encoder::new(BoundedBytes::default(), -3)
            .map_err(|_| Error::SerializeBufferFull)?;
        Ok(Self {
            encoder,
            input,
            uncompressed: 0,
        })
    }

    fn flush(&mut self) -> Result<()> {
        let _cost = timing::costs::Scope::enter("query.checkpoint-compress");
        self.encoder
            .write_all(&self.input)
            .map_err(|_| Error::SerializeBufferFull)?;
        self.input.clear();
        Ok(())
    }

    #[cold]
    fn extend_chunks(&mut self, mut bytes: &[u8]) -> Result<()> {
        while !bytes.is_empty() {
            let count = bytes.len().min(CHUNK_BYTES - self.input.len());
            self.input.extend_from_slice(&bytes[..count]);
            bytes = &bytes[count..];
            if self.input.len() == CHUNK_BYTES {
                self.flush()?;
            }
        }
        Ok(())
    }
}

impl<const LIMIT: usize> Flavor for Buffer<LIMIT> {
    type Output = Vec<u8>;

    #[inline]
    fn try_push(&mut self, byte: u8) -> Result<()> {
        if self.uncompressed == LIMIT {
            return Err(Error::SerializeBufferFull);
        }
        self.uncompressed += 1;
        self.input.push(byte);
        if self.input.len() == CHUNK_BYTES {
            self.flush()?;
        }
        Ok(())
    }

    #[inline]
    fn try_extend(&mut self, bytes: &[u8]) -> Result<()> {
        if bytes.len() > LIMIT - self.uncompressed {
            return Err(Error::SerializeBufferFull);
        }
        self.uncompressed += bytes.len();
        // Most writes are short varints. Keep their copy out of the chunk loop.
        if bytes.len() < CHUNK_BYTES - self.input.len() {
            self.input.extend_from_slice(bytes);
            Ok(())
        } else {
            self.extend_chunks(bytes)
        }
    }

    fn finalize(mut self) -> Result<Vec<u8>> {
        self.flush()?;
        let _cost = timing::costs::Scope::enter("query.checkpoint-compress");
        Ok(self
            .encoder
            .finish()
            .map_err(|_| Error::SerializeBufferFull)?
            .0)
    }
}

pub(crate) fn decompress<const LIMIT: usize>(bytes: &[u8]) -> Option<Vec<u8>> {
    if bytes.is_empty() || bytes.len() > LIMIT {
        return None;
    }
    let mut decoder = zstd::stream::read::Decoder::new(bytes).ok()?;
    // Fast checkpoints use a smaller window; bound decoder scratch space too.
    decoder.window_log_max(23).ok()?;
    let mut output = BoundedBytes::<LIMIT>::default();
    io::copy(&mut decoder, &mut output).ok()?;
    Some(output.0)
}
