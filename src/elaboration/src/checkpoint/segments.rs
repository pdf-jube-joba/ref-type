//! Content-defined checkpoint segments keep publication and decoding buffers
//! bounded while unchanged metadata shares content-addressed objects.
use kernel::graph_store::GraphStore;
use postcard::{Error, Result, ser_flavors::Flavor};
use std::{
    io::{self, Read},
    rc::Rc,
};

pub(super) const MAGIC: &[u8; 8] = b"REFCHNK1";
const MIN: usize = 16 * 1024;
const MAX: usize = 128 * 1024;

#[derive(serde::Serialize, serde::Deserialize)]
struct Index {
    bytes: u64,
    segments: Vec<Vec<u8>>,
}

pub(super) struct Buffer {
    store: Rc<dyn GraphStore>,
    index: Index,
    buffer: Vec<u8>,
    hash: u64,
}
impl Buffer {
    pub(super) fn new(store: Rc<dyn GraphStore>) -> Self {
        Self {
            store,
            index: Index {
                bytes: 0,
                segments: Vec::new(),
            },
            buffer: Vec::with_capacity(MAX),
            hash: 0,
        }
    }
    fn flush(&mut self) -> Result<()> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        let reference = self
            .store
            .write(&self.buffer)
            .map_err(|_| Error::SerializeBufferFull)?;
        self.index.segments.push(reference);
        self.buffer.clear();
        self.hash = 0;
        Ok(())
    }
}
impl Flavor for Buffer {
    type Output = Vec<u8>;
    fn try_push(&mut self, byte: u8) -> Result<()> {
        self.buffer.push(byte);
        self.index.bytes += 1;
        // A rolling gear hash resynchronizes boundaries after inserted fields.
        let mut gear = u64::from(byte).wrapping_add(0x9e3779b97f4a7c15);
        gear = (gear ^ (gear >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        gear = (gear ^ (gear >> 27)).wrapping_mul(0x94d049bb133111eb);
        self.hash = self.hash.wrapping_shl(1).wrapping_add(gear ^ (gear >> 31));
        if self.buffer.len() >= MAX || (self.buffer.len() >= MIN && self.hash & 0xffff == 0) {
            self.flush()?;
        }
        Ok(())
    }
    fn finalize(mut self) -> Result<Vec<u8>> {
        self.flush()?;
        postcard::to_extend(&self.index, MAGIC.to_vec())
    }
}

struct Reader {
    store: Rc<dyn GraphStore>,
    segments: std::vec::IntoIter<Vec<u8>>,
    current: io::Cursor<Vec<u8>>,
    remaining: u64,
}
impl Read for Reader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        if buffer.is_empty() {
            return Ok(0);
        }
        loop {
            let count = self.current.read(buffer)?;
            if count != 0 {
                self.remaining = self
                    .remaining
                    .checked_sub(count as u64)
                    .ok_or_else(|| io::Error::other("checkpoint length mismatch"))?;
                return Ok(count);
            }
            let Some(reference) = self.segments.next() else {
                return if self.remaining == 0 {
                    Ok(0)
                } else {
                    Err(io::Error::other("truncated checkpoint"))
                };
            };
            let bytes = self.store.read(&reference)?;
            if bytes.is_empty() || bytes.len() > MAX {
                return Err(io::Error::other("invalid checkpoint segment"));
            }
            self.current = io::Cursor::new(bytes);
        }
    }
}

pub(super) fn deserialize<T: serde::de::DeserializeOwned>(
    bytes: &[u8],
    store: Rc<dyn GraphStore>,
) -> Option<T> {
    let index: Index = postcard::from_bytes(bytes.strip_prefix(MAGIC)?).ok()?;
    if index.bytes > (index.segments.len() as u64).checked_mul(MAX as u64)? {
        return None;
    }
    let reader = Reader {
        store,
        segments: index.segments.into_iter(),
        current: io::Cursor::new(Vec::new()),
        remaining: index.bytes,
    };
    let mut scratch = vec![0; 1024 * 1024];
    let (value, (mut reader, _)) = postcard::from_io::<T, _>((reader, &mut scratch)).ok()?;
    (reader.read(&mut [0]).ok()? == 0).then_some(value)
}
