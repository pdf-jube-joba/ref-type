//! Deterministic postcard encoding with recursively ordered serde maps.
//!
//! Map keys and values are encoded with the same serializer, then ordered by
//! their bytes. All other types retain postcard's ordinary wire format. Sequence
//! order is meaningful; callers must give sets their own canonical ordering.
use postcard::{Error, Result};
use serde::{Serialize, ser};
use std::{cell::Cell, rc::Rc};

const MAX_DEPTH: usize = 256;
const MAX_ITEMS: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureReason {
    ByteLimit {
        limit: usize,
        used: usize,
        requested: usize,
    },
    ItemLimit {
        limit: usize,
        remaining: usize,
        requested: usize,
    },
    Allocation {
        operation: &'static str,
        requested: usize,
    },
    DepthLimit {
        limit: usize,
    },
}

#[derive(Debug)]
pub struct EncodingError {
    pub error: Error,
    pub reason: Option<FailureReason>,
}

impl std::fmt::Display for EncodingError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}", self.error)?;
        match self.reason {
            Some(FailureReason::ByteLimit {
                limit,
                used,
                requested,
            }) => write!(
                formatter,
                "; byte limit {limit}, used {used}, requested {requested}"
            ),
            Some(FailureReason::ItemLimit {
                limit,
                remaining,
                requested,
            }) => write!(
                formatter,
                "; item limit {limit}, remaining {remaining}, requested {requested}"
            ),
            Some(FailureReason::Allocation {
                operation,
                requested,
            }) => write!(
                formatter,
                "; allocation failed during {operation}, requested {requested}"
            ),
            Some(FailureReason::DepthLimit { limit }) => write!(formatter, "; depth limit {limit}"),
            None => Ok(()),
        }
    }
}
impl std::error::Error for EncodingError {}

/// Serde field adapter for unordered sets. Deserialization uses the ordinary
/// set sequence representation. Sort buffers are limited to 64 MiB in total.
pub fn serialize_set<T, H, S>(
    values: &std::collections::HashSet<T, H>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    T: Serialize,
    H: std::hash::BuildHasher,
    S: ser::Serializer,
{
    use ser::{Error as _, SerializeSeq};
    if values.len() > MAX_ITEMS {
        return Err(S::Error::custom("set element limit exceeded"));
    }
    let mut remaining = 64 * 1024 * 1024;
    let mut ordered = Vec::new();
    ordered
        .try_reserve(values.len())
        .map_err(S::Error::custom)?;
    for value in values {
        let bytes = to_vec(value, remaining).map_err(S::Error::custom)?;
        remaining -= bytes.len();
        ordered.push((bytes, value));
    }
    ordered.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    let mut sequence = serializer.serialize_seq(Some(values.len()))?;
    for (_, value) in ordered {
        sequence.serialize_element(value)?;
    }
    sequence.end()
}

/// Encode at most `limit` bytes, including all temporary map entry buffers.
/// The depth and visited-item limits also bound zero-sized nested metadata.
/// The returned bytes can be decoded by `postcard::from_bytes`.
pub fn to_vec<T: Serialize + ?Sized>(value: &T, limit: usize) -> Result<Vec<u8>> {
    to_vec_detailed(value, limit).map_err(|failure| failure.error)
}

/// The same encoding and limits as `to_vec`, with an outer serializer's
/// resource-limit or allocation failure attached to the postcard error.
pub fn to_vec_detailed<T: Serialize + ?Sized>(
    value: &T,
    limit: usize,
) -> std::result::Result<Vec<u8>, EncodingError> {
    encode_with_limits(value, limit, MAX_ITEMS.max(limit))
}

fn encode_with_limits<T: Serialize + ?Sized>(
    value: &T,
    limit: usize,
    item_limit: usize,
) -> std::result::Result<Vec<u8>, EncodingError> {
    let mut serializer = Encoder {
        bytes: Vec::new(),
        budget: Rc::new(Budget {
            byte_limit: limit,
            item_limit,
            remaining: Cell::new(limit),
            items: Cell::new(item_limit),
            failure: Cell::new(None),
        }),
        depth: 0,
    };
    serializer.value(value).map_err(|error| EncodingError {
        error,
        reason: serializer.budget.failure.get(),
    })?;
    Ok(serializer.bytes)
}

struct Budget {
    byte_limit: usize,
    item_limit: usize,
    remaining: Cell<usize>,
    items: Cell<usize>,
    failure: Cell<Option<FailureReason>>,
}
impl Budget {
    fn fail(&self, reason: FailureReason, error: Error) -> Error {
        if self.failure.get().is_none() {
            self.failure.set(Some(reason));
        }
        error
    }
    fn item_limit(&self, requested: usize) -> Error {
        self.fail(
            FailureReason::ItemLimit {
                limit: self.item_limit,
                remaining: self.items.get(),
                requested,
            },
            Error::SerializeBufferFull,
        )
    }
    fn allocation(&self, operation: &'static str, requested: usize) -> Error {
        self.fail(
            FailureReason::Allocation {
                operation,
                requested,
            },
            Error::SerializeBufferFull,
        )
    }
}
struct Encoder {
    bytes: Vec<u8>,
    budget: Rc<Budget>,
    depth: usize,
}
impl Encoder {
    fn value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        if self.depth >= MAX_DEPTH {
            return Err(self.budget.fail(
                FailureReason::DepthLimit { limit: MAX_DEPTH },
                Error::SerdeSerCustom,
            ));
        }
        self.budget.items.set(
            self.budget
                .items
                .get()
                .checked_sub(1)
                .ok_or_else(|| self.budget.item_limit(1))?,
        );
        self.depth += 1;
        let result = value.serialize(&mut *self);
        self.depth -= 1;
        result
    }
    fn write(&mut self, bytes: &[u8]) -> Result<()> {
        let remaining = self
            .budget
            .remaining
            .get()
            .checked_sub(bytes.len())
            .ok_or_else(|| {
                self.budget.fail(
                    FailureReason::ByteLimit {
                        limit: self.budget.byte_limit,
                        used: self.budget.byte_limit - self.budget.remaining.get(),
                        requested: bytes.len(),
                    },
                    Error::SerializeBufferFull,
                )
            })?;
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| self.budget.allocation("output bytes", bytes.len()))?;
        self.budget.remaining.set(remaining);
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }
    fn temporary<T: Serialize + ?Sized>(&self, value: &T) -> Result<Vec<u8>> {
        let mut encoder = Encoder {
            bytes: Vec::new(),
            budget: self.budget.clone(),
            depth: self.depth,
        };
        encoder.value(value)?;
        Ok(encoder.bytes)
    }
    fn primitive<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        postcard::serialize_with_flavor(value, Output(self))
    }
    fn append_counted(&mut self, mut bytes: Vec<u8>) -> Result<()> {
        // Each byte was charged while building the temporary buffer.
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| self.budget.allocation("map buffer append", bytes.len()))?;
        self.bytes.append(&mut bytes);
        Ok(())
    }
}
struct Output<'a>(&'a mut Encoder);
impl postcard::ser_flavors::Flavor for Output<'_> {
    type Output = ();
    fn try_push(&mut self, byte: u8) -> Result<()> {
        self.0.write(&[byte])
    }
    fn try_extend(&mut self, bytes: &[u8]) -> Result<()> {
        self.0.write(bytes)
    }
    fn finalize(self) -> Result<()> {
        Ok(())
    }
}

macro_rules! primitives {
    ($($method:ident : $ty:ty),* $(,)?) => {$ (
        fn $method(self, value: $ty) -> Result<()> { self.primitive(&value) }
    )*};
}
impl<'a> ser::Serializer for &'a mut Encoder {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Map<'a>;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn is_human_readable(&self) -> bool {
        false
    }
    primitives! {
        serialize_bool: bool, serialize_i8: i8, serialize_i16: i16, serialize_i32: i32,
        serialize_i64: i64, serialize_i128: i128, serialize_u8: u8, serialize_u16: u16,
        serialize_u32: u32, serialize_u64: u64, serialize_u128: u128,
        serialize_f32: f32, serialize_f64: f64, serialize_char: char, serialize_str: &str,
    }
    fn serialize_bytes(self, value: &[u8]) -> Result<()> {
        self.primitive(&value.len())?;
        self.write(value)
    }
    fn serialize_none(self) -> Result<()> {
        self.write(&[0])
    }
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<()> {
        self.write(&[1])?;
        self.value(value)
    }
    fn serialize_unit(self) -> Result<()> {
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        Ok(())
    }
    fn serialize_unit_variant(self, _: &'static str, variant: u32, _: &'static str) -> Result<()> {
        self.primitive(&variant)
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        value: &T,
    ) -> Result<()> {
        self.value(value)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        variant: u32,
        _: &'static str,
        value: &T,
    ) -> Result<()> {
        self.primitive(&variant)?;
        self.value(value)
    }
    fn serialize_seq(self, length: Option<usize>) -> Result<Self> {
        self.primitive(&length.ok_or(Error::SerializeSeqLengthUnknown)?)?;
        Ok(self)
    }
    fn serialize_tuple(self, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        variant: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self> {
        self.primitive(&variant)?;
        Ok(self)
    }
    fn serialize_map(self, length: Option<usize>) -> Result<Map<'a>> {
        let length = length.ok_or(Error::SerializeSeqLengthUnknown)?;
        if length > self.budget.items.get() / 2 {
            return Err(self.budget.item_limit(length.saturating_mul(2)));
        }
        self.primitive(&length)?;
        Ok(Map {
            encoder: self,
            entries: Vec::new(),
            key: None,
            length,
        })
    }
    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        variant: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self> {
        self.primitive(&variant)?;
        Ok(self)
    }
    fn collect_str<T: std::fmt::Display + ?Sized>(self, value: &T) -> Result<()> {
        // Postcard formats in two passes, retaining no unbounded String.
        ser::Serializer::collect_str(
            &mut postcard::Serializer {
                output: Output(self),
            },
            value,
        )
    }
}

macro_rules! compound {
    ($trait:ident, $method:ident $(, $key:ident)?) => {
        impl ser::$trait for &mut Encoder {
            type Ok = ();
            type Error = Error;
            fn $method<T: Serialize + ?Sized>(&mut self, $($key: &'static str,)? value: &T) -> Result<()> {
                $(let _ = $key;)?
                self.value(value)
            }
            fn end(self) -> Result<()> { Ok(()) }
        }
    };
}
compound!(SerializeSeq, serialize_element);
compound!(SerializeTuple, serialize_element);
compound!(SerializeTupleStruct, serialize_field);
compound!(SerializeTupleVariant, serialize_field);
compound!(SerializeStruct, serialize_field, key);
compound!(SerializeStructVariant, serialize_field, key);

struct Map<'a> {
    encoder: &'a mut Encoder,
    entries: Vec<(Vec<u8>, Vec<u8>)>,
    key: Option<Vec<u8>>,
    length: usize,
}
impl ser::SerializeMap for Map<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<()> {
        if self.key.is_some() || self.entries.len() >= self.length {
            return Err(Error::SerdeSerCustom);
        }
        self.key = Some(self.encoder.temporary(key)?);
        Ok(())
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        let key = self.key.take().ok_or(Error::SerdeSerCustom)?;
        let value = self.encoder.temporary(value)?;
        self.entries
            .try_reserve(1)
            .map_err(|_| self.encoder.budget.allocation("map entries", 1))?;
        self.entries.push((key, value));
        Ok(())
    }
    fn end(mut self) -> Result<()> {
        if self.key.is_some() || self.entries.len() != self.length {
            return Err(Error::SerdeSerCustom);
        }
        self.entries.sort_unstable();
        for (key, value) in self.entries {
            self.encoder.append_counted(key)?;
            self.encoder.append_counted(value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::collections::HashMap;

    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Document {
        tuples: Vec<(i32, Option<String>)>,
        variants: HashMap<String, Variant>,
    }
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    enum Variant {
        Unit,
        Newtype(HashMap<u64, i128>),
        Tuple(u8, HashMap<u64, i128>),
        Struct {
            flag: bool,
            nested: HashMap<u64, i128>,
        },
    }
    fn document(reverse: bool) -> Document {
        let values = [(1, -10), (128, i128::MIN), (16_384, i128::MAX)];
        let nested = || -> HashMap<u64, i128> {
            if reverse {
                values.into_iter().rev().collect()
            } else {
                values.into_iter().collect()
            }
        };
        let entries = [
            ("a".into(), Variant::Newtype(nested())),
            ("b".into(), Variant::Tuple(77, nested())),
            (
                "c".into(),
                Variant::Struct {
                    flag: true,
                    nested: nested(),
                },
            ),
            ("d".into(), Variant::Unit),
        ];
        Document {
            tuples: vec![(i32::MIN, None), (i32::MAX, Some("日本語".into()))],
            variants: if reverse {
                entries.into_iter().rev().collect()
            } else {
                entries.into_iter().collect()
            },
        }
    }
    #[test]
    fn hash_seeds_and_insertion_order_do_not_change_nested_map_bytes() {
        let expected = to_vec(&document(false), 10000).unwrap();
        for index in 0..20 {
            let value = document(index % 2 == 0);
            let encoded = to_vec(&value, 10000).unwrap();
            assert_eq!(encoded, expected);
            assert_eq!(postcard::from_bytes::<Document>(&encoded).unwrap(), value);
        }
    }
    #[test]
    fn non_map_wire_matches_postcard_including_numeric_boundaries() {
        let primitives = (
            (true, i8::MIN, i16::MIN, i32::MIN, i64::MIN, i128::MIN),
            (u8::MAX, u16::MAX, u32::MAX, u64::MAX, u128::MAX),
            (f32::MIN, f64::MAX, '界', "é"),
            (Some(5u16), None::<u16>, (), vec![1u8, 0, 255]),
        );
        assert_eq!(
            to_vec(&primitives, 10000).unwrap(),
            postcard::to_allocvec(&primitives).unwrap()
        );
    }
    #[test]
    fn budget_counts_nested_temporary_bytes_once_and_rejects_overflow() {
        let value = document(true);
        let size = to_vec(&value, 10000).unwrap().len();
        assert_eq!(to_vec(&value, size).unwrap().len(), size);
        assert_eq!(to_vec(&value, size - 1), Err(Error::SerializeBufferFull));
        assert_eq!(to_vec(&(), 0).unwrap(), Vec::<u8>::new());
        assert_eq!(to_vec(&"huge", 2), Err(Error::SerializeBufferFull));
    }
    #[test]
    fn detailed_failures_distinguish_byte_and_item_limits() {
        let failure = to_vec_detailed(&"huge", 2).unwrap_err();
        assert_eq!(failure.error, Error::SerializeBufferFull);
        assert_eq!(
            failure.reason,
            Some(FailureReason::ByteLimit {
                limit: 2,
                used: 1,
                requested: 4,
            })
        );
        let failure = encode_with_limits(&[(), ()], 100, 2).unwrap_err();
        assert_eq!(failure.error, Error::SerializeBufferFull);
        assert_eq!(
            failure.reason,
            Some(FailureReason::ItemLimit {
                limit: 2,
                remaining: 0,
                requested: 1,
            })
        );
        let map = HashMap::from([(1u8, 2u8), (3, 4)]);
        let failure = encode_with_limits(&map, 100, 4).unwrap_err();
        assert_eq!(
            failure.reason,
            Some(FailureReason::ItemLimit {
                limit: 4,
                remaining: 3,
                requested: 4,
            })
        );
        let document = document(false);
        assert_eq!(
            to_vec_detailed(&document, 10000).unwrap(),
            to_vec(&document, 10000).unwrap()
        );
    }
    #[test]
    fn deeply_nested_metadata_stops_at_depth_limit() {
        #[derive(Serialize)]
        struct Nested {
            next: Option<Box<Nested>>,
        }
        let mut value = Nested { next: None };
        for _ in 0..300 {
            value = Nested {
                next: Some(Box::new(value)),
            };
        }
        assert_eq!(to_vec(&value, 10000), Err(Error::SerdeSerCustom));
    }
    #[test]
    fn custom_map_serializer_order_is_canonicalized() {
        struct Entries(bool);
        impl Serialize for Entries {
            fn serialize<S: ser::Serializer>(
                &self,
                serializer: S,
            ) -> std::result::Result<S::Ok, S::Error> {
                use ser::SerializeMap;
                let mut map = serializer.serialize_map(Some(2))?;
                let values = if self.0 {
                    [(2u8, 3u8), (1, 4)]
                } else {
                    [(1u8, 4u8), (2, 3)]
                };
                for (key, value) in values {
                    map.serialize_key(&key)?;
                    map.serialize_value(&value)?;
                }
                map.end()
            }
        }
        assert_eq!(
            to_vec(&Entries(true), 100).unwrap(),
            to_vec(&Entries(false), 100).unwrap()
        );
    }
    #[test]
    fn unordered_set_adapter_is_stable_and_round_trips() {
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        struct Saved {
            #[serde(serialize_with = "serialize_set")]
            values: std::collections::HashSet<String>,
        }
        let first = Saved {
            values: ["a", "b", "long"].into_iter().map(str::to_owned).collect(),
        };
        let second = Saved {
            values: ["long", "b", "a"].into_iter().map(str::to_owned).collect(),
        };
        let encoded = to_vec(&first, 100).unwrap();
        assert_eq!(encoded, to_vec(&second, 100).unwrap());
        assert_eq!(postcard::from_bytes::<Saved>(&encoded).unwrap(), first);
    }

    #[test]
    fn byte_and_display_serializers_match_postcard_without_intermediate_strings() {
        struct Bytes;
        impl Serialize for Bytes {
            fn serialize<S: ser::Serializer>(
                &self,
                serializer: S,
            ) -> std::result::Result<S::Ok, S::Error> {
                serializer.serialize_bytes(&[0, 255, 128, 1])
            }
        }
        struct Displayed;
        impl Serialize for Displayed {
            fn serialize<S: ser::Serializer>(
                &self,
                serializer: S,
            ) -> std::result::Result<S::Ok, S::Error> {
                serializer.collect_str(&format_args!("prefix {} suffix", 12345))
            }
        }
        assert_eq!(
            to_vec(&Bytes, 100).unwrap(),
            postcard::to_allocvec(&Bytes).unwrap()
        );
        assert_eq!(
            to_vec(&Displayed, 100).unwrap(),
            postcard::to_allocvec(&Displayed).unwrap()
        );
        assert!(to_vec(&Displayed, 2).is_err());
    }
}
