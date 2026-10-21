//! Content addressed package objects, atomic manifests, and session protected collection.
use crate::{
    cache::{Fingerprint, fingerprint},
    error::{CacheError, CacheOperation},
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::{
        Mutex,
        atomic::{AtomicU64, Ordering},
    },
    time::{Duration, Instant, SystemTime},
};

pub const DEFAULT_CACHE_BUDGET: u64 = u64::MAX;
const MAX_OBJECT: u64 = 512 * 1024 * 1024;
const MAX_MANIFEST: u64 = 16 * 1024 * 1024;
const HEADER: usize = 60;
const MAGIC: &[u8; 8] = b"REFOBJ02";
static NEXT: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum ObjectKind {
    Result = 1,
    Resolver = 2,
    Environment = 3,
    Checkpoint = 4,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectRef {
    pub digest: Fingerprint,
    pub kind: ObjectKind,
    pub stored_bytes: u64,
    pub decoded_bytes: u64,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoreManifest {
    pub key: Fingerprint,
    pub input: Fingerprint,
    pub coverage: Vec<Vec<String>>,
    pub dependencies: Vec<Fingerprint>,
    pub results: Vec<(Vec<String>, ObjectRef)>,
    pub resolver: Option<ObjectRef>,
    pub environment: Option<ObjectRef>,
    pub checkpoint: Option<ObjectRef>,
    #[serde(default)]
    pub graph: Vec<ObjectRef>,
}
impl StoreManifest {
    fn objects(&self) -> impl Iterator<Item = &ObjectRef> {
        self.results
            .iter()
            .map(|(_, object)| object)
            .chain(self.resolver.iter())
            .chain(self.environment.iter())
            .chain(self.checkpoint.iter())
            .chain(self.graph.iter())
    }
}
/// Reference counts preserve the oldest currently eligible eviction order without
/// rescanning every manifest for each dependency and object being removed.
struct CollectionIndex {
    dependencies: BTreeMap<Fingerprint, usize>,
    objects: BTreeMap<Fingerprint, usize>,
    ranks: BTreeMap<(Fingerprint, bool), usize>,
    eligible: BTreeSet<usize>,
}
impl CollectionIndex {
    fn new(
        records: &BTreeMap<(Fingerprint, bool), StoreManifest>,
        candidates: &[(Fingerprint, bool)],
    ) -> Self {
        let mut dependencies = BTreeMap::new();
        let mut objects = BTreeMap::new();
        for manifest in records.values() {
            for dependency in &manifest.dependencies {
                *dependencies.entry(*dependency).or_default() += 1;
            }
            for object in manifest.objects() {
                *objects.entry(object.digest).or_default() += 1;
            }
        }
        let ranks: BTreeMap<_, _> = candidates
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, key)| (key, rank))
            .collect();
        let eligible = candidates
            .iter()
            .enumerate()
            .filter_map(|(rank, (key, checkpoint))| {
                (*checkpoint || !dependencies.contains_key(key)).then_some(rank)
            })
            .collect();
        Self {
            dependencies,
            objects,
            ranks,
            eligible,
        }
    }
    fn remove(
        &mut self,
        key: (Fingerprint, bool),
        manifest: &StoreManifest,
    ) -> BTreeSet<Fingerprint> {
        self.ranks.remove(&key);
        for dependency in &manifest.dependencies {
            let count = self.dependencies.get_mut(dependency).unwrap();
            *count -= 1;
            if *count == 0
                && let Some(rank) = self.ranks.get(&(*dependency, false))
            {
                self.eligible.insert(*rank);
            }
        }
        let mut orphaned = BTreeSet::new();
        for object in manifest.objects() {
            let count = self.objects.get_mut(&object.digest).unwrap();
            *count -= 1;
            if *count == 0 {
                orphaned.insert(object.digest);
            }
        }
        orphaned
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MissReason {
    Missing,
    Format,
    Corrupt,
    SizeLimit,
    InputMismatch,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CacheStoreStats {
    pub result_read_bytes: u64,
    pub result_write_bytes: u64,
    pub environment_read_bytes: u64,
    pub environment_write_bytes: u64,
    pub result_hits: u64,
    pub environment_imports: u64,
    pub checkpoint_resumes: u64,
    pub missing: u64,
    pub format_misses: u64,
    pub corrupt: u64,
    pub size_limits: u64,
    pub save_failures: u64,
    pub last_save_error: Option<String>,
    pub input_mismatches: u64,
    pub relocation_time: Duration,
    pub shared_objects: u64,
    pub collected_bytes: u64,
    pub compression_time: Duration,
    pub decompression_time: Duration,
    pub retained_bytes: u64,
    pub retained_bytes_is_upper_bound: bool,
    pub budget_excess_bytes: u64,
}
impl CacheStoreStats {
    /// Accumulate I/O across workers and publication; retention describes the
    /// most recently observed store, rather than adding repeated snapshots.
    pub fn merge(&mut self, other: &Self) {
        macro_rules! add {
            ($($field:ident),* $(,)?) => {$(self.$field += other.$field;)*};
        }
        add!(
            result_read_bytes,
            result_write_bytes,
            environment_read_bytes,
            environment_write_bytes,
            result_hits,
            environment_imports,
            checkpoint_resumes,
            missing,
            format_misses,
            corrupt,
            size_limits,
            save_failures,
            input_mismatches,
            relocation_time,
            shared_objects,
            collected_bytes,
            compression_time,
            decompression_time,
        );
        if other.last_save_error.is_some() {
            self.last_save_error.clone_from(&other.last_save_error);
        }
        if other.retained_bytes != 0 {
            self.retained_bytes = other.retained_bytes;
            self.retained_bytes_is_upper_bound = other.retained_bytes_is_upper_bound;
            self.budget_excess_bytes = other.budget_excess_bytes;
        }
    }
}
#[derive(Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
struct Pins {
    artifacts: BTreeSet<Fingerprint>,
    checkpoints: BTreeSet<Fingerprint>,
    objects: BTreeSet<Fingerprint>,
    #[serde(default)]
    read_objects: BTreeSet<Fingerprint>,
}
struct Lease {
    path: PathBuf,
    _file: File,
    pins: Pins,
    owner: bool,
    generation: u64,
}
impl Drop for Lease {
    fn drop(&mut self) {
        if self.owner {
            let _ = fs::remove_file(self.path.with_extension("pins"));
            let _ = fs::remove_file(self.path.with_extension("objects"));
            let _ = fs::remove_file(&self.path);
        }
    }
}

pub struct ArtifactStore {
    root: PathBuf,
    budget: AtomicU64,
    pending_bytes: AtomicU64,
    lease: Mutex<Option<Lease>>,
    stats: Mutex<CacheStoreStats>,
}
impl Drop for ArtifactStore {
    fn drop(&mut self) {
        // Only the lease owner ends a session. A supervised worker borrows that
        // lease; collecting on every worker exit repeatedly scans the whole store
        // while its artifacts remain protected by the supervisor anyway.
        let ended_session = self
            .lease
            .get_mut()
            .unwrap()
            .take()
            .is_some_and(|lease| lease.owner);
        let usage = self.root.join("usage");
        let collection_needed = self.pending_bytes.load(Ordering::Relaxed) != 0
            || read_bounded(&usage, 8)
                .ok()
                .and_then(|bytes| bytes.try_into().ok())
                .map(u64::from_le_bytes)
                .is_none_or(|usage| usage > self.budget.load(Ordering::Relaxed))
            // Periodically reclaim abandoned publications left by killed writers.
            || fs::metadata(&usage)
                .and_then(|metadata| metadata.modified())
                .ok()
                .and_then(|modified| modified.elapsed().ok())
                .is_none_or(|age| age >= Duration::from_secs(60));
        if ended_session && collection_needed && self.root.is_dir() {
            let _ = self.collect();
        }
    }
}
fn hex(key: &Fingerprint) -> String {
    key.iter().map(|b| format!("{b:02x}")).collect()
}
fn io_error(operation: CacheOperation, path: &Path, source: std::io::Error) -> CacheError {
    CacheError::Io {
        operation,
        path: path.to_owned(),
        source,
    }
}
fn invalid(reason: MissReason) -> CacheError {
    CacheError::Invalid(reason)
}
pub fn serialize<T: Serialize>(value: &T) -> Result<Vec<u8>, CacheError> {
    postcard::to_allocvec(value).map_err(|e| CacheError::Codec(e.to_string()))
}
pub fn deserialize<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, CacheError> {
    postcard::from_bytes(bytes).map_err(|e| CacheError::Codec(e.to_string()))
}

impl ArtifactStore {
    pub fn new(directory: impl Into<PathBuf>) -> Self {
        Self {
            root: directory.into(),
            budget: AtomicU64::new(DEFAULT_CACHE_BUDGET),
            pending_bytes: AtomicU64::new(0),
            lease: Mutex::new(None),
            stats: Mutex::new(CacheStoreStats::default()),
        }
    }
    pub fn directory(&self) -> &Path {
        &self.root
    }

    pub fn set_budget(&self, bytes: u64) {
        self.budget.store(bytes, Ordering::Relaxed);
    }
    /// Remember the last observed input for an instance, including across processes.
    /// This small diagnostic index never authorizes reuse of an artifact.
    pub fn observe_input(
        &self,
        instance: &Fingerprint,
        input: &Fingerprint,
    ) -> Result<(), CacheError> {
        self.failure(
            (|| {
                let _lock = self.lock()?;
                let path = self.root.join("instances").join(hex(instance));
                let previous = read_bounded(&path, 32)
                    .ok()
                    .filter(|bytes| bytes.len() == 32);
                if previous.as_deref() == Some(input.as_slice()) {
                    return Ok(());
                }
                if previous.is_some() {
                    self.record_input_mismatch();
                }
                self.atomic_metadata(&path, input)
            })(),
            true,
        )
    }

    pub fn record_input_mismatch(&self) {
        self.stats.lock().unwrap().input_mismatches += 1;
    }
    pub fn record_export_failure(&self, message: impl std::fmt::Display) {
        let mut stats = self.stats.lock().unwrap();
        stats.save_failures += 1;
        stats.last_save_error = Some(message.to_string());
    }
    pub fn record_relocation(&self, elapsed: Duration) {
        self.stats.lock().unwrap().relocation_time += elapsed;
    }
    pub fn stats(&self) -> CacheStoreStats {
        let mut stats = self.stats.lock().unwrap().clone();
        // Read-only warm sessions still report the cache retained by earlier writers.
        // The counter is atomically replaced, so no store lock or directory scan is needed.
        if let Some(usage) = read_bounded(&self.root.join("usage"), 8)
            .ok()
            .and_then(|bytes| bytes.try_into().ok())
            .map(u64::from_le_bytes)
        {
            stats.retained_bytes = usage;
            stats.retained_bytes_is_upper_bound = true;
        }
        stats.budget_excess_bytes = stats
            .retained_bytes
            .saturating_sub(self.budget.load(Ordering::Relaxed));
        stats
    }
    /// Keep this store alive in a supervisor and pass the token to sequential workers.
    pub fn session_token(&self) -> Result<String, CacheError> {
        let _lock = self.lock()?;
        self.pin(|_| false)?;
        Ok(self
            .lease
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned())
    }
    /// End the current checking session once callers own all imported bytes.
    pub fn release_pins(&self) -> Result<(), CacheError> {
        let _lock = self.lock()?;
        self.pin(|_| false)?;
        if self
            .lease
            .lock()
            .unwrap()
            .as_ref()
            .is_some_and(|lease| !lease.owner)
        {
            return Ok(());
        }
        self.pin(|pins| {
            *pins = Pins::default();
            true
        })?;
        remove(
            &self
                .lease
                .lock()
                .unwrap()
                .as_ref()
                .unwrap()
                .path
                .with_extension("objects"),
        )
    }
    fn lock(&self) -> Result<File, CacheError> {
        fs::create_dir_all(&self.root)
            .map_err(|e| io_error(CacheOperation::CreateDirectory, &self.root, e))?;
        let path = self.root.join("store.lock");
        let file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&path)
            .map_err(|e| io_error(CacheOperation::Lock, &path, e))?;
        file.lock()
            .map_err(|e| io_error(CacheOperation::Lock, &path, e))?;
        Ok(file)
    }
    fn object_path(&self, digest: &Fingerprint) -> PathBuf {
        let key = hex(digest);
        self.root.join("objects").join(&key[..2]).join(key)
    }
    fn input_directory(&self, input: &Fingerprint) -> PathBuf {
        let input = hex(input);
        self.root.join("inputs").join(&input[..2]).join(input)
    }
    fn manifest_path(&self, key: &Fingerprint, checkpoint: bool) -> PathBuf {
        let key = hex(key);
        self.root
            .join(if checkpoint {
                "checkpoints"
            } else {
                "artifacts"
            })
            .join(&key[..2])
            .join(format!(
                "{key}.{}",
                if checkpoint { "checkpoint" } else { "manifest" }
            ))
    }
    // Called under store.lock; the lease's separate advisory lock is its liveness token.
    fn pin(&self, update: impl FnOnce(&mut Pins) -> bool) -> Result<(), CacheError> {
        let mut lease = self.lease.lock().unwrap();
        if lease.is_none() {
            let dir = self.root.join("leases");
            fs::create_dir_all(&dir)
                .map_err(|e| io_error(CacheOperation::CreateDirectory, &dir, e))?;
            if let Ok(token) = std::env::var("REF_TYPE_CACHE_SESSION")
                && !token.is_empty()
                && token
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            {
                let path = dir.join(token);
                if let Ok(file) = OpenOptions::new().read(true).write(true).open(&path)
                    && matches!(file.try_lock(), Err(std::fs::TryLockError::WouldBlock))
                {
                    *lease = Some(Lease {
                        path,
                        _file: file,
                        pins: Pins::default(),
                        owner: false,
                        generation: 0,
                    });
                }
            }
        }
        if lease.is_none() {
            let dir = self.root.join("leases");
            let (path, file) = loop {
                let path = dir.join(format!(
                    "{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match OpenOptions::new()
                    .create_new(true)
                    .read(true)
                    .write(true)
                    .open(&path)
                {
                    Ok(file) => break (path, file),
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(e) => return Err(io_error(CacheOperation::WriteRecord, &path, e)),
                }
            };
            file.lock()
                .map_err(|e| io_error(CacheOperation::Lock, &path, e))?;
            *lease = Some(Lease {
                path,
                _file: file,
                pins: Pins::default(),
                owner: true,
                generation: 0,
            });
        }
        let lease = lease.as_mut().unwrap();
        // Pin data is atomically replaced separately from the persistent liveness lock.
        // Killing a worker during publication cannot truncate its supervisor's pins.
        let pin_path = lease.path.with_extension("pins");
        match File::open(&pin_path) {
            Ok(mut file) => {
                let mut generation = [0; 8];
                file.read_exact(&mut generation)
                    .map_err(|e| io_error(CacheOperation::ReadRecord, &pin_path, e))?;
                let generation = u64::from_le_bytes(generation);
                if generation == 0 {
                    return Err(invalid(MissReason::Corrupt));
                }
                if generation != lease.generation {
                    lease.pins = serde_json::from_reader(file.take(MAX_MANIFEST))?;
                    lease.generation = generation;
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                lease.generation = 0;
            }
            Err(error) => return Err(io_error(CacheOperation::ReadRecord, &pin_path, error)),
        }
        let changed = update(&mut lease.pins);
        if !changed && lease.generation != 0 {
            return Ok(());
        }
        let generation = lease
            .generation
            .checked_add(1)
            .ok_or_else(|| invalid(MissReason::SizeLimit))?;
        let mut bytes = generation.to_le_bytes().to_vec();
        bytes.extend(serde_json::to_vec(&lease.pins)?);
        lease.generation = 0;
        self.atomic_metadata(&pin_path, &bytes)?;
        lease.generation = generation;
        Ok(())
    }

    // Written pages are append-only lease roots. Updating a fixed-size journal
    // avoids rewriting the entire growing pin set for every graph page.
    // Callers hold the store lock until the pin is durable in the filesystem.
    fn pin_written_object(&self, digest: &Fingerprint) -> Result<(), CacheError> {
        self.pin(|_| false)?;
        let lease = self.lease.lock().unwrap();
        let path = lease.as_ref().unwrap().path.with_extension("objects");
        OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .and_then(|mut file| file.write_all(digest))
            .map_err(|error| io_error(CacheOperation::WriteRecord, &path, error))
    }

    fn failure<T>(&self, result: Result<T, CacheError>, writing: bool) -> Result<T, CacheError> {
        if let Err(error) = &result {
            let mut stats = self.stats.lock().unwrap();
            if writing {
                stats.save_failures += 1;
                stats.last_save_error = Some(error.to_string());
            }
            match error {
                CacheError::Invalid(MissReason::Missing) => stats.missing += 1,
                CacheError::Invalid(MissReason::Format) => stats.format_misses += 1,
                CacheError::Invalid(MissReason::SizeLimit) => stats.size_limits += 1,
                CacheError::Invalid(MissReason::Corrupt) | CacheError::Codec(_) => {
                    stats.corrupt += 1
                }
                _ => (),
            }
        }
        result
    }
    fn atomic_write(&self, destination: &Path, bytes: &[u8]) -> Result<(), CacheError> {
        self.atomic_replace(destination, bytes, true)
    }
    fn atomic_metadata(&self, destination: &Path, bytes: &[u8]) -> Result<(), CacheError> {
        // Leases protect running processes, which cannot survive a machine crash.
        // Access times and lookup indexes are advisory and may safely be lost then.
        // Atomic replacement still protects readers and GC against worker crashes.
        self.atomic_replace(destination, bytes, false)
    }
    fn atomic_replace(
        &self,
        destination: &Path,
        bytes: &[u8],
        durable: bool,
    ) -> Result<(), CacheError> {
        let parent = destination.parent().unwrap();
        fs::create_dir_all(parent)
            .map_err(|e| io_error(CacheOperation::CreateDirectory, parent, e))?;
        let temporary = parent.join(format!(
            ".{}-{}.tmp",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let result = (|| {
            let mut file = OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(&temporary)?;
            file.write_all(bytes)?;
            if durable {
                file.sync_all()?;
            }
            fs::rename(&temporary, destination)?;
            if durable {
                File::open(parent)?.sync_all()?;
            }
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temporary);
        }
        result.map_err(|e| io_error(CacheOperation::WriteRecord, destination, e))
    }
    pub fn write_object(&self, kind: ObjectKind, payload: &[u8]) -> Result<ObjectRef, CacheError> {
        self.failure(
            (|| {
                if payload.len() as u64 > MAX_OBJECT {
                    return Err(invalid(MissReason::SizeLimit));
                }
                let started = Instant::now();
                let (codec, compressed) = compress(payload)?;
                self.stats.lock().unwrap().compression_time += started.elapsed();
                if compressed.len() as u64 > MAX_OBJECT {
                    return Err(invalid(MissReason::SizeLimit));
                }
                let mut bytes = MAGIC.to_vec();
                bytes.extend([kind as u8, codec, 0, 0]);
                bytes.extend((compressed.len() as u64).to_le_bytes());
                bytes.extend((payload.len() as u64).to_le_bytes());
                bytes.extend(fingerprint(payload));
                bytes.extend(compressed);
                let object = ObjectRef {
                    digest: fingerprint(&bytes),
                    kind,
                    stored_bytes: bytes.len() as u64,
                    decoded_bytes: payload.len() as u64,
                };
                {
                    let _lock = self.lock()?;
                    self.pin_written_object(&object.digest)?;
                }
                let path = self.object_path(&object.digest);
                let reused = read_bounded(&path, MAX_OBJECT + HEADER as u64)
                    .is_ok_and(|existing| fingerprint(&existing) == object.digest);
                if reused {
                    self.stats.lock().unwrap().shared_objects += 1;
                } else {
                    self.atomic_write(&path, &bytes)?;
                    self.pending_bytes
                        .fetch_add(bytes.len() as u64, Ordering::Relaxed);
                    let mut stats = self.stats.lock().unwrap();
                    if kind == ObjectKind::Result {
                        stats.result_write_bytes += bytes.len() as u64;
                    } else {
                        stats.environment_write_bytes += bytes.len() as u64;
                    }
                }
                Ok(object)
            })(),
            true,
        )
    }
    pub fn read_object(&self, object: &ObjectRef) -> Result<Vec<u8>, CacheError> {
        self.pin_objects(&[object])?;
        self.read_pinned_object(object)
    }

    /// Pin a result batch in one atomic lease update. Decode each object before
    /// reading the next, so batching does not retain all uncompressed buffers.
    pub(crate) fn read_values<T: DeserializeOwned>(
        &self,
        objects: &[&ObjectRef],
    ) -> Result<Vec<T>, CacheError> {
        self.pin_objects(objects)?;
        objects
            .iter()
            .map(|object| deserialize(&self.read_pinned_object(object)?))
            .collect()
    }

    pub(crate) fn pin_objects(&self, objects: &[&ObjectRef]) -> Result<(), CacheError> {
        self.failure(
            (|| {
                let _lock = self.lock()?;
                self.pin(|pins| {
                    let before = pins.read_objects.len();
                    pins.read_objects
                        .extend(objects.iter().map(|object| object.digest));
                    pins.read_objects.len() != before
                })
            })(),
            false,
        )
    }

    pub(crate) fn read_pinned_object(&self, object: &ObjectRef) -> Result<Vec<u8>, CacheError> {
        self.failure(
            (|| {
                let bytes = read_bounded(
                    &self.object_path(&object.digest),
                    MAX_OBJECT + HEADER as u64,
                )?;
                {
                    let mut stats = self.stats.lock().unwrap();
                    if object.kind == ObjectKind::Result {
                        stats.result_read_bytes += bytes.len() as u64;
                    } else {
                        stats.environment_read_bytes += bytes.len() as u64;
                    }
                }
                if bytes.len() < HEADER
                    || &bytes[..8] != MAGIC
                    || bytes[8] != object.kind as u8
                    || bytes[10..12] != [0, 0]
                {
                    return Err(invalid(MissReason::Format));
                }
                if bytes.len() as u64 != object.stored_bytes || fingerprint(&bytes) != object.digest
                {
                    return Err(invalid(MissReason::Corrupt));
                }
                let stored = u64::from_le_bytes(bytes[12..20].try_into().unwrap());
                let decoded = u64::from_le_bytes(bytes[20..28].try_into().unwrap());
                if decoded > MAX_OBJECT {
                    return Err(invalid(MissReason::SizeLimit));
                }
                if stored != (bytes.len() - HEADER) as u64 || decoded != object.decoded_bytes {
                    return Err(invalid(MissReason::Corrupt));
                }
                let started = Instant::now();
                let payload = decompress(bytes[9], &bytes[HEADER..], decoded)?;
                if payload.len() as u64 != decoded || fingerprint(&payload) != bytes[28..60] {
                    return Err(invalid(MissReason::Corrupt));
                }
                let mut stats = self.stats.lock().unwrap();
                stats.decompression_time += started.elapsed();
                if object.kind == ObjectKind::Result {
                    stats.result_hits += 1;
                } else {
                    if object.kind == ObjectKind::Checkpoint {
                        stats.checkpoint_resumes += 1;
                    } else {
                        stats.environment_imports += 1;
                    }
                }
                Ok(payload)
            })(),
            false,
        )
    }
    pub fn publish(&self, manifest: &StoreManifest) -> Result<(), CacheError> {
        self.publish_record(manifest, false)
    }
    pub fn publish_checkpoint(&self, manifest: &StoreManifest) -> Result<(), CacheError> {
        self.publish_record(manifest, true)
    }
    fn publish_record(&self, manifest: &StoreManifest, checkpoint: bool) -> Result<(), CacheError> {
        let mut canonical = manifest.clone();
        canonical.coverage.sort();
        canonical.coverage.dedup();
        canonical.dependencies.sort();
        canonical.dependencies.dedup();
        canonical
            .results
            .sort_by(|left, right| left.0.cmp(&right.0));
        let manifest = &canonical;
        let collect = self.failure(
            (|| {
                let payload = serialize(manifest)?;
                if payload.len() as u64 > MAX_MANIFEST {
                    return Err(invalid(MissReason::SizeLimit));
                }
                let mut bytes = b"REFMAN02".to_vec();
                bytes.extend(fingerprint(&payload));
                bytes.extend(payload);
                let _lock = self.lock()?;
                for object in manifest.objects() {
                    let path = self.object_path(&object.digest);
                    let metadata = fs::metadata(&path)
                        .map_err(|e| io_error(CacheOperation::ReadRecord, &path, e))?;
                    if metadata.len() != object.stored_bytes {
                        return Err(invalid(MissReason::Corrupt));
                    }
                }
                // Accounting is shared by concurrent writers under store.lock.
                // Replaced records are charged conservatively until the next sweep.
                let usage_path = self.root.join("usage");
                let previous = fs::read(&usage_path)
                    .ok()
                    .and_then(|bytes| bytes.try_into().ok())
                    .map(u64::from_le_bytes);
                let previous = match previous {
                    Some(previous) => previous,
                    None => store_bytes(&self.root)?,
                };
                let usage = previous
                    .saturating_add(bytes.len() as u64)
                    .saturating_add(self.pending_bytes.swap(0, Ordering::Relaxed));
                self.atomic_write(&usage_path, &usage.to_le_bytes())?;
                {
                    let mut stats = self.stats.lock().unwrap();
                    stats.retained_bytes = usage;
                    stats.retained_bytes_is_upper_bound = true;
                }
                if !checkpoint {
                    // The lock makes the marker and manifest visible as one publication.
                    // A crash before the manifest leaves a harmless, lazily removed marker.
                    self.atomic_metadata(
                        &self
                            .input_directory(&manifest.input)
                            .join(hex(&manifest.key)),
                        &[],
                    )?;
                }
                self.atomic_write(&self.manifest_path(&manifest.key, checkpoint), &bytes)?;
                self.pin(|pins| {
                    let mut changed = if checkpoint {
                        pins.checkpoints.insert(manifest.key)
                    } else {
                        pins.artifacts.insert(manifest.key)
                    };
                    for object in manifest.objects() {
                        changed |= pins.objects.remove(&object.digest);
                    }
                    changed
                })?;
                self.touch(&manifest.key, checkpoint)?;
                Ok(usage > self.budget.load(Ordering::Relaxed))
            })(),
            true,
        )?;
        if collect {
            self.failure(self.collect().map(|_| ()), true)
        } else {
            Ok(())
        }
    }
    fn touch(&self, key: &Fingerprint, checkpoint: bool) -> Result<(), CacheError> {
        let path = self
            .root
            .join("access")
            .join(format!("{}-{}", hex(key), u8::from(checkpoint)));
        self.atomic_metadata(&path, &[])
    }
    fn load_manifest(
        &self,
        key: &Fingerprint,
        checkpoint: bool,
    ) -> Result<StoreManifest, CacheError> {
        let bytes = read_bounded(&self.manifest_path(key, checkpoint), MAX_MANIFEST + 40)?;
        if bytes.len() < 40 || &bytes[..8] != b"REFMAN02" {
            return Err(invalid(MissReason::Format));
        }
        if fingerprint(&bytes[40..]) != bytes[8..40] {
            return Err(invalid(MissReason::Corrupt));
        }
        let manifest: StoreManifest = deserialize(&bytes[40..])?;
        if manifest.key != *key {
            return Err(invalid(MissReason::Corrupt));
        }
        Ok(manifest)
    }
    pub fn read_manifest(&self, key: &Fingerprint) -> Result<StoreManifest, CacheError> {
        self.read_record(key, false)
    }
    pub fn read_checkpoint(&self, key: &Fingerprint) -> Result<StoreManifest, CacheError> {
        self.read_record(key, true)
    }
    fn read_record(
        &self,
        key: &Fingerprint,
        checkpoint: bool,
    ) -> Result<StoreManifest, CacheError> {
        self.failure(
            (|| {
                let _lock = self.lock()?;
                let manifest = self.load_manifest(key, checkpoint)?;
                self.pin(|pins| {
                    let mut changed = if checkpoint {
                        pins.checkpoints.insert(*key)
                    } else {
                        pins.artifacts.insert(*key)
                    };
                    for object in manifest.objects() {
                        changed |= pins.read_objects.insert(object.digest);
                    }
                    changed
                })?;
                self.touch(key, checkpoint)?;
                Ok(manifest)
            })(),
            false,
        )
    }
    pub fn discard_checkpoint(&self, key: &Fingerprint) -> Result<(), CacheError> {
        let _lock = self.lock()?;
        remove(&self.manifest_path(key, true))?;
        self.pin(|pins| pins.checkpoints.remove(key))
    }
    pub fn list_matching(&self, input: &Fingerprint) -> Result<Vec<StoreManifest>, CacheError> {
        let _lock = self.lock()?;
        let mut matches = Vec::new();
        for path in files(&self.input_directory(input))? {
            let Some(key) = path_key(&path) else { continue };
            match self.load_manifest(&key, false) {
                Ok(manifest) if manifest.input == *input => matches.push(manifest),
                _ => {
                    remove(&path)?;
                }
            }
        }
        self.pin(|pins| {
            let before = pins.artifacts.len() + pins.read_objects.len();
            pins.artifacts.extend(matches.iter().map(|m| m.key));
            pins.read_objects
                .extend(matches.iter().flat_map(|m| m.objects().map(|o| o.digest)));
            before != pins.artifacts.len() + pins.read_objects.len()
        })?;
        for manifest in &matches {
            self.touch(&manifest.key, false)?;
        }
        matches.sort_by_key(|m| m.key);
        Ok(matches)
    }
    /// Remove least recently used, unleased roots and then unreachable objects.
    /// Advisory locks release on process death, including forcibly killed workers.
    pub fn collect(&self) -> Result<CacheStoreStats, CacheError> {
        let _lock = self.lock()?;
        let before = store_bytes(&self.root)?;
        let budget = self.budget.load(Ordering::Relaxed);
        let mut pinned = Pins::default();
        for path in files(&self.root.join("leases"))? {
            if path
                .extension()
                .is_some_and(|ext| ext == "pins" || ext == "objects")
            {
                if !path.with_extension("").exists() {
                    remove(&path)?;
                }
                continue;
            }
            if path.extension().is_some_and(|ext| ext == "tmp") {
                if old_temporary(&path) {
                    remove(&path)?;
                }
                continue;
            }
            let Ok(file) = OpenOptions::new().read(true).write(true).open(&path) else {
                continue;
            };
            match file.try_lock() {
                Ok(()) => {
                    remove(&path.with_extension("pins"))?;
                    remove(&path.with_extension("objects"))?;
                    remove(&path)?;
                }
                Err(std::fs::TryLockError::WouldBlock) => {
                    let bytes = read_bounded(&path.with_extension("pins"), MAX_MANIFEST + 8)?;
                    // A live but unreadable lease is conservatively retained with everything.
                    let Ok(pins) =
                        serde_json::from_slice::<Pins>(bytes.get(8..).unwrap_or_default())
                    else {
                        return Ok(self.stats());
                    };
                    pinned.artifacts.extend(pins.artifacts);
                    pinned.checkpoints.extend(pins.checkpoints);
                    pinned.objects.extend(pins.objects);
                    pinned.objects.extend(pins.read_objects);
                    let journal = path.with_extension("objects");
                    if journal.exists() {
                        let file = File::open(&journal)
                            .map_err(|e| io_error(CacheOperation::ReadRecord, &journal, e))?;
                        if file
                            .metadata()
                            .map_err(|e| io_error(CacheOperation::ReadRecord, &journal, e))?
                            .len()
                            % 32
                            != 0
                        {
                            return Ok(self.stats());
                        }
                        let mut reader = std::io::BufReader::with_capacity(64 * 1024, file);
                        loop {
                            let mut digest = [0; 32];
                            match reader.read_exact(&mut digest) {
                                Ok(()) => {
                                    pinned.objects.insert(digest);
                                }
                                Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => break,
                                Err(e) => {
                                    return Err(io_error(CacheOperation::ReadRecord, &journal, e));
                                }
                            }
                        }
                    }
                }
                Err(std::fs::TryLockError::Error(e)) => {
                    return Err(io_error(CacheOperation::Collect, &path, e));
                }
            }
        }
        let mut records = std::collections::BTreeMap::new();
        for checkpoint in [false, true] {
            for path in files(&self.root.join(if checkpoint {
                "checkpoints"
            } else {
                "artifacts"
            }))? {
                let Some(key) = path_key(&path) else {
                    if old_temporary(&path) {
                        remove(&path)?;
                    }
                    continue;
                };
                match self.load_manifest(&key, checkpoint) {
                    Ok(manifest) => {
                        records.insert((key, checkpoint), manifest);
                    }
                    Err(_) => {
                        if !(if checkpoint {
                            &pinned.checkpoints
                        } else {
                            &pinned.artifacts
                        })
                        .contains(&key)
                        {
                            remove(&path)?;
                        }
                    }
                }
            }
        }
        // Preserve the entire dependency closure of every active manifest.
        let mut protected: BTreeSet<_> = pinned
            .artifacts
            .iter()
            .map(|k| (*k, false))
            .chain(pinned.checkpoints.iter().map(|k| (*k, true)))
            .collect();
        let mut pending: Vec<_> = protected.iter().copied().collect();
        while let Some(key) = pending.pop() {
            if let Some(manifest) = records.get(&key) {
                for dependency in &manifest.dependencies {
                    if protected.insert((*dependency, false)) {
                        pending.push((*dependency, false));
                    }
                }
            }
        }
        let mut candidates: Vec<_> = records
            .keys()
            .filter(|key| !protected.contains(key))
            .copied()
            .collect();
        candidates.sort_by_cached_key(|(key, checkpoint)| {
            fs::metadata(self.root.join("access").join(format!(
                "{}-{}",
                hex(key),
                u8::from(*checkpoint)
            )))
            .and_then(|m| m.modified())
            .unwrap_or(SystemTime::UNIX_EPOCH)
        });
        // Stale leases and damaged records have already been removed above.
        let mut remaining = store_bytes(&self.root)?;
        let mut marked = pinned.objects.clone();
        marked.extend(records.values().flat_map(|m| m.objects().map(|o| o.digest)));
        // Unpublished objects are safe to remove only once their writer lease has ended.
        for path in files(&self.root.join("objects"))? {
            if path_key(&path).is_some_and(|key| !marked.contains(&key)) || old_temporary(&path) {
                remaining =
                    remaining.saturating_sub(fs::metadata(&path).map(|m| m.len()).unwrap_or(0));
                remove(&path)?;
            }
        }
        let mut collection = CollectionIndex::new(&records, &candidates);
        while remaining > budget {
            let Some(index) = collection.eligible.pop_first() else {
                break;
            };
            let (key, checkpoint) = candidates[index];
            let manifest = records.remove(&(key, checkpoint)).unwrap();
            let orphaned = collection.remove((key, checkpoint), &manifest);
            if !checkpoint {
                remove(&self.input_directory(&manifest.input).join(hex(&key)))?;
            }
            let path = self.manifest_path(&key, checkpoint);
            remaining = remaining.saturating_sub(fs::metadata(&path).map(|m| m.len()).unwrap_or(0));
            remove(&path)?;
            remove(&self.root.join("access").join(format!(
                "{}-{}",
                hex(&key),
                u8::from(checkpoint)
            )))?;
            for digest in orphaned {
                if !pinned.objects.contains(&digest) {
                    let path = self.object_path(&digest);
                    remaining =
                        remaining.saturating_sub(fs::metadata(&path).map(|m| m.len()).unwrap_or(0));
                    remove(&path)?;
                }
            }
        }
        for path in files(&self.root.join("tmp"))? {
            if old_temporary(&path) {
                remove(&path)?;
            }
        }
        // Interrupted publications and damaged manifests can leave index entries
        // that list_matching will never visit again.
        for path in files(&self.root.join("inputs"))? {
            if let Some(key) = path_key(&path) {
                let retained = records.get(&(key, false)).is_some_and(|manifest| {
                    path.parent() == Some(self.input_directory(&manifest.input).as_path())
                });
                if !retained {
                    remove(&path)?;
                }
            } else if old_temporary(&path) {
                remove(&path)?;
            }
        }
        let retained_inputs: BTreeSet<_> =
            records.values().map(|manifest| manifest.input).collect();
        for path in files(&self.root.join("instances"))? {
            let keep = read_bounded(&path, 32)
                .ok()
                .and_then(|bytes| bytes.try_into().ok())
                .is_some_and(|input: Fingerprint| retained_inputs.contains(&input));
            if !keep {
                remove(&path)?;
            }
        }
        let after = store_bytes(&self.root)?;
        self.atomic_write(&self.root.join("usage"), &after.to_le_bytes())?;
        let mut stats = self.stats.lock().unwrap();
        stats.collected_bytes += before.saturating_sub(after);
        stats.retained_bytes = after;
        stats.retained_bytes_is_upper_bound = false;
        stats.budget_excess_bytes = after.saturating_sub(budget);
        Ok(stats.clone())
    }
    /// Publish verified worker outputs through the same object-before-manifest protocol.
    pub fn publish_from(&self, source_directory: impl Into<PathBuf>) -> Result<(), CacheError> {
        let source = Self::new(source_directory);
        let mut records = Vec::new();
        {
            // Hold the source lock until the entire batch is pinned. Updating
            // an ever-growing object lease once per manifest makes publication
            // quadratic, even though each immutable object is copied once.
            let _lock = source.lock()?;
            for checkpoint in [false, true] {
                for path in files(&source.root.join(if checkpoint {
                    "checkpoints"
                } else {
                    "artifacts"
                }))? {
                    let Some(key) = path_key(&path) else { continue };
                    if let Ok(manifest) = source.load_manifest(&key, checkpoint) {
                        records.push((manifest, checkpoint));
                    }
                }
            }
            source.pin(|pins| {
                for (manifest, checkpoint) in &records {
                    if *checkpoint {
                        pins.checkpoints.insert(manifest.key);
                    } else {
                        pins.artifacts.insert(manifest.key);
                    }
                    pins.read_objects
                        .extend(manifest.objects().map(|object| object.digest));
                }
                !records.is_empty()
            })?;
        }
        // Complete dependency records must become visible before their consumers.
        // Pin dependencies already in the destination while the source is copied.
        let mut pending: std::collections::BTreeMap<_, _> = records
            .into_iter()
            .map(|(manifest, checkpoint)| ((manifest.key, checkpoint), manifest))
            .collect();
        let mut records = Vec::new();
        let mut published = BTreeSet::new();
        while !pending.is_empty() {
            let next = pending.iter().find_map(|(key, manifest)| {
                manifest
                    .dependencies
                    .iter()
                    .all(|dependency| !pending.contains_key(&(*dependency, false)))
                    .then_some(*key)
            });
            let Some(key) = next else {
                return self.failure(Err(invalid(MissReason::Corrupt)), true);
            };
            let manifest = pending.remove(&key).unwrap();
            for dependency in &manifest.dependencies {
                if !published.contains(dependency) {
                    self.read_manifest(dependency)?;
                }
            }
            if !key.1 {
                published.insert(key.0);
            }
            records.push((manifest, key.1));
        }
        // Pin all copied objects before any publication can trigger collection.
        let objects: BTreeMap<_, _> = records
            .iter()
            .flat_map(|(manifest, _)| manifest.objects())
            .map(|object| (object.digest, object))
            .collect();
        source.pin_objects(&objects.values().copied().collect::<Vec<_>>())?;
        let mut linked_directories = BTreeSet::new();
        for object in objects.into_values() {
            let source_path = source.object_path(&object.digest);
            let bytes = read_bounded(&source_path, MAX_OBJECT + HEADER as u64)?;
            if bytes.len() as u64 != object.stored_bytes || fingerprint(&bytes) != object.digest {
                return Err(invalid(MissReason::Corrupt));
            }
            {
                let _lock = self.lock()?;
                self.pin_written_object(&object.digest)?;
            }
            let path = self.object_path(&object.digest);
            if read_bounded(&path, MAX_OBJECT + HEADER as u64)
                .is_ok_and(|existing| fingerprint(&existing) == object.digest)
            {
                self.stats.lock().unwrap().shared_objects += 1;
            } else {
                let parent = path.parent().unwrap();
                fs::create_dir_all(parent)
                    .map_err(|error| io_error(CacheOperation::CreateDirectory, parent, error))?;
                // Both stores own immutable objects. On the same filesystem a
                // link shares their durable data, and syncing each directory
                // once makes every link durable before publishing manifests.
                let linked = fs::hard_link(&source_path, &path).is_ok();
                if linked {
                    linked_directories.insert(parent.to_path_buf());
                } else {
                    self.atomic_write(&path, &bytes)?;
                }
                self.pending_bytes
                    .fetch_add(bytes.len() as u64, Ordering::Relaxed);
                let mut stats = self.stats.lock().unwrap();
                if linked {
                    stats.shared_objects += 1;
                } else if object.kind == ObjectKind::Result {
                    stats.result_write_bytes += bytes.len() as u64;
                } else {
                    stats.environment_write_bytes += bytes.len() as u64;
                }
            }
            let mut stats = self.stats.lock().unwrap();
            if object.kind == ObjectKind::Result {
                stats.result_read_bytes += bytes.len() as u64;
            } else {
                stats.environment_read_bytes += bytes.len() as u64;
            }
        }
        for directory in linked_directories {
            File::open(&directory)
                .and_then(|file| file.sync_all())
                .map_err(|error| io_error(CacheOperation::WriteRecord, &directory, error))?;
        }
        for (manifest, checkpoint) in records {
            self.publish_record(&manifest, checkpoint)?;
        }
        Ok(())
    }
}

fn read_bounded(path: &Path, limit: u64) -> Result<Vec<u8>, CacheError> {
    let file = File::open(path).map_err(|e| {
        if e.kind() == std::io::ErrorKind::NotFound {
            invalid(MissReason::Missing)
        } else {
            io_error(CacheOperation::ReadRecord, path, e)
        }
    })?;
    if file
        .metadata()
        .map_err(|e| io_error(CacheOperation::ReadRecord, path, e))?
        .len()
        > limit
    {
        return Err(invalid(MissReason::SizeLimit));
    }
    let mut bytes = Vec::new();
    file.take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| io_error(CacheOperation::ReadRecord, path, e))?;
    if bytes.len() as u64 > limit {
        return Err(invalid(MissReason::SizeLimit));
    }
    Ok(bytes)
}
fn remove(path: &Path) -> Result<(), CacheError> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(io_error(CacheOperation::Collect, path, e)),
    }
}
fn files(root: &Path) -> Result<Vec<PathBuf>, CacheError> {
    let mut paths = Vec::new();
    let mut directories = vec![root.to_owned()];
    while let Some(directory) = directories.pop() {
        let entries = match fs::read_dir(&directory) {
            Ok(entries) => entries,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => return Err(io_error(CacheOperation::Collect, &directory, e)),
        };
        for entry in entries {
            let entry = entry.map_err(|e| io_error(CacheOperation::Collect, &directory, e))?;
            let ty = entry
                .file_type()
                .map_err(|e| io_error(CacheOperation::Collect, &entry.path(), e))?;
            if ty.is_dir() {
                directories.push(entry.path());
            } else if ty.is_file() {
                paths.push(entry.path());
            }
        }
    }
    Ok(paths)
}
fn store_bytes(root: &Path) -> Result<u64, CacheError> {
    let mut paths = vec![root.join("store.lock"), root.join("usage")];
    // The cache root also hosts supervisor workspaces and batch layouts.
    for directory in [
        "artifacts",
        "objects",
        "checkpoints",
        "leases",
        "access",
        "tmp",
        "inputs",
        "instances",
    ] {
        paths.extend(files(&root.join(directory))?);
    }
    Ok(paths
        .iter()
        .filter_map(|p| fs::metadata(p).ok())
        .map(|m| m.len())
        .sum())
}
fn path_key(path: &Path) -> Option<Fingerprint> {
    let name = path.file_name()?.to_str()?.split('.').next()?;
    if name.len() != 64 || !name.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return None;
    }
    let mut key = [0; 32];
    for (index, byte) in key.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&name[index * 2..index * 2 + 2], 16).ok()?;
    }
    Some(key)
}
fn old_temporary(path: &Path) -> bool {
    path.extension().is_some_and(|e| e == "tmp")
        && fs::metadata(path)
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| t.elapsed().ok())
            .is_some_and(|elapsed| elapsed > Duration::from_secs(3600))
}
#[cfg(not(target_arch = "wasm32"))]
fn compress(bytes: &[u8]) -> Result<(u8, Vec<u8>), CacheError> {
    zstd::stream::encode_all(bytes, 3)
        .map(|bytes| (1, bytes))
        .map_err(|e| CacheError::Codec(e.to_string()))
}
#[cfg(target_arch = "wasm32")]
fn compress(bytes: &[u8]) -> Result<(u8, Vec<u8>), CacheError> {
    Ok((2, miniz_oxide::deflate::compress_to_vec_zlib(bytes, 6)))
}
fn decompress(codec: u8, bytes: &[u8], limit: u64) -> Result<Vec<u8>, CacheError> {
    #[cfg(not(target_arch = "wasm32"))]
    if codec == 1 {
        let decoder = zstd::stream::read::Decoder::new(bytes)
            .map_err(|e| CacheError::Codec(e.to_string()))?;
        let mut result = Vec::new();
        decoder
            .take(limit + 1)
            .read_to_end(&mut result)
            .map_err(|e| CacheError::Codec(e.to_string()))?;
        if result.len() as u64 > limit {
            return Err(invalid(MissReason::SizeLimit));
        }
        return Ok(result);
    }
    #[cfg(target_arch = "wasm32")]
    if codec == 2 {
        return miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(bytes, limit as usize)
            .map_err(|e| CacheError::Codec(format!("{e:?}")));
    }
    Err(invalid(MissReason::Format))
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "ref-artifact-store-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }
        fn store(&self) -> ArtifactStore {
            ArtifactStore::new(&self.0)
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    fn manifest(store: &ArtifactStore, value: u8) -> StoreManifest {
        StoreManifest {
            key: fingerprint(&[value]),
            input: fingerprint(b"inputs"),
            coverage: vec![vec!["Test".into()]],
            results: vec![(
                vec!["Test".into()],
                store
                    .write_object(ObjectKind::Result, b"shared result")
                    .unwrap(),
            )],
            environment: Some(
                store
                    .write_object(ObjectKind::Environment, &[value; 1024])
                    .unwrap(),
            ),
            ..StoreManifest::default()
        }
    }
    #[test]
    fn collection_index_matches_oldest_eligible_scan_and_shared_object_lifetimes() {
        fn key(n: u32) -> Fingerprint {
            fingerprint(&n.to_le_bytes())
        }
        let mut records = BTreeMap::new();
        for n in 0..64u32 {
            let object = ObjectRef {
                digest: key(100 + n % 7),
                kind: ObjectKind::Result,
                stored_bytes: 1,
                decoded_bytes: 1,
            };
            let mut manifest = StoreManifest {
                key: key(n),
                dependencies: if n == 0 { vec![] } else { vec![key(n - 1)] },
                results: vec![(vec![], object.clone())],
                ..StoreManifest::default()
            };
            if n % 5 == 0 {
                manifest.results.push((vec!["alias".into()], object));
            }
            records.insert((manifest.key, false), manifest.clone());
            if n % 9 == 0 {
                manifest.dependencies.push(key(n));
                records.insert((manifest.key, true), manifest);
            }
        }
        // Cycles and self references remain ineligible, just as in the full scan.
        for (n, dependency) in [(70, 71), (71, 70), (72, 72)] {
            records.insert(
                (key(n), false),
                StoreManifest {
                    key: key(n),
                    dependencies: vec![key(dependency)],
                    ..StoreManifest::default()
                },
            );
        }
        // A retained root and its dependency remain outside the candidate set.
        let protected = BTreeSet::from([(key(0), false), (key(1), false)]);
        let mut candidates: Vec<_> = records
            .keys()
            .filter(|key| !protected.contains(key))
            .copied()
            .collect();
        candidates.rotate_left(11);
        let mut index = CollectionIndex::new(&records, &candidates);
        loop {
            let expected = candidates.iter().position(|candidate| {
                records.contains_key(candidate)
                    && (candidate.1
                        || !records
                            .values()
                            .any(|m| m.dependencies.contains(&candidate.0)))
            });
            assert_eq!(index.eligible.pop_first(), expected);
            let Some(rank) = expected else { break };
            let record_key = candidates[rank];
            let manifest = records.remove(&record_key).unwrap();
            let expected_objects: BTreeSet<_> = manifest
                .objects()
                .map(|object| object.digest)
                .filter(|digest| {
                    !records
                        .values()
                        .any(|m| m.objects().any(|o| o.digest == *digest))
                })
                .collect();
            assert_eq!(index.remove(record_key, &manifest), expected_objects);
        }
        assert_eq!(records.len(), protected.len() + 3);
        assert!(protected.iter().all(|key| records.contains_key(key)));
    }

    #[test]
    fn warm_store_reports_persisted_usage_without_a_write() {
        let directory = Directory::new();
        let writer = directory.store();
        writer.publish(&manifest(&writer, 1)).unwrap();
        drop(writer);
        let reader = directory.store();
        let usage = u64::from_le_bytes(
            fs::read(reader.root.join("usage"))
                .unwrap()
                .try_into()
                .unwrap(),
        );
        assert!(usage > 0);
        assert_eq!(reader.stats().retained_bytes, usage);
        reader.set_budget(usage - 1);
        assert_eq!(reader.stats().budget_excess_bytes, 1);
        assert_eq!(reader.stats().result_write_bytes, 0);
        assert!(reader.lease.lock().unwrap().is_none());
    }

    #[test]
    fn collection_budget_excludes_supervisor_workspaces_and_layouts() {
        let directory = Directory::new();
        let workspace = directory.0.join(".check-123-0");
        fs::create_dir(&workspace).unwrap();
        let snapshot = workspace.join("snapshot.json");
        let layout = directory.0.join("batches.json");
        fs::write(&snapshot, vec![0; 16 * 1024]).unwrap();
        fs::write(&layout, vec![0; 16 * 1024]).unwrap();

        let store = directory.store();
        store.set_budget(8 * 1024);
        let record = manifest(&store, 1);
        store.publish(&record).unwrap();
        assert!(store.stats().retained_bytes < 8 * 1024);
        store.release_pins().unwrap();
        let stats = store.collect().unwrap();
        assert_eq!(stats.budget_excess_bytes, 0);
        assert_eq!(store.read_manifest(&record.key).unwrap(), record);
        assert_eq!(fs::metadata(snapshot).unwrap().len(), 16 * 1024);
        assert_eq!(fs::metadata(layout).unwrap().len(), 16 * 1024);
    }

    #[test]
    fn observed_inputs_count_each_persisted_change_once() {
        let directory = Directory::new();
        let first = directory.store();
        let second = directory.store();
        let instance = fingerprint(b"package instance");
        let before = fingerprint(b"before");
        let after = fingerprint(b"after");
        first.observe_input(&instance, &before).unwrap();
        first.observe_input(&instance, &before).unwrap();
        second.observe_input(&instance, &before).unwrap();
        assert_eq!(first.stats().input_mismatches, 0);
        assert_eq!(second.stats().input_mismatches, 0);
        second.observe_input(&instance, &after).unwrap();
        second.observe_input(&instance, &after).unwrap();
        first.observe_input(&instance, &after).unwrap();
        assert_eq!(first.stats().input_mismatches, 0);
        assert_eq!(second.stats().input_mismatches, 1);
        assert_eq!(
            fs::read(first.root.join("instances").join(hex(&instance))).unwrap(),
            after
        );
    }

    #[test]
    fn malformed_observed_inputs_are_repaired_without_counting_a_change() {
        let directory = Directory::new();
        let store = directory.store();
        let instance = fingerprint(b"package instance");
        let input = fingerprint(b"current input");
        store.observe_input(&instance, &input).unwrap();
        let path = store.root.join("instances").join(hex(&instance));
        for length in [0, 7, 33] {
            fs::write(&path, vec![0; length]).unwrap();
            store.observe_input(&instance, &input).unwrap();
            assert_eq!(fs::read(&path).unwrap(), input);
        }
        assert_eq!(store.stats().input_mismatches, 0);
        assert_eq!(store.stats().save_failures, 0);
    }

    #[test]
    fn collection_removes_stale_indexes_without_overevicting_after_damage() {
        let directory = Directory::new();
        let store = directory.store();
        let record = manifest(&store, 1);
        store.publish(&record).unwrap();
        store.release_pins().unwrap();
        let retained_size = store_bytes(&store.root).unwrap();
        store.set_budget(retained_size + 512);

        let damaged = fingerprint(b"damaged manifest");
        let damaged_path = store.manifest_path(&damaged, false);
        fs::create_dir_all(damaged_path.parent().unwrap()).unwrap();
        fs::write(&damaged_path, vec![0; 1024 * 1024]).unwrap();
        let missing = fingerprint(b"missing manifest");
        let other_input = fingerprint(b"incorrect index input");
        let stale = [
            store.input_directory(&record.input).join(hex(&damaged)),
            store.input_directory(&record.input).join(hex(&missing)),
            store.input_directory(&other_input).join(hex(&record.key)),
        ];
        for path in &stale {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, []).unwrap();
        }

        let stats = store.collect().unwrap();
        assert!(store.manifest_path(&record.key, false).exists());
        assert!(!damaged_path.exists());
        assert!(stale.iter().all(|path| !path.exists()));
        assert_eq!(stats.budget_excess_bytes, 0);
        assert!(stats.collected_bytes >= 1024 * 1024);
        assert_eq!(store.list_matching(&record.input).unwrap(), vec![record]);
    }

    #[test]
    fn batched_reads_pin_every_object_before_collection() {
        let directory = Directory::new();
        let writer = directory.store();
        let first = writer
            .write_object(ObjectKind::Result, &serialize(&vec![1u32, 2]).unwrap())
            .unwrap();
        let second = writer
            .write_object(ObjectKind::Result, &serialize(&vec![3u32]).unwrap())
            .unwrap();
        let reader = directory.store();
        let values: Vec<Vec<u32>> = reader.read_values(&[&first, &second]).unwrap();
        assert_eq!(values, [vec![1, 2], vec![3]]);
        drop(writer);
        reader.set_budget(0);
        reader.collect().unwrap();
        assert!(reader.object_path(&first.digest).exists());
        assert!(reader.object_path(&second.digest).exists());
        assert_eq!(reader.stats().result_hits, 2);
        reader.release_pins().unwrap();
        reader.collect().unwrap();
        assert!(!reader.object_path(&first.digest).exists());
        assert!(!reader.object_path(&second.digest).exists());
    }

    #[test]
    fn results_do_not_read_or_decode_environments() {
        let directory = Directory::new();
        let writer = directory.store();
        let expected = manifest(&writer, 1);
        writer.publish(&expected).unwrap();
        drop(writer);
        let reader = directory.store();
        let restored = reader.read_manifest(&expected.key).unwrap();
        fs::write(
            reader.object_path(&restored.environment.unwrap().digest),
            b"broken",
        )
        .unwrap();
        assert_eq!(
            reader.read_object(&restored.results[0].1).unwrap(),
            b"shared result"
        );
        assert_eq!(reader.stats().environment_read_bytes, 0);
        assert_eq!(reader.stats().environment_imports, 0);
        assert!(reader.stats().result_read_bytes > 0);
    }
    #[test]
    fn damaged_objects_and_oversized_expansion_are_recoverable() {
        let directory = Directory::new();
        let store = directory.store();
        let object = store
            .write_object(ObjectKind::Resolver, b"payload")
            .unwrap();
        let path = store.object_path(&object.digest);
        let mut bytes = fs::read(&path).unwrap();
        bytes[HEADER] ^= 1;
        fs::write(&path, &bytes).unwrap();
        assert!(matches!(
            store.read_object(&object),
            Err(CacheError::Invalid(MissReason::Corrupt))
        ));
        // Rewriting identical data repairs an existing corrupt content-addressed entry.
        assert_eq!(
            store
                .write_object(ObjectKind::Resolver, b"payload")
                .unwrap(),
            object
        );
        assert_eq!(store.read_object(&object).unwrap(), b"payload");
        let mut bytes = fs::read(path).unwrap();
        bytes[20..28].copy_from_slice(&(MAX_OBJECT + 1).to_le_bytes());
        let oversized = ObjectRef {
            digest: fingerprint(&bytes),
            ..object
        };
        fs::create_dir_all(store.object_path(&oversized.digest).parent().unwrap()).unwrap();
        fs::write(store.object_path(&oversized.digest), bytes).unwrap();
        assert!(matches!(
            store.read_object(&oversized),
            Err(CacheError::Invalid(MissReason::SizeLimit))
        ));
    }
    #[test]
    fn leases_protect_dependency_closure_and_shared_objects_until_session_ends() {
        let directory = Directory::new();
        let writer = directory.store();
        let dependency = manifest(&writer, 1);
        writer.publish(&dependency).unwrap();
        let mut consumer = manifest(&writer, 2);
        consumer.dependencies.push(dependency.key);
        writer.publish(&consumer).unwrap();
        let unused = manifest(&writer, 3);
        writer.publish(&unused).unwrap();
        drop(writer);
        let reader = directory.store();
        reader.read_manifest(&consumer.key).unwrap();
        let collector = directory.store();
        collector.set_budget(0);
        let stats = collector.collect().unwrap();
        assert!(stats.budget_excess_bytes > 0);
        assert!(collector.manifest_path(&dependency.key, false).exists());
        assert!(collector.manifest_path(&consumer.key, false).exists());
        assert!(!collector.manifest_path(&unused.key, false).exists());
        assert_eq!(
            reader.read_object(&consumer.results[0].1).unwrap(),
            b"shared result"
        );
        drop(reader);
        collector.collect().unwrap();
        assert!(
            !collector
                .object_path(&consumer.results[0].1.digest)
                .exists()
        );
        assert!(!collector.manifest_path(&consumer.key, false).exists());
    }
    #[test]
    fn concurrent_writers_readers_and_collection_publish_complete_records() {
        let directory = Directory::new();
        std::thread::scope(|scope| {
            let mut workers = Vec::new();
            for _ in 0..4 {
                workers.push(scope.spawn(|| {
                    let store = directory.store();
                    for _ in 0..8 {
                        let record = manifest(&store, 7);
                        store.publish(&record).unwrap();
                        let loaded = store.read_manifest(&record.key).unwrap();
                        assert_eq!(
                            store.read_object(&loaded.results[0].1).unwrap(),
                            b"shared result"
                        );
                        assert_eq!(
                            store
                                .read_object(loaded.environment.as_ref().unwrap())
                                .unwrap(),
                            [7; 1024]
                        );
                        store.collect().unwrap();
                    }
                }));
            }
            for worker in workers {
                worker.join().unwrap();
            }
        });
    }
    #[test]
    fn unpublished_objects_and_dead_leases_are_collected() {
        let directory = Directory::new();
        let store = directory.store();
        let object = store
            .write_object(ObjectKind::Environment, b"unfinished")
            .unwrap();
        let collector = directory.store();
        collector.set_budget(0);
        collector.collect().unwrap();
        assert!(store.object_path(&object.digest).exists());
        drop(store);
        collector.collect().unwrap();
        assert!(!collector.object_path(&object.digest).exists());
        let stale = collector.root.join("leases/stale");
        fs::write(&stale, b"truncated lease from dead writer").unwrap();
        collector.collect().unwrap();
        assert!(!stale.exists());
    }
    #[test]
    fn killed_worker_helper() {
        let Some(directory) = std::env::var_os("REF_STORE_TEST_CHILD") else {
            return;
        };
        let store = ArtifactStore::new(PathBuf::from(directory));
        let record = manifest(&store, 9);
        store.publish(&record).unwrap();
        fs::write(store.root.join("ready"), []).unwrap();
        loop {
            std::thread::park_timeout(Duration::from_secs(60));
        }
    }

    #[test]
    fn ending_under_budget_session_does_not_wait_for_collection_lock() {
        let directory = Directory::new();
        let store = directory.store();
        store.session_token().unwrap();
        fs::write(store.root.join("usage"), 0_u64.to_le_bytes()).unwrap();
        let lock = store.lock().unwrap();
        let (finished, completion) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            drop(store);
            finished.send(()).unwrap();
        });
        let completed_without_lock = completion.recv_timeout(Duration::from_secs(2)).is_ok();
        drop(lock);
        worker.join().unwrap();
        assert!(completed_without_lock);
    }

    #[test]
    fn borrowed_session_leaves_final_collection_to_its_owner() {
        let directory = Directory::new();
        let supervisor = directory.store();
        supervisor.set_budget(0);
        supervisor.session_token().unwrap();
        let path = supervisor
            .lease
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .path
            .clone();
        let worker = directory.store();
        worker.set_budget(0);
        *worker.lease.lock().unwrap() = Some(Lease {
            _file: OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
                .unwrap(),
            path,
            pins: Pins::default(),
            owner: false,
            generation: 0,
        });
        let writer = directory.store();
        let record = manifest(&writer, 17);
        writer.publish(&record).unwrap();
        writer.release_pins().unwrap();
        let manifest_path = writer.manifest_path(&record.key, false);
        drop(worker);
        assert!(manifest_path.exists());
        drop(supervisor);
        assert!(!manifest_path.exists());
    }

    #[test]
    fn killed_worker_keeps_supervisor_session_readable() {
        let directory = Directory::new();
        let supervisor = directory.store();
        let token = supervisor.session_token().unwrap();
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "artifact_store::tests::killed_worker_helper"])
            .env("REF_STORE_TEST_CHILD", &directory.0)
            .env("REF_TYPE_CACHE_SESSION", token)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let started = Instant::now();
        while !supervisor.root.join("ready").exists() && started.elapsed() < Duration::from_secs(10)
        {
            if child.try_wait().unwrap().is_some() {
                panic!("worker exited before publishing");
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        child.kill().unwrap();
        child.wait().unwrap();
        assert!(supervisor.root.join("ready").exists());
        let collector = directory.store();
        collector.set_budget(0);
        collector.collect().unwrap();
        let key = fingerprint(&[9]);
        assert!(collector.manifest_path(&key, false).exists());
        let record = supervisor.read_manifest(&key).unwrap();
        assert_eq!(
            supervisor.read_object(&record.results[0].1).unwrap(),
            b"shared result"
        );
        drop(supervisor);
        collector.collect().unwrap();
        assert!(!collector.manifest_path(&key, false).exists());
    }

    #[test]
    fn worker_publication_keeps_manifests_and_objects_together() {
        let source = Directory::new();
        let target = Directory::new();
        let writer = source.store();
        let record = manifest(&writer, 5);
        writer.publish(&record).unwrap();
        let destination = target.store();
        destination.publish_from(&source.0).unwrap();
        let restored = destination.read_manifest(&record.key).unwrap();
        assert_eq!(
            destination
                .read_object(restored.environment.as_ref().unwrap())
                .unwrap(),
            [5; 1024]
        );
        assert_eq!(
            destination.list_matching(&record.input).unwrap(),
            vec![record]
        );
    }

    #[test]
    fn worker_publication_protects_dependency_closure_with_zero_budget() {
        let source = Directory::new();
        let target = Directory::new();
        let writer = source.store();
        let dependency = manifest(&writer, 1);
        writer.publish(&dependency).unwrap();
        let mut consumer = manifest(&writer, 2);
        consumer.dependencies.push(dependency.key);
        writer.publish(&consumer).unwrap();

        let destination = target.store();
        destination.set_budget(0);
        destination.publish_from(&source.0).unwrap();
        let collector = target.store();
        collector.set_budget(0);
        collector.collect().unwrap();
        for record in [&dependency, &consumer] {
            assert_eq!(destination.read_manifest(&record.key).unwrap(), *record);
            assert_eq!(
                destination.read_object(&record.results[0].1).unwrap(),
                b"shared result"
            );
        }
    }
}
