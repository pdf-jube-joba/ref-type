//! Cooperative collection requests, checked without allocating in signal handlers.
use std::sync::atomic::{AtomicBool, Ordering};
static PRESSURE: AtomicBool = AtomicBool::new(false);
pub fn request_collection() {
    PRESSURE.store(true, Ordering::Relaxed);
}
pub fn collection_requested() -> bool {
    PRESSURE.load(Ordering::Relaxed)
}
pub fn take_collection_request() -> bool {
    PRESSURE.swap(false, Ordering::Relaxed)
}

static ALLOCATOR_COLLECTION: std::sync::OnceLock<fn()> = std::sync::OnceLock::new();
/// The executable can release allocator-owned free pages after cache eviction.
pub fn set_allocator_collection(collect: fn()) {
    let _ = ALLOCATOR_COLLECTION.set(collect);
}
pub fn collect_allocator() {
    if let Some(collect) = ALLOCATOR_COLLECTION.get() {
        collect();
    }
}
