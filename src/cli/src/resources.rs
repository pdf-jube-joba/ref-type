//! Cooperatively reclaim caches and page live heap objects to disk.
pub fn initialize(directory: &std::path::Path, requested: Option<u64>) -> std::io::Result<()> {
    #[cfg(all(
        target_os = "linux",
        not(any(
            feature = "system-allocator",
            feature = "large-allocation-profile",
            feature = "small-allocation-profile"
        ))
    ))]
    {
        let directory = std::env::var_os("REF_TYPE_GRAPH_SPILL_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| directory.to_owned());
        crate::spill_allocator::initialize(&directory, requested)?;
    }
    #[cfg(any(
        not(target_os = "linux"),
        feature = "system-allocator",
        feature = "large-allocation-profile",
        feature = "small-allocation-profile"
    ))]
    let _ = directory;

    #[cfg(not(target_os = "linux"))]
    if requested.is_some_and(|mib| mib != 0) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "--memory-mib is supported on Linux",
        ));
    }
    let _ = requested;
    Ok(())
}

pub fn heap_pageout_requested_bytes() -> u64 {
    #[cfg(all(
        target_os = "linux",
        not(any(
            feature = "system-allocator",
            feature = "large-allocation-profile",
            feature = "small-allocation-profile"
        ))
    ))]
    return crate::spill_allocator::pageout_bytes();
    #[cfg(any(
        not(target_os = "linux"),
        feature = "system-allocator",
        feature = "large-allocation-profile",
        feature = "small-allocation-profile"
    ))]
    0
}

/// Called at a declaration boundary after releasing reconstructed caches.
pub fn collect_allocator() {
    #[cfg(not(feature = "system-allocator"))]
    {
        unsafe extern "C" {
            fn mi_collect(force: bool);
        }
        // SAFETY: mimalloc's process allocator is linked by MiMalloc. Collection
        // only releases unused pages and does not invalidate live allocations.
        unsafe {
            mi_collect(true);
        }
    }
}
