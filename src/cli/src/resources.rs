//! Bound allocations before reading a project so a failed check leaves the host usable.
#[cfg(target_os = "linux")]
pub fn limit_memory(requested: Option<u64>) -> std::io::Result<()> {
    let mib = requested.unwrap_or(3072);
    if mib == 0 {
        return Ok(());
    }
    let bytes = mib.checked_mul(1024 * 1024).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "memory limit is too large",
        )
    })?;
    let mut limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: getrlimit/setrlimit receive a valid pointer to a live rlimit.
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut limit) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    limit.rlim_cur = limit.rlim_cur.min(bytes);
    if unsafe { libc::setrlimit(libc::RLIMIT_AS, &limit) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(not(target_os = "linux"))]
pub fn limit_memory(requested: Option<u64>) -> std::io::Result<()> {
    if requested.is_some_and(|mib| mib != 0) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "--memory-mib is supported on Linux",
        ));
    }
    Ok(())
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
