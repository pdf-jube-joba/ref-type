//! File-backed mimalloc arenas let Linux reclaim every long-lived Rust heap
//! object, including frontend tables and graph indices, without moving pointers.
use std::{
    alloc::{GlobalAlloc, Layout},
    ffi::c_void,
    fs::File,
    io,
    os::fd::{AsRawFd, IntoRawFd, RawFd},
    path::Path,
    sync::{
        Mutex,
        atomic::{AtomicPtr, AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};

unsafe extern "C" {
    fn mi_arena_min_alignment() -> usize;
    fn mi_manage_os_memory_ex(
        start: *mut c_void,
        size: usize,
        committed: bool,
        pinned: bool,
        zero: bool,
        numa: libc::c_int,
        exclusive: bool,
        arena: *mut *mut c_void,
    ) -> bool;
    fn mi_heap_new_in_arena(arena: *mut c_void) -> *mut c_void;
    fn mi_heap_malloc_aligned(heap: *mut c_void, size: usize, alignment: usize) -> *mut c_void;
    fn mi_heap_zalloc_aligned(heap: *mut c_void, size: usize, alignment: usize) -> *mut c_void;
    fn ref_type_spill_configure(max_object_bytes: usize);
}

const MIB: usize = 1024 * 1024;
const ARENA_SIZE: usize = 64 * MIB;
const MAX_ARENA_SIZE: usize = if usize::BITS >= 64 {
    (16_u64 * 1024 * 1024 * 1024) as usize
} else {
    512 * MIB
};
const PAGEOUT_SIZE: usize = 32 * MIB;

#[derive(Clone, Copy)]
struct Mapping {
    start: usize,
    len: usize,
    heap: usize,
}

struct Backing {
    directory: RawFd,
    // Keep allocator bookkeeping outside the allocator it manages. Growing a
    // Vec here would recursively enter GlobalAlloc while holding this mutex.
    mappings: [Mapping; 160],
    count: usize,
    cursor: usize,
    offset: usize,
}

static BACKING: Mutex<Backing> = Mutex::new(Backing {
    directory: -1,
    mappings: [Mapping {
        start: 0,
        len: 0,
        heap: 0,
    }; 160],
    count: 0,
    cursor: 0,
    offset: 0,
});
static HEAP: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
static PAGEOUT_BYTES: AtomicU64 = AtomicU64::new(0);

impl Backing {
    fn grow(&mut self, requested: usize) -> io::Result<()> {
        if self.count == self.mappings.len() {
            return Err(io::Error::from_raw_os_error(libc::ENOSPC));
        }
        let size = requested
            .checked_add(32 * MIB)
            .and_then(usize::checked_next_power_of_two)
            .ok_or_else(|| io::Error::from_raw_os_error(libc::ENOMEM))?
            .max(
                ARENA_SIZE
                    .saturating_mul(1 << (self.count / 8).min(8))
                    .min(MAX_ARENA_SIZE),
            );
        if size > MAX_ARENA_SIZE {
            return Err(io::Error::from_raw_os_error(libc::ENOMEM));
        }
        // SAFETY: mimalloc returns its required power-of-two arena alignment.
        let alignment = unsafe { mi_arena_min_alignment() };
        let length = size + alignment;
        // O_TMPFILE leaves no directory entry, including after SIGKILL. A live
        // mapping keeps the backing inode alive after its descriptor is closed.
        // SAFETY: directory is an owned directory fd and the name is terminated.
        let mut fd = unsafe {
            libc::openat(
                self.directory,
                c".".as_ptr(),
                libc::O_TMPFILE | libc::O_RDWR | libc::O_CLOEXEC,
                0o600,
            )
        };
        if fd < 0 {
            let error = io::Error::last_os_error();
            if !matches!(
                error.raw_os_error(),
                Some(libc::EOPNOTSUPP | libc::EINVAL | libc::EISDIR)
            ) {
                return Err(error);
            }
            // Some disk filesystems support shared mappings but not O_TMPFILE.
            // Format without Rust allocation, then unlink the exclusive file.
            let mut name = [0 as libc::c_char; 80];
            unsafe {
                libc::snprintf(
                    name.as_mut_ptr(),
                    name.len(),
                    c".ref-type-heap-%d-%zu".as_ptr(),
                    libc::getpid(),
                    self.count,
                );
                fd = libc::openat(
                    self.directory,
                    name.as_ptr(),
                    libc::O_CREAT | libc::O_EXCL | libc::O_RDWR | libc::O_CLOEXEC,
                    0o600,
                );
                if fd < 0 {
                    return Err(io::Error::last_os_error());
                }
                if libc::unlinkat(self.directory, name.as_ptr(), 0) != 0 {
                    let error = io::Error::last_os_error();
                    libc::close(fd);
                    return Err(error);
                }
            }
        }
        // Reserve disk blocks before exposing the mapping: otherwise ENOSPC
        // could become SIGBUS on a later page fault into a sparse file.
        // SAFETY: fd is writable and the length fits off_t on supported Linux.
        let error = unsafe { libc::posix_fallocate(fd, 0, length as libc::off_t) };
        if error != 0 {
            unsafe { libc::close(fd) };
            return Err(io::Error::from_raw_os_error(error));
        }
        // SAFETY: mmap creates a fresh shared writable mapping of the file.
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                length,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd,
                0,
            )
        };
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        if base == libc::MAP_FAILED {
            return Err(error);
        }
        let start = (base as usize).next_multiple_of(alignment);
        // Mark the arena as pinned only to prevent mimalloc decommit/reset.
        // This does not mlock pages: Linux can still write them back and evict
        // them. MAP_SHARED preserves their contents on subsequent page faults.
        // SAFETY: the aligned range is writable, zeroed, and remains mapped for
        // the process lifetime. mimalloc exclusively manages its allocations.
        let mut arena = std::ptr::null_mut();
        let managed = unsafe {
            mi_manage_os_memory_ex(
                start as *mut c_void,
                size,
                true,
                true,
                true,
                -1,
                true,
                &mut arena,
            )
        };
        if !managed {
            unsafe { libc::munmap(base, length) };
            return Err(io::Error::from_raw_os_error(libc::ENOMEM));
        }
        // SAFETY: only unmap alignment padding outside the registered arena.
        unsafe {
            if start > base as usize {
                libc::munmap(base, start - base as usize);
            }
            let suffix = base as usize + length - start - size;
            if suffix > 0 {
                libc::munmap((start + size) as *mut c_void, suffix);
            }
        }
        // Mimalloc v3 heaps obtain a separate thread-local allocation context
        // for each calling thread. An exclusive arena keeps these allocations
        // out of the anonymous arena used during process startup.
        let heap = unsafe { mi_heap_new_in_arena(arena) };
        if heap.is_null() {
            // The registered arena must remain mapped even on heap failure.
            return Err(io::Error::from_raw_os_error(libc::ENOMEM));
        }
        self.mappings[self.count] = Mapping {
            start,
            len: size,
            heap: heap as usize,
        };
        self.count += 1;
        HEAP.store(heap, Ordering::Release);
        Ok(())
    }

    fn next_range(&mut self) -> Option<Mapping> {
        if self.count == 0 {
            return None;
        }
        let mapping = self.mappings[self.cursor];
        let range = Mapping {
            start: mapping.start + self.offset,
            len: PAGEOUT_SIZE.min(mapping.len - self.offset),
            heap: mapping.heap,
        };
        self.offset += range.len;
        if self.offset == mapping.len {
            self.offset = 0;
            self.cursor = (self.cursor + 1) % self.count;
        }
        Some(range)
    }
}

pub struct SpillAllocator;

impl SpillAllocator {
    unsafe fn allocate(&self, layout: Layout, zeroed: bool) -> *mut u8 {
        let allocate = |heap: *mut c_void| -> *mut u8 {
            unsafe {
                if zeroed {
                    mi_heap_zalloc_aligned(heap, layout.size(), layout.align()).cast()
                } else {
                    mi_heap_malloc_aligned(heap, layout.size(), layout.align()).cast()
                }
            }
        };
        let heap = HEAP.load(Ordering::Acquire);
        // Objects larger than mimalloc's arena range, or with exceptional page
        // alignment, retain the allocator's native OS path instead of acquiring
        // an artificial maximum allocation size from this backing strategy.
        if heap.is_null() || layout.size() > MAX_ARENA_SIZE - 32 * MIB || layout.align() > 64 * 1024
        {
            return if zeroed {
                unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) }
            } else {
                unsafe { mimalloc::MiMalloc.alloc(layout) }
            };
        }
        let pointer = allocate(heap);
        if !pointer.is_null() {
            return pointer;
        }
        let mut backing = BACKING.lock().unwrap_or_else(|error| error.into_inner());
        // Another thread may have grown the store; older arenas may also have
        // space again after the buffers which filled them were freed.
        for mapping in &backing.mappings[..backing.count] {
            let pointer = allocate(mapping.heap as *mut c_void);
            if !pointer.is_null() {
                HEAP.store(mapping.heap as *mut c_void, Ordering::Release);
                return pointer;
            }
        }
        if let Err(error) = backing.grow(layout.size()) {
            // GlobalAlloc must not allocate to report a backing-store failure.
            let mut message = [0 as libc::c_char; 160];
            unsafe {
                let length = libc::snprintf(
                    message.as_mut_ptr(),
                    message.len(),
                    c"ref-type: cannot extend heap spill storage (OS error %d)\n".as_ptr(),
                    error.raw_os_error().unwrap_or(0),
                );
                if length > 0 {
                    libc::write(
                        libc::STDERR_FILENO,
                        message.as_ptr().cast(),
                        (length as usize).min(message.len() - 1),
                    );
                }
            }
            return std::ptr::null_mut();
        }
        allocate(HEAP.load(Ordering::Acquire))
    }
}

// SAFETY: all allocations and frees go through mimalloc. Retrying an allocation
// after registering fresh arenas does not invalidate any previous allocation.
unsafe impl GlobalAlloc for SpillAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { self.allocate(layout, false) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        unsafe { self.allocate(layout, true) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { mimalloc::MiMalloc.dealloc(pointer, layout) }
    }
}

/// Enable before loading source snapshots, including in the supervisor. The
/// requested amount is a resident-memory target, never an address-space limit.
pub fn initialize(directory: &Path, target_mib: Option<u64>) -> io::Result<()> {
    // Source inspection and --no-cache need no semantic cache directory. Its
    // nearest existing parent is on the intended filesystem and can hold an
    // unnamed backing file without creating artifacts in the source tree.
    let path = std::path::absolute(directory)?;
    let mut directory = path
        .ancestors()
        .find_map(|path| File::open(path).ok())
        .ok_or_else(|| io::Error::from_raw_os_error(libc::ENOENT))?;
    if memory_filesystem(&directory)? {
        // /tmp and explicitly chosen caches may be tmpfs. Such a backing file
        // cannot release RAM without swap, so prefer an actual disk directory.
        let executable = std::env::current_exe()?;
        directory = [
            std::env::current_dir()?,
            executable.parent().unwrap().to_owned(),
        ]
        .into_iter()
        .filter_map(|path| File::open(path).ok())
        .find(|file| memory_filesystem(file).is_ok_and(|memory| !memory))
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Unsupported,
                "heap spilling needs a disk-backed directory; set REF_TYPE_GRAPH_SPILL_DIR",
            )
        })?;
    }
    let mut backing = BACKING.lock().unwrap_or_else(|error| error.into_inner());
    backing.directory = directory.as_raw_fd();
    unsafe { ref_type_spill_configure(MAX_ARENA_SIZE - 32 * MIB) };
    backing.grow(0)?;
    let _ = directory.into_raw_fd();
    drop(backing);
    let target = target_mib.unwrap_or(3072).saturating_mul(MIB as u64);
    if target != 0 {
        std::thread::Builder::new()
            .name("heap-paging".to_owned())
            .spawn(move || monitor(target))?;
    }
    Ok(())
}

fn memory_filesystem(directory: &File) -> io::Result<bool> {
    let mut stat: libc::statfs = unsafe { std::mem::zeroed() };
    // SAFETY: stat is writable and directory owns a live fd.
    if unsafe { libc::fstatfs(directory.as_raw_fd(), &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // RAMFS_MAGIC from Linux's uapi/linux/magic.h is absent from libc bindings.
    Ok(stat.f_type == libc::TMPFS_MAGIC || stat.f_type as u32 == 0x8584_58f6)
}

fn monitor(target: u64) {
    let mut last_collection = None::<Instant>;
    loop {
        std::thread::sleep(Duration::from_millis(100));
        let resident = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|status| {
                status.lines().find_map(|line| {
                    line.strip_prefix("VmRSS:")?
                        .split_whitespace()
                        .next()?
                        .parse::<u64>()
                        .ok()
                })
            })
            .unwrap_or(0)
            .saturating_mul(1024);
        if resident < target.saturating_mul(4) / 5 {
            continue;
        }
        // Paging can continue frequently while live tables keep RSS high.
        // Repeatedly discarding judgement caches would redo useful checking.
        if last_collection.is_none_or(|last| last.elapsed() >= Duration::from_secs(5)) {
            sema::request_collection();
            last_collection = Some(Instant::now());
        }
        // Never hold the allocator lock across page I/O. The arena mappings
        // remain valid until process exit, even while allocations continue.
        let range = BACKING
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .next_range();
        if let Some(range) = range {
            // PAGEOUT preserves live bytes and can be ignored by the kernel
            // for busy pages. It imposes no hard limit and needs no restart.
            // SAFETY: the page-aligned file mapping is live and shared.
            if unsafe { libc::madvise(range.start as *mut c_void, range.len, libc::MADV_PAGEOUT) }
                == 0
            {
                PAGEOUT_BYTES.fetch_add(range.len as u64, Ordering::Relaxed);
            }
        }
    }
}

pub fn pageout_bytes() -> u64 {
    PAGEOUT_BYTES.load(Ordering::Relaxed)
}
