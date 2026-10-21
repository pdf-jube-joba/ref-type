//! Route large buffers through libc for heaptrack; keep transient small-node
//! allocations on mimalloc so detailed profiles remain practical on libraries.
use std::alloc::{GlobalAlloc, Layout, System};

struct ProfileAllocator;

#[global_allocator]
static ALLOCATOR: ProfileAllocator = ProfileAllocator;

// SAFETY: allocation and deallocation select the same allocator from Layout.
// GlobalAlloc's default realloc copies through these methods when sizes cross
// the threshold. Neither allocator's pointer is passed to the other allocator.
unsafe impl GlobalAlloc for ProfileAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        #[cfg(feature = "small-allocation-profile")]
        {
            use std::sync::atomic::{AtomicUsize, Ordering};
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let selected = layout.size() < 64 * 1024
                && NEXT.fetch_add(1, Ordering::Relaxed).is_multiple_of(64);
            let prefix = layout.align().max(8);
            let Some(size) = layout.size().checked_add(prefix) else {
                return std::ptr::null_mut();
            };
            let Ok(actual) = Layout::from_size_align(size, layout.align()) else {
                return std::ptr::null_mut();
            };
            let pointer = if selected {
                unsafe { System.alloc(actual) }
            } else {
                unsafe { mimalloc::MiMalloc.alloc(actual) }
            };
            if pointer.is_null() {
                return pointer;
            }
            // SAFETY: prefix is part of this allocation; it preserves alignment.
            unsafe {
                pointer.add(prefix - 1).write(u8::from(selected));
            }
            return unsafe { pointer.add(prefix) };
        }
        #[cfg(not(feature = "small-allocation-profile"))]
        if layout.size() >= 64 * 1024 {
            unsafe { System.alloc(layout) }
        } else {
            unsafe { mimalloc::MiMalloc.alloc(layout) }
        }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        #[cfg(feature = "small-allocation-profile")]
        {
            let prefix = layout.align().max(8);
            // SAFETY: alloc wrote this byte and returned the following address.
            let selected = unsafe { pointer.sub(1).read() } != 0;
            let actual = Layout::from_size_align(layout.size() + prefix, layout.align()).unwrap();
            let pointer = unsafe { pointer.sub(prefix) };
            if selected {
                unsafe { System.dealloc(pointer, actual) }
            } else {
                unsafe { mimalloc::MiMalloc.dealloc(pointer, actual) }
            }
        }
        #[cfg(not(feature = "small-allocation-profile"))]
        if layout.size() >= 64 * 1024 {
            unsafe { System.dealloc(pointer, layout) }
        } else {
            unsafe { mimalloc::MiMalloc.dealloc(pointer, layout) }
        }
    }
}
