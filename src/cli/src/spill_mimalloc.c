#include <mimalloc.h>

// Use the linked allocator's enum rather than duplicating its option numbers.
void ref_type_spill_configure(size_t max_object_bytes) {
    mi_option_set(mi_option_arena_max_object_size, (long)(max_object_bytes / 1024));
}
