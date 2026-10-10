/* Linux/glibc: trace large allocations without changing the checker.
 * cc -shared -fPIC -O2 benchmarks/alloc_trace.c -o /tmp/ref-type-alloc-trace.so
 * LD_PRELOAD=/tmp/ref-type-alloc-trace.so python3 benchmarks/check.py PATH
 * Resolve executable offsets with: addr2line -Cf -e target/debug/cli OFFSET
 */
#define _GNU_SOURCE
#include <execinfo.h>
#include <stddef.h>
#include <stdio.h>
#include <unistd.h>

extern void *__libc_malloc(size_t);
extern void *__libc_realloc(void *, size_t);

static void trace(size_t size) {
    if (size < 128 * 1024 * 1024) return;
    char message[80];
    int length = snprintf(message, sizeof message, "allocation bytes=%zu\n", size);
    ssize_t written = write(STDERR_FILENO, message, (size_t)length);
    (void)written;
    void *frames[24];
    int count = backtrace(frames, 24);
    backtrace_symbols_fd(frames, count, STDERR_FILENO);
}

void *malloc(size_t size) {
    trace(size);
    return __libc_malloc(size);
}

void *realloc(void *pointer, size_t size) {
    trace(size);
    return __libc_realloc(pointer, size);
}
