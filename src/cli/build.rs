fn main() {
    println!("cargo:rerun-if-changed=src/spill_mimalloc.c");
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux")
        || [
            "CARGO_FEATURE_SYSTEM_ALLOCATOR",
            "CARGO_FEATURE_LARGE_ALLOCATION_PROFILE",
            "CARGO_FEATURE_SMALL_ALLOCATION_PROFILE",
        ]
        .iter()
        .any(|feature| std::env::var_os(feature).is_some())
    {
        return;
    }
    cc::Build::new()
        .include(std::env::var_os("DEP_MIMALLOC_INCLUDE_DIR").expect("mimalloc headers"))
        .file("src/spill_mimalloc.c")
        .compile("ref_type_spill_mimalloc");
}
