use sema::{CheckOptions, Database, SourceSnapshot};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Cache(PathBuf);
impl Cache {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(std::env::temp_dir().join(format!(
            "ref-partial-artifacts-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )))
    }
}
impl Drop for Cache {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn snapshot() -> SourceSnapshot {
    let mut snapshot = SourceSnapshot::new("/partial/app");
    snapshot.insert(
        "/partial/app/ref.toml",
        "[package]\nname='app'\n[dependencies]\nbase={path='../base'}\n",
    );
    snapshot.insert("/partial/app/src/root.ref",r"\module Main { \import base.Left[] \as L; \import base.Right[] \as R; \import base.Common[] \as B; \definition left: B.Unit := L.value; \definition right: B.Unit := R.value; \infer right; }");
    snapshot.insert("/partial/base/ref.toml", "[package]\nname='base'\n");
    snapshot.insert("/partial/base/src/root.ref",r"\module Common { \inductive Unit: \Set := | unit: Unit; } \module Left { \import \root.Common[] \as C; \definition value: C.Unit := C.Unit::unit; } \module Right { \import \root.Common[] \as C; \definition value: C.Unit := C.Unit::unit; }");
    snapshot
}
#[test]
fn overlapping_partial_artifacts_combine_in_both_orders_and_feed_a_consumer() {
    for order in [["Left", "Right"], ["Right", "Left"]] {
        let cache = Cache::new();
        let snapshot = snapshot();
        for name in order {
            let mut database = Database::with_cache(&cache.0);
            let result = database.module_with_options(
                &snapshot,
                &["base".into(), name.into()],
                &CheckOptions::default(),
            );
            assert!(result.is_success(), "{name}: {result:?}");
            assert!(result.modules.iter().all(|module| module.path.len() == 1
                || module.path[1] == name
                || module.path[1] == "Common"));
        }
        let mut union = Database::with_cache(&cache.0);
        let combined =
            union.module_with_options(&snapshot, &["base".into()], &CheckOptions::default());
        assert!(combined.is_success(), "{combined:?}");
        assert_eq!(union.stats().checked_modules, 0, "{:?}", union.stats());
        assert_eq!(union.cache_store_stats().environment_read_bytes, 0);
        let mut consumer = Database::with_cache(&cache.0);
        let result = consumer.check(&snapshot);
        assert!(result.is_success(), "{result:?}");
        assert_eq!(
            result,
            Database::new().check_with_options(
                &snapshot,
                &CheckOptions {
                    collect_statistics: true,
                    ..Default::default()
                }
            )
        );
        assert_eq!(
            consumer.stats().checked_modules,
            2,
            "{:?}",
            consumer.stats()
        );
    }
}
