use project::{SourceSnapshot, package_loader, workspace::default_cache_directory};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ref-workspace-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    fn package(&self, path: &str, name: &str, dependencies: &str) {
        self.write(
            &format!("{path}/ref.toml"),
            &format!("[package]\nname = '{name}'\n{dependencies}"),
        );
        self.write(&format!("{path}/src/root.ref"), r"\module Main {}");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn workspace_loads_members_and_shared_dependencies_once() {
    let fixture = Fixture::new();
    fixture.write(
        "workspace/ref.toml",
        "[workspace]\npackages = ['left', 'right', 'left/../left']\n",
    );
    fixture.package("base", "base", "");
    for name in ["left", "right"] {
        fixture.package(
            &format!("workspace/{name}"),
            name,
            "[dependencies]\nbase = {path = '../../base'}\n",
        );
    }
    fixture.package("workspace/unlisted", "unlisted", "");
    let root = fixture.0.join("workspace");
    let graph = package_loader::load_package(&root).unwrap();
    assert_eq!(
        graph
            .packages
            .iter()
            .map(|package| package.name.as_str())
            .collect::<Vec<_>>(),
        ["base", "left", "right"]
    );
    assert_eq!(
        graph
            .entry_packages
            .iter()
            .map(|id| graph.packages[id.0].name.as_str())
            .collect::<Vec<_>>(),
        ["left", "right"]
    );
    let snapshot = SourceSnapshot::read(&root).unwrap();
    assert!(
        snapshot
            .source(fixture.0.join("base/src/root.ref"))
            .is_some()
    );
    assert!(snapshot.source(root.join("left/src/root.ref")).is_some());
    assert!(
        snapshot
            .source(root.join("unlisted/src/root.ref"))
            .is_none()
    );
    assert_eq!(snapshot.default_cache_directory(), root.join("refcache"));
}

#[test]
fn workspace_cache_is_shared_by_members_and_their_source_files() {
    let fixture = Fixture::new();
    fixture.write("ref.toml", "[workspace]\npackages = ['nested/member']\n");
    fixture.package("nested/member", "member", "");
    fixture.package("unlisted", "unlisted", "");
    let shared = fixture.0.join("refcache");
    for path in ["", "nested/member", "nested/member/src/root.ref"] {
        let entry = fixture.0.join(path);
        assert_eq!(default_cache_directory(&entry).unwrap(), shared);
        let snapshot = SourceSnapshot::read(entry).unwrap();
        assert_eq!(snapshot.default_cache_directory(), shared);
        assert!(snapshot.source(fixture.0.join("ref.toml")).is_some());
    }
    assert_eq!(
        default_cache_directory(fixture.0.join("unlisted")).unwrap(),
        fixture.0.join("unlisted/refcache")
    );
}

#[test]
fn workspace_can_include_its_root_package() {
    let fixture = Fixture::new();
    fixture.write("ref.toml", "[package]\nname = 'app'\n[workspace]\npackages = ['member', '.']\n[dependencies]\nmember = {path = 'member'}\n");
    fixture.write("src/root.ref", r"\module Main {}");
    fixture.package("member", "member", "");
    let graph = package_loader::load_package(&fixture.0).unwrap();
    assert_eq!(graph.packages.len(), 2);
    assert_eq!(graph.entry_packages.len(), 2);
    assert_eq!(
        default_cache_directory(fixture.0.join("member")).unwrap(),
        fixture.0.join("refcache")
    );
}

#[cfg(unix)]
#[test]
fn workspace_membership_uses_canonical_package_paths() {
    let fixture = Fixture::new();
    fixture.write("ref.toml", "[workspace]\npackages = ['alias']\n");
    fixture.package("member", "member", "");
    std::os::unix::fs::symlink("member", fixture.0.join("alias")).unwrap();
    for path in ["alias", "member"] {
        assert_eq!(
            default_cache_directory(fixture.0.join(path)).unwrap(),
            fixture.0.join("refcache")
        );
    }
    assert_eq!(
        package_loader::load_package(&fixture.0)
            .unwrap()
            .packages
            .len(),
        1
    );
}
