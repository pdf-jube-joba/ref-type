use super::*;
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ref-lsp-cache-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        Self(directory)
    }

    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, text).unwrap();
        path
    }

    fn package(&self, path: &str, name: &str, dependencies: &str, text: &str) -> PathBuf {
        self.write(
            &format!("{path}/ref.toml"),
            &format!("[package]\nname = '{name}'\n{dependencies}"),
        );
        self.write(&format!("{path}/src/root.ref"), text)
    }

    fn seed(&self, entry: &Path) -> PathBuf {
        let cache = sema::default_cache_directory(entry).unwrap();
        let mut database = Database::with_cache(&cache);
        let snapshot = database.read_snapshot(entry, true).unwrap();
        let result = database.check(&snapshot);
        assert!(result.is_success(), "{result:?}");
        assert_eq!(database.stats().cache_write_failures, 0);
        cache
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn open(server: &mut Server, connection: &Connection, file: &Path) {
    server
        .notification(
            connection,
            Notification::new(
                "textDocument/didOpen".into(),
                json!({ "textDocument": {
                    "uri": Url::from_file_path(file).unwrap().as_str(),
                    "text": fs::read_to_string(file).unwrap(), "version": 1
                }}),
            ),
        )
        .unwrap();
}

fn diagnostics(client: &Connection, file: &Path) -> Vec<Value> {
    let uri = Url::from_file_path(file).unwrap();
    let mut diagnostics = None;
    while let Ok(message) = client.receiver.try_recv() {
        let Message::Notification(notification) = message else {
            panic!("expected diagnostics");
        };
        assert_eq!(notification.method, "textDocument/publishDiagnostics");
        if notification.params["uri"] == uri.as_str() {
            diagnostics = Some(
                notification.params["diagnostics"]
                    .as_array()
                    .unwrap()
                    .clone(),
            );
        }
    }
    diagnostics.expect("diagnostics were published for the open file")
}

fn query(server: &mut Server, method: &str, file: &Path, token: &str) -> Value {
    let text = fs::read_to_string(file).unwrap();
    let byte = text.rfind(token).unwrap();
    server.request(&Request::new(
        1.into(),
        method.into(),
        json!({
            "textDocument": {"uri": Url::from_file_path(file).unwrap().as_str()},
            "position": position(&text, byte), "context": {"includeDeclaration": true}
        }),
    ))
}

const BASE: &str = r"\module Core { \definition P: \Prop := \forall (A: \Prop) -> A -> A; }";
const APP: &str = r"\module Main { \import base.Core[] \as B; \definition p: \Prop := B.P; }";

#[test]
fn workspace_cache_restores_diagnostics_hover_definitions_and_references() {
    let fixture = Fixture::new();
    let workspace = fixture.0.join("workspace");
    fixture.write(
        "workspace/ref.toml",
        "[workspace]\npackages = ['left', 'right']\n",
    );
    let base = fixture.package("base", "base", "", BASE);
    let left = fixture.package(
        "workspace/left",
        "left",
        "[dependencies]\nbase = {path = '../../base'}\n",
        APP,
    );
    let right = fixture.package("workspace/right", "right", "", r"\module Other {}");
    let cache = fixture.seed(&workspace);
    let (connection, client) = Connection::memory();
    let mut server = Server::new();
    open(&mut server, &connection, &left);
    assert!(diagnostics(&client, &left).is_empty());
    assert_eq!(server.databases.len(), 1);
    let database = &server.databases[&cache];
    assert_eq!(database.stats().checked_modules, 0);
    assert!(database.stats().package_hits >= 2);
    assert!(database.cache_store_stats().result_read_bytes > 0);

    let definition = query(&mut server, "textDocument/definition", &left, "B.P");
    assert_eq!(
        definition["uri"],
        Url::from_file_path(&base).unwrap().as_str()
    );
    let snapshot = SourceSnapshot::read(sema::source_entry(&left).unwrap()).unwrap();
    let cold = Database::new().check(&snapshot);
    let declaration = cold.definition_at(&left, APP.find("B.P").unwrap()).unwrap();
    assert_eq!(
        definition,
        location(&snapshot, &declaration.location).unwrap()
    );
    let hover = query(&mut server, "textDocument/hover", &left, "B.P");
    assert_eq!(hover["contents"]["value"], r"\Prop");
    let references = query(&mut server, "textDocument/references", &left, "B.P");
    assert_eq!(references.as_array().unwrap().len(), 2);
    assert!(references.as_array().unwrap().contains(&definition));

    open(&mut server, &connection, &right);
    assert!(diagnostics(&client, &right).is_empty());
    assert_eq!(server.databases.len(), 1);
    assert_eq!(server.databases[&cache].stats().checked_modules, 0);
    assert!(!workspace.join("left/refcache").exists());
    assert!(!workspace.join("right/refcache").exists());
}

#[test]
fn unlisted_packages_and_standalone_projects_keep_separate_caches() {
    let fixture = Fixture::new();
    fixture.write("ref.toml", "[workspace]\npackages = ['member']\n");
    let member = fixture.package("member", "member", "", r"\module Main {}");
    let unlisted = fixture.package("unlisted", "unlisted", "", r"\module Main {}");
    let standalone = fixture.write("standalone/Main.ref", r"\module Main {}");
    let (connection, client) = Connection::memory();
    let mut server = Server::new();
    for (file, cache) in [
        (&member, fixture.0.join("refcache")),
        (&unlisted, fixture.0.join("unlisted/refcache")),
        (&standalone, fixture.0.join("standalone/refcache")),
    ] {
        open(&mut server, &connection, file);
        assert!(diagnostics(&client, file).is_empty());
        assert!(server.databases.contains_key(&cache));
        assert!(cache.join("v2").is_dir());
        let mut restarted = Server::new();
        open(&mut restarted, &connection, file);
        assert!(diagnostics(&client, file).is_empty());
        assert_eq!(restarted.databases[&cache].stats().checked_modules, 0);
    }
    assert_eq!(server.databases.len(), 3);
}

#[test]
fn unsaved_edits_and_watched_dependency_changes_invalidate_disk_results() {
    let fixture = Fixture::new();
    fixture.write("ref.toml", "[workspace]\npackages = ['app']\n");
    let base = fixture.package("base", "base", "", BASE);
    let app = fixture.package(
        "app",
        "app",
        "[dependencies]\nbase = {path = '../base'}\n",
        APP,
    );
    let cache = fixture.seed(&fixture.0);
    let (connection, client) = Connection::memory();
    let mut server = Server::new();
    open(&mut server, &connection, &app);
    assert!(diagnostics(&client, &app).is_empty());
    let uri = Url::from_file_path(&app).unwrap();
    for text in [APP.replace("B.P", "B.missing"), APP.to_owned()] {
        server.notification(&connection, Notification::new(
            "textDocument/didChange".into(),
            json!({"textDocument": {"uri": uri.as_str()}, "contentChanges": [{"text": text}]}),
        )).unwrap();
        let errors = diagnostics(&client, &app);
        assert_eq!(errors.is_empty(), text == APP, "{errors:?}");
    }
    assert_eq!(fs::read_to_string(&app).unwrap(), APP);
    fixture.write("base/src/root.ref", &BASE.replace("P:", "Q:"));
    server.notification(&connection, Notification::new(
        "workspace/didChangeWatchedFiles".into(),
        json!({"changes": [{"uri": Url::from_file_path(&base).unwrap().as_str(), "type": 2}]}),
    )).unwrap();
    let errors = diagnostics(&client, &app);
    assert!(!errors.is_empty(), "a changed dependency must be checked");
    assert!(
        errors
            .iter()
            .any(|error| error["message"].as_str().unwrap().contains('P'))
    );
    assert!(server.databases[&cache].stats().checked_modules > 0);
    assert!(query(&mut server, "textDocument/definition", &app, "B.P").is_null());
}

#[test]
fn missing_cache_objects_fall_back_to_source_checking() {
    let fixture = Fixture::new();
    let file = fixture.package("app", "app", "", BASE);
    let cache = fixture.seed(&fixture.0.join("app"));
    fs::remove_dir_all(cache.join("v2/objects")).unwrap();
    let (connection, client) = Connection::memory();
    let mut server = Server::new();
    open(&mut server, &connection, &file);
    assert!(diagnostics(&client, &file).is_empty());
    assert!(server.databases[&cache].stats().checked_modules > 0);
}
