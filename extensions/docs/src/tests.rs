use super::*;
use axum::{
    body::{Body, to_bytes},
    http::Request,
};
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};
use tower::ServiceExt;

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ref-docs-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("demo/src/Outer")).unwrap();
        fs::create_dir_all(path.join("empty")).unwrap();
        fs::create_dir_all(path.join("refcache")).unwrap();
        fs::write(path.join("refcache/secret.ref"), "do not expose").unwrap();
        fs::write(path.join("secret.txt"), "do not expose").unwrap();
        fs::write(
            path.join("README.md"),
            "# Libraries\n\n[Demo](demo/README.md)\n\n[Source](demo/src/root.ref)",
        )
        .unwrap();
        fs::write(path.join("demo/README.md"), "# Demo\n\nA library.").unwrap();
        fs::write(
            path.join("demo/src/root.ref"),
            r#"/* **Outer** documentation. */
\module Outer;
\module Inline {
  /* Japanese 日本語, \(\forall x_i \in A\), <script>alert(1)</script> & quotes. */
  \definition identity (A: \Set): A -> A := \fun (x: A) => x;
}
"#,
        )
        .unwrap();
        fs::write(
            path.join("demo/src/Outer.ref"),
            r"/* Naturals. */
\inductive Nat: \VType := | zero: Nat | succ: Nat -> Nat;
\module Child;",
        )
        .unwrap();
        fs::write(
            path.join("demo/src/Outer/Child.ref"),
            r"\structure Pair[A: \Set]: \Set { first: A, second: A }",
        )
        .unwrap();
        fs::write(
            path.join("demo/src/empty.ref"),
            "/* No declarations here. */",
        )
        .unwrap();
        fs::write(path.join("demo/src/broken.ref"), r"\definition invalid: ;").unwrap();
        Self(path)
    }
    fn catalog(&self) -> Catalog {
        Catalog::read(&self.0).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn enumerates_sources_and_handles_empty_and_invalid_files() {
    let f = Fixture::new();
    let c = f.catalog();
    assert_eq!(c.files.len(), 5);
    let root = c
        .files
        .iter()
        .position(|f| f.path.ends_with("root.ref"))
        .unwrap();
    let outer = c
        .files
        .iter()
        .position(|f| f.path.ends_with("Outer.ref"))
        .unwrap();
    let child = c
        .files
        .iter()
        .position(|f| f.path.ends_with("Child.ref"))
        .unwrap();
    let html = render::file(&c, root);
    assert!(html.contains(&format!("href=\"/file/{outer}\"")));
    assert!(html.contains("Inline.identity"));
    assert!(html.contains("&lt;script&gt;alert(1)&lt;/script&gt;"));
    assert!(html.contains("日本語"));
    assert!(html.contains(r"\(\forall x_i \in A\)"));
    assert!(render::file(&c, outer).contains(&format!("href=\"/file/{child}\"")));
    assert!(render::file(&c, child).contains("first: A, second: A"));
    for (id, file) in c.files.iter().enumerate() {
        if file.path.ends_with("empty.ref") {
            assert!(render::file(&c, id).contains("No named declarations"));
        }
        if file.path.ends_with("broken.ref") {
            assert!(render::file(&c, id).contains("Could not parse"));
        }
    }
    assert!(render::source(&c, root).contains("id=\"L4\""));
    assert!(render::directory(&c, 0).contains("Library explorer"));
    assert!(render::search(&c).contains("identity"));
}

#[test]
fn markdown_is_safe_and_preserves_code_and_math() {
    let c = Catalog::default();
    let md = r#"# Heading

**Bold** and `x < y`, \(a_i * b_j\), \[x_{i} < y\].

<script>alert('x')</script>
<img src=x onerror=alert(1)>

[bad](javascript:alert%281%29) [data](data:text/html,hello)
[ok](https://example.com/ "a & b") ![alt](https://example.com/image.png)

```ref
\( x_1 * y_2 \)
```
"#;
    let html = render::markdown(&c, std::path::Path::new(""), md);
    assert!(html.contains("<strong>Bold</strong>"));
    assert!(html.contains("x &lt; y"));
    assert!(html.contains(r"\(a_i * b_j\)"));
    assert!(html.contains(r"\[x_{i} &lt; y\]"));
    assert!(html.contains(r"\( x_1 * y_2 \)"));
    assert!(!html.contains("<script"));
    assert!(!html.contains("<img"));
    assert!(!html.contains("href=\"javascript:"));
    assert!(!html.contains("href=\"data:"));
    assert!(html.contains("href=\"https://example.com/\""));
    assert!(html.contains("a &amp; b"));
    for attack in [
        "[x](JaVaScRiPt:alert%281%29)",
        "[x](//evil.example/a)",
        "[x](file:///etc/passwd)",
        "[x](&#106;avascript:alert%281%29)",
    ] {
        assert!(!render::markdown(&c, std::path::Path::new(""), attack).contains("href="));
    }
}

#[test]
fn markdown_heading_links_keep_fragments_and_have_distinct_ids() {
    let f = Fixture::new();
    let c = f.catalog();
    let html = render::markdown(
        &c,
        std::path::Path::new(""),
        "# 日本語 `x`\n\n# 日本語 `x`\n\n[here](#日本語-x)\n\n[there](demo/README.md#demo)",
    );
    assert!(html.contains("id=\"md-日本語-x\""));
    assert!(html.contains("id=\"md-日本語-x-1\""));
    assert!(html.contains("href=\"#md-日本語-x\""));
    assert!(html.contains("#md-demo\""));
}

#[test]
fn missing_paths_relative_links_and_symlinks_are_safe() {
    let f = Fixture::new();
    assert!(
        Catalog::read(&f.0.join("missing"))
            .err()
            .unwrap()
            .contains("--libs")
    );
    assert!(
        Catalog::read(&f.0.join("README.md"))
            .err()
            .unwrap()
            .contains("not a directory")
    );
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("/etc/passwd", f.0.join("escape.ref")).unwrap();
        std::os::unix::fs::symlink(&f.0, f.0.join("loop")).unwrap();
    }
    let c = f.catalog();
    assert_eq!(c.files.len(), 5);
    let base = std::path::Path::new("demo/src");
    assert!(c.link(base, "../../README.md").is_some());
    for path in [
        "../../../etc/passwd",
        "/etc/passwd",
        "%2e%2e/secret.txt",
        "../../secret.txt",
        "../../escape.ref",
    ] {
        assert!(c.link(base, path).is_none(), "{path}");
    }
}

#[tokio::test]
async fn http_routes_links_headers_and_traversal() {
    let f = Fixture::new();
    let c = f.catalog();
    let mut urls = vec![
        "/".to_string(),
        "/search?q=%3Cscript%3E".into(),
        "/style.css".into(),
        "/app.js".into(),
    ];
    urls.extend((0..c.directories.len()).map(|id| format!("/dir/{id}")));
    urls.extend((0..c.files.len()).flat_map(|id| [format!("/file/{id}"), format!("/source/{id}")]));
    let app = app(c);
    for url in urls {
        let response = app
            .clone()
            .oneshot(Request::builder().uri(&url).body(Body::empty()).unwrap())
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK, "{url}");
        assert!(
            response.headers()["content-security-policy"]
                .to_str()
                .unwrap()
                .contains("default-src 'none'")
        );
        assert_eq!(response.headers()["x-content-type-options"], "nosniff");
        assert!(
            !to_bytes(response.into_body(), usize::MAX)
                .await
                .unwrap()
                .is_empty()
        );
    }
    for url in [
        "/file/9999",
        "/source/9999",
        "/dir/9999",
        "/../Cargo.toml",
        "/source/%2e%2e%2fetc%2fpasswd",
        "/libs/secret.txt",
        "/etc/passwd",
    ] {
        let response = app
            .clone()
            .oneshot(Request::builder().uri(url).body(Body::empty()).unwrap())
            .await
            .unwrap();
        assert!(response.status().is_client_error(), "{url}");
    }
}

#[test]
fn repository_libraries_parse_and_link() {
    let c = Catalog::read(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../libs")).unwrap();
    assert!(c.files.len() >= 200);
    assert!(c.directories[0].directories.len() >= 8);
    for file in &c.files {
        assert!(
            file.error.is_none(),
            "{}: {:?}",
            file.path.display(),
            file.error
        );
    }
    assert!(
        c.files
            .iter()
            .flat_map(|file| &file.items)
            .any(|item| !item.documentation.is_empty())
    );
}
