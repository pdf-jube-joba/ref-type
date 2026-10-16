use quote::ToTokens;
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use syn::visit_mut::VisitMut;

fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        if path.file_name().is_some_and(|name| {
            matches!(
                name.to_str(),
                Some("tests" | "examples" | "benches" | "target")
            )
        }) {
            return;
        }
        println!("cargo:rerun-if-changed={}", path.display());
        for entry in fs::read_dir(path).unwrap() {
            collect(&entry.unwrap().path(), files);
        }
    } else if (path.extension().is_some_and(|extension| extension == "rs")
        && path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name != "tests.rs" && !name.starts_with("test_")))
        || path.file_name().is_some_and(|name| name == "Cargo.toml")
    {
        files.push(path.to_owned());
    }
}
fn item(hash: &mut Sha256, kind: &[u8], name: &[u8], value: &[u8]) {
    for bytes in [kind, name, value] {
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
}
fn test_only(attributes: &[syn::Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        attribute.path().is_ident("test")
            || (attribute.path().is_ident("cfg")
                && attribute
                    .parse_args::<syn::Path>()
                    .is_ok_and(|path| path.is_ident("test")))
    })
}
struct RuntimeSource;
impl VisitMut for RuntimeSource {
    fn visit_item_mut(&mut self, item: &mut syn::Item) {
        let attributes: &[syn::Attribute] = match item {
            syn::Item::Const(v) => &v.attrs,
            syn::Item::Enum(v) => &v.attrs,
            syn::Item::ExternCrate(v) => &v.attrs,
            syn::Item::Fn(v) => &v.attrs,
            syn::Item::ForeignMod(v) => &v.attrs,
            syn::Item::Impl(v) => &v.attrs,
            syn::Item::Macro(v) => &v.attrs,
            syn::Item::Mod(v) => &v.attrs,
            syn::Item::Static(v) => &v.attrs,
            syn::Item::Struct(v) => &v.attrs,
            syn::Item::Trait(v) => &v.attrs,
            syn::Item::TraitAlias(v) => &v.attrs,
            syn::Item::Type(v) => &v.attrs,
            syn::Item::Union(v) => &v.attrs,
            syn::Item::Use(v) => &v.attrs,
            _ => &[],
        };
        if test_only(attributes) {
            *item = syn::Item::Verbatim(Default::default());
        } else {
            syn::visit_mut::visit_item_mut(self, item);
        }
    }
    fn visit_impl_item_mut(&mut self, item: &mut syn::ImplItem) {
        let attributes: &[syn::Attribute] = match item {
            syn::ImplItem::Const(v) => &v.attrs,
            syn::ImplItem::Fn(v) => &v.attrs,
            syn::ImplItem::Type(v) => &v.attrs,
            syn::ImplItem::Macro(v) => &v.attrs,
            _ => &[],
        };
        if test_only(attributes) {
            *item = syn::ImplItem::Verbatim(Default::default());
        } else {
            syn::visit_mut::visit_impl_item_mut(self, item);
        }
    }
    fn visit_trait_item_mut(&mut self, item: &mut syn::TraitItem) {
        let attributes: &[syn::Attribute] = match item {
            syn::TraitItem::Const(v) => &v.attrs,
            syn::TraitItem::Fn(v) => &v.attrs,
            syn::TraitItem::Type(v) => &v.attrs,
            syn::TraitItem::Macro(v) => &v.attrs,
            _ => &[],
        };
        if test_only(attributes) {
            *item = syn::TraitItem::Verbatim(Default::default());
        } else {
            syn::visit_mut::visit_trait_item_mut(self, item);
        }
    }
}
fn runtime_source(bytes: Vec<u8>) -> Vec<u8> {
    let source = std::str::from_utf8(&bytes).expect("Rust source encoding");
    let mut file = syn::parse_file(source).expect("parse checker implementation");
    RuntimeSource.visit_file_mut(&mut file);
    file.into_token_stream().to_string().into_bytes()
}
fn main() {
    let root = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    let mut files = vec![root.join("Cargo.lock"), root.join("Cargo.toml")];
    for name in [
        "artifact",
        "artifact-derive",
        "diagnostics",
        "timing",
        "kernel",
        "syntax",
        "project",
        "resolve",
        "elaboration",
        "sema",
    ] {
        collect(&root.join("src").join(name), &mut files);
    }
    for name in [
        "rust-toolchain",
        "rust-toolchain.toml",
        ".cargo/config",
        ".cargo/config.toml",
    ] {
        let path = root.join(name);
        println!("cargo:rerun-if-changed={}", path.display());
        if path.is_file() {
            files.push(path);
        }
    }
    files.sort();
    let mut hash = Sha256::new();
    for file in files {
        println!("cargo:rerun-if-changed={}", file.display());
        let bytes = fs::read(&file).unwrap();
        let bytes = if file.extension().is_some_and(|extension| extension == "rs") {
            runtime_source(bytes)
        } else {
            bytes
        };
        item(
            &mut hash,
            b"file",
            file.strip_prefix(&root)
                .unwrap()
                .as_os_str()
                .as_encoded_bytes(),
            &bytes,
        );
    }
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    item(
        &mut hash,
        b"compiler",
        b"rustc",
        &Command::new(rustc).arg("-vV").output().unwrap().stdout,
    );
    // Cargo exposes resolved target cfgs and features to build scripts. Include the
    // compilation inputs, but never paths such as OUT_DIR or CARGO_MANIFEST_DIR.
    let mut environment: Vec<_> = std::env::vars()
        .filter(|(name, _)| {
            name.starts_with("CARGO_FEATURE_")
                || name.starts_with("CARGO_CFG_")
                || matches!(
                    name.as_str(),
                    "TARGET"
                        | "HOST"
                        | "PROFILE"
                        | "OPT_LEVEL"
                        | "DEBUG"
                        | "CARGO_ENCODED_RUSTFLAGS"
                        | "RUSTFLAGS"
                )
        })
        .collect();
    environment.sort();
    for (name, value) in environment {
        println!("cargo:rerun-if-env-changed={name}");
        item(&mut hash, b"environment", name.as_bytes(), value.as_bytes());
    }
    let revision: String = hash
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    println!("cargo:rustc-env=REF_SEMA_REVISION={revision}");
}
