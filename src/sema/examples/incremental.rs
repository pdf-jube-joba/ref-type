//! Run with: cargo run --release -p sema --example incremental -- libs/std libs/std/src/Algebra/Algebra.ref
use sema::{Database, SourceSnapshot};
use std::{path::PathBuf, time::Instant};

fn main() {
    let mut arguments = std::env::args_os().skip(1);
    let entry = PathBuf::from(arguments.next().expect("package or root file"));
    let edited_file = PathBuf::from(arguments.next().expect("external module file to edit"));
    let source = SourceSnapshot::read(entry).unwrap();
    let mut database = Database::new();
    let mut check = |label, snapshot: &SourceSnapshot| {
        let started = Instant::now();
        let result = database.check(snapshot);
        println!("{label}: {:?}; {:?}", started.elapsed(), database.stats());
        assert!(result.is_success(), "{:?}", result.diagnostics);
        result
    };
    let cold = check("cold", &source);
    let warm = check("warm", &source);
    assert_eq!(cold, warm);
    let text = &source
        .source(&edited_file)
        .expect("file belongs to snapshot")
        .text;
    let edited = source.with_file(
        &edited_file,
        format!(
            "{text}\n\\definition incrementalProbe: \\Prop := \\forall (P: \\Prop) -> P -> P;\n"
        ),
    );
    let changed = check("edited", &edited);
    let started = Instant::now();
    let rebuilt = Database::new().check(&edited);
    println!("clean edited: {:?}", started.elapsed());
    assert_eq!(changed, rebuilt);
}
