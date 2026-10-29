//! Compare decoding identical lease protection sets with the old and new I/O.
use std::{collections::BTreeSet, fs::File, io::Read, path::PathBuf, time::Instant};

#[derive(serde::Serialize, serde::Deserialize, PartialEq)]
struct Pins {
    artifacts: BTreeSet<[u8; 32]>,
    checkpoints: BTreeSet<[u8; 32]>,
    objects: BTreeSet<[u8; 32]>,
    read_objects: BTreeSet<[u8; 32]>,
}

fn main() {
    let mut args = std::env::args().skip(1);
    let directory = PathBuf::from(args.next().expect("output directory"));
    let count: usize = args
        .next()
        .unwrap_or_else(|| "8000".into())
        .parse()
        .unwrap();
    std::fs::create_dir(&directory).expect("use a fresh directory");
    let mut pins = Pins {
        artifacts: BTreeSet::new(),
        checkpoints: BTreeSet::new(),
        objects: BTreeSet::new(),
        read_objects: BTreeSet::new(),
    };
    let mut state = 0x243f6a8885a308d3_u64;
    for _ in 0..count {
        let mut digest = [0; 32];
        for part in digest.chunks_mut(8) {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            part.copy_from_slice(&state.to_le_bytes());
        }
        pins.read_objects.insert(digest);
    }
    let legacy = serde_json::to_vec(&pins).unwrap();
    let compact = postcard::to_allocvec(&pins).unwrap();
    std::fs::write(directory.join("legacy.json"), &legacy).unwrap();
    std::fs::write(directory.join("compact.bin"), &compact).unwrap();
    for mode in ["unbuffered-json", "bulk-json", "compact"] {
        for iteration in 0..3 {
            let start = Instant::now();
            let decoded: Pins = match mode {
                "unbuffered-json" => serde_json::from_reader(
                    File::open(directory.join("legacy.json"))
                        .unwrap()
                        .take(64 * 1024 * 1024),
                )
                .unwrap(),
                "bulk-json" => {
                    serde_json::from_slice(&std::fs::read(directory.join("legacy.json")).unwrap())
                        .unwrap()
                }
                _ => postcard::from_bytes(&std::fs::read(directory.join("compact.bin")).unwrap())
                    .unwrap(),
            };
            let seconds = start.elapsed().as_secs_f64();
            assert!(decoded == pins);
            println!(
                "{}",
                serde_json::json!({"mode":mode,"iteration":iteration,"seconds":seconds,"fingerprints":count,"legacy_bytes":legacy.len(),"compact_bytes":compact.len()})
            );
        }
    }
}
