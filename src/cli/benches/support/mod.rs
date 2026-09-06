use anyhow::{Context, Result, bail, ensure};
use clap::Parser;
use std::{
    collections::BTreeMap,
    fmt::Write as _,
    fs,
    hint::black_box,
    io::Write as _,
    path::PathBuf,
    process::Command,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

#[derive(Debug, Parser)]
#[command(about = "Measure ref-type in-process performance (optimized cargo bench profile)")]
struct Args {
    /// Run only cases whose name contains this text
    #[arg(long, default_value = "")]
    filter: String,
    /// List matching cases without running them
    #[arg(long)]
    list: bool,
    /// Number of measured samples per case
    #[arg(long, default_value_t = 20, value_parser = clap::value_parser!(u32).range(2..))]
    samples: u32,
    /// Warm-up wall time per case (at least one iteration always runs)
    #[arg(long, default_value_t = 200)]
    warmup_ms: u64,
    /// Minimum wall time per sample, including untimed setup/cleanup
    #[arg(long, default_value_t = 50, value_parser = clap::value_parser!(u64).range(1..))]
    sample_ms: u64,
    /// Save raw samples and environment metadata under this new name
    #[arg(long)]
    save_baseline: Option<String>,
    /// Compare median times with a previously saved baseline
    #[arg(long)]
    baseline: Option<String>,
    /// Directory for baseline TSV files (relative to the workspace root)
    #[arg(long, default_value = "target/benchmarks")]
    output_dir: PathBuf,
    // Cargo supplies this flag to harness=false benchmark executables.
    #[arg(long, hide = true)]
    bench: bool,
}

pub struct Case<'a> {
    name: &'static str,
    iteration: Box<dyn Fn() -> Duration + 'a>,
}

impl<'a> Case<'a> {
    pub fn new(name: &'static str, iteration: impl Fn() -> Duration + 'a) -> Self {
        Self {
            name,
            iteration: Box::new(iteration),
        }
    }
}

/// Keep the result alive until after the timer and prevent unused-work elimination.
pub fn timed<T>(operation: impl FnOnce() -> T) -> (Duration, T) {
    let start = Instant::now();
    let result = black_box(operation());
    (start.elapsed(), result)
}

fn baseline_path(args: &Args, name: &str) -> Result<PathBuf> {
    ensure!(
        !name.is_empty()
            && name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"-_".contains(&b)),
        "baseline names must contain only ASCII letters, digits, '-' or '_'"
    );
    Ok(args.output_dir.join(format!("{name}.tsv")))
}

fn median(values: &[f64]) -> f64 {
    let mut values = values.to_vec();
    values.sort_by(f64::total_cmp);
    let middle = values.len() / 2;
    if values.len() % 2 == 0 {
        (values[middle - 1] + values[middle]) / 2.0
    } else {
        values[middle]
    }
}

fn read_baseline(path: &PathBuf) -> Result<BTreeMap<String, Vec<f64>>> {
    let contents = fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    ensure!(
        contents.lines().next() == Some("# ref-type-bench-v1"),
        "unsupported baseline format"
    );
    let mut values = BTreeMap::<String, Vec<f64>>::new();
    for line in contents.lines().filter(|line| !line.starts_with('#')) {
        if line == "case\tsample\titerations\telapsed_ns\tns_per_iteration" {
            continue;
        }
        let fields: Vec<_> = line.split('\t').collect();
        ensure!(fields.len() == 5, "invalid baseline row: {line}");
        let value: f64 = fields[4].parse().context("invalid baseline duration")?;
        ensure!(
            value.is_finite() && value > 0.0,
            "baseline duration must be positive and finite"
        );
        values.entry(fields[0].to_owned()).or_default().push(value);
    }
    ensure!(!values.is_empty(), "baseline is empty");
    Ok(values)
}

fn command_output(program: &str, args: &[&str]) -> String {
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .unwrap_or_else(|| "unavailable".to_owned())
}

fn metadata(args: &Args) -> String {
    let mut text = String::from("# ref-type-bench-v1\n");
    let cpu = fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|info| {
            info.lines()
                .find(|line| line.starts_with("model name"))
                .map(str::to_owned)
        })
        .unwrap_or_else(|| "unavailable".to_owned());
    let entries = [
        (
            "unix_time",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
                .to_string(),
        ),
        ("git_commit", command_output("git", &["rev-parse", "HEAD"])),
        ("git_status", command_output("git", &["status", "--short"])),
        ("rustc", command_output("rustc", &["-Vv"])),
        ("system", command_output("uname", &["-a"])),
        ("cpu", cpu),
        ("RUSTFLAGS", std::env::var("RUSTFLAGS").unwrap_or_default()),
        (
            "CARGO_ENCODED_RUSTFLAGS",
            std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default(),
        ),
        ("config", format!("{args:?}")),
    ];
    for (key, value) in entries {
        // Escaping also prevents multiline metadata from looking like sample rows.
        writeln!(text, "# {key}: {value:?}").unwrap();
    }
    text.push_str("case\tsample\titerations\telapsed_ns\tns_per_iteration\n");
    text
}

pub fn run(cases: Vec<Case<'_>>) -> Result<()> {
    ensure!(
        !cfg!(debug_assertions),
        "use cargo bench: debug builds are not comparable"
    );
    let args = Args::parse();
    let cases: Vec<_> = cases
        .into_iter()
        .filter(|case| case.name.contains(&args.filter))
        .collect();
    ensure!(!cases.is_empty(), "no benchmark matches {:?}", args.filter);
    if args.list {
        for case in cases {
            println!("{}", case.name);
        }
        return Ok(());
    }
    let previous = args
        .baseline
        .as_ref()
        .map(|name| read_baseline(&baseline_path(&args, name)?))
        .transpose()?;
    if let Some(previous) = &previous {
        for case in &cases {
            ensure!(
                previous.contains_key(case.name),
                "baseline has no case {} (use --filter or a complete baseline)",
                case.name
            );
        }
    }
    let destination = args
        .save_baseline
        .as_ref()
        .map(|name| baseline_path(&args, name))
        .transpose()?;
    if let Some(path) = &destination {
        ensure!(
            !path.exists(),
            "{} already exists; choose a new baseline name",
            path.display()
        );
    }
    let mut report = metadata(&args);
    println!(
        "{:28} {:>12} {:>10} {:>12}",
        "case", "median (ms)", "CV (%)", "change (%)"
    );
    for case in cases {
        eprintln!("measuring {} ...", case.name);
        let warmup = Instant::now();
        loop {
            black_box((case.iteration)());
            if warmup.elapsed() >= Duration::from_millis(args.warmup_ms) {
                break;
            }
        }
        let mut values = Vec::new();
        for sample in 0..args.samples {
            let wall_start = Instant::now();
            let mut elapsed = Duration::ZERO;
            let mut iterations = 0_u64;
            loop {
                elapsed += (case.iteration)();
                iterations += 1;
                if wall_start.elapsed() >= Duration::from_millis(args.sample_ms) {
                    break;
                }
            }
            let per_iteration = elapsed.as_nanos() as f64 / iterations as f64;
            ensure!(
                per_iteration > 0.0,
                "timer resolution too low for {}",
                case.name
            );
            values.push(per_iteration);
            writeln!(
                report,
                "{}\t{sample}\t{iterations}\t{}\t{per_iteration:.6}",
                case.name,
                elapsed.as_nanos()
            )?;
        }
        let middle = median(&values);
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        let variance = values
            .iter()
            .map(|value| (value - mean).powi(2))
            .sum::<f64>()
            / (values.len() - 1) as f64;
        let cv = variance.sqrt() / mean * 100.0;
        let change = previous
            .as_ref()
            .map(|old| format!("{:+.2}", (middle / median(&old[case.name]) - 1.0) * 100.0))
            .unwrap_or_else(|| "-".to_owned());
        println!(
            "{:28} {:12.4} {:10.2} {:>12}",
            case.name,
            middle / 1_000_000.0,
            cv,
            change
        );
    }
    if let Some(path) = destination {
        fs::create_dir_all(&args.output_dir)?;
        // create_new also protects an existing baseline if another process wrote it meanwhile.
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(mut file) => file.write_all(report.as_bytes())?,
            Err(error) => bail!("cannot save {}: {error}", path.display()),
        }
        println!("Saved {}", path.display());
    }
    Ok(())
}
