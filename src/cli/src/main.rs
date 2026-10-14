mod progress;
mod resources;
#[cfg(target_os = "linux")]
mod supervisor;

use anyhow::Context;
use clap::Parser;
use std::{cell::RefCell, io::IsTerminal, path::PathBuf, time::Duration};

thread_local! {
    static PROGRESS: RefCell<Vec<sema::ModuleProgress>> = const { RefCell::new(Vec::new()) };
}

#[derive(Parser, Debug, Clone, serde::Serialize, serde::Deserialize)]
#[command(author, version, about)]
struct Args {
    /// パッケージ・workspace のディレクトリ、または .ref ファイル
    path: PathBuf,
    /// 検査プロセスの仮想メモリ上限 MiB（Linux の既定3072、0は既存の上限を維持）
    #[arg(long)]
    memory_mib: Option<u64>,
    /// 大きな検査範囲を分割するまでの秒数（末端の検査には適用しない）
    #[arg(long, default_value_t = 180, value_parser = clap::value_parser!(u64).range(1..))]
    batch_seconds: u64,
    #[arg(long, hide = true)]
    worker: Option<PathBuf>,
    /// 指定した module・子 module と、その参照先だけを検証する（例: std.Data.Nat）
    #[arg(long, conflicts_with = "parse_only")]
    module: Option<String>,
    /// 指定 module 自身と参照先を検証し、無関係な子 module を対象に含めない
    #[arg(long, requires = "module")]
    module_only: bool,
    /// ソースにある module の検査用パスを一行ずつ表示する
    #[arg(long, conflicts_with_all = ["module", "parse_only"])]
    list_modules: bool,
    /// kernel の型検査・定義登録・評価ログを標準エラーへ木構造で表示する
    #[arg(long)]
    trace: bool,
    /// 処理後に raw / kernel の構文ノード数を標準エラーへ表示する
    #[arg(long, conflicts_with = "parse_only")]
    stats: bool,
    /// 構文解析と module 読み込みだけを行う
    #[arg(long)]
    parse_only: bool,
    /// 永続キャッシュを使わず source から検証する
    #[arg(long)]
    no_cache: bool,
    /// キャッシュを再利用せず全体を検証し、検証済みの結果を保存する
    #[arg(long, conflicts_with = "parse_only")]
    full_check: bool,
    /// 入力 package・workspace の member を再検証し、外部依存のキャッシュを再利用する
    #[arg(long, conflicts_with_all = ["parse_only", "full_check", "no_cache", "trace", "stats"])]
    full_check_local: bool,
    /// 進捗バーと module ごとの所要時間を表示しない
    #[arg(long)]
    no_progress: bool,
    /// 詳細ログをリダイレクトしたまま、進捗バーを制御端末 (/dev/tty) に表示する
    #[arg(long, conflicts_with_all = ["no_progress", "parse_only"])]
    progress_tty: bool,
    /// キャッシュ保存先の中身を削除してから処理する
    #[arg(long)]
    clear_cache: bool,
    /// チェック済み semantic result の保存先（既定: workspace または入力先の refcache/）
    #[arg(long)]
    cache_dir: Option<PathBuf>,
    /// ディスクキャッシュの容量上限 MiB（利用中の成果物は保護する）
    #[arg(long, default_value_t = 8192)]
    cache_budget_mib: u64,
    /// parse・チェック・キャッシュ再利用の件数を表示する
    #[arg(long)]
    cache_stats: bool,
    /// package途中のcheckpoint保存間隔（秒、既定30）。module完了時に保存する
    #[arg(long)]
    checkpoint_seconds: Option<u64>,
    /// 簡潔な診断（compact）か制約を含む詳細診断（detailed）を選ぶ
    #[arg(long, value_enum)]
    diagnostics: Option<DiagnosticMode>,
}

#[derive(clap::ValueEnum, Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
enum DiagnosticMode {
    Compact,
    Detailed,
}

fn main() -> anyhow::Result<()> {
    let timing = sema::timing::Session::start(true);
    let args = Args::parse();
    #[cfg(target_os = "linux")]
    let args = supervisor::worker_arguments(args)?;
    resources::limit_memory(args.memory_mib)?;
    let timing = if args.no_progress || args.parse_only {
        drop(timing);
        sema::timing::Session::start(false)
    } else {
        timing
    };
    let cost_session = sema::timing::costs::Session::start();
    init_tracing(args.trace)?;
    let automatic_progress = !args.no_progress
        && !args.parse_only
        && !args.trace
        && std::io::stderr().is_terminal()
        && std::env::var_os("RUST_LOG").is_none()
        && !std::env::vars_os()
            .any(|(name, _)| name.to_string_lossy().starts_with("REF_TYPE_PROFILE_"));
    let live = args.worker.is_none() && (args.progress_tty || automatic_progress);
    let progress_output: Box<dyn std::io::Write + Send> = if args.progress_tty {
        Box::new(
            std::fs::OpenOptions::new()
                .write(true)
                .open("/dev/tty")
                .context("--progress-tty requires a controlling terminal (/dev/tty)")?,
        )
    } else {
        Box::new(std::io::stderr())
    };
    let mut display = progress::Display::new(live, progress_output);
    #[cfg(target_os = "linux")]
    let supervised = args.worker.is_none()
        && !args.parse_only
        && !args.list_modules
        && !args.path.extension().is_some_and(|ext| ext == "ref");
    #[cfg(target_os = "linux")]
    let result = if supervised {
        supervisor::run(&args, &mut display)
    } else {
        run_path(&args, &mut display)
    };
    #[cfg(not(target_os = "linux"))]
    let result = run_path(&args, &mut display);
    display.finish(
        result
            .as_ref()
            .is_ok_and(|status| *status == std::process::ExitCode::SUCCESS),
    );
    if let Some(measurements) = timing.measurements() {
        let mut modules = Duration::ZERO;
        PROGRESS.with_borrow_mut(|events| {
            for progress in events.drain(..) {
                let elapsed = measurements
                    .modules
                    .get(&progress.path)
                    .copied()
                    .unwrap_or(progress.elapsed);
                modules += elapsed;
                let action = match progress.action {
                    sema::ProgressAction::Check => "check",
                    sema::ProgressAction::Skip => "skip",
                };
                #[cfg(target_os = "linux")]
                if args.worker.is_some() {
                    supervisor::send_timing(sema::ModuleProgress {
                        elapsed,
                        ..progress
                    });
                    continue;
                }
                if !live || args.progress_tty {
                    eprintln!(
                        "{action} {} ({:.9}s)",
                        progress.path.join("."),
                        elapsed.as_secs_f64()
                    );
                }
            }
        });
        let measurements = timing.finish().expect("CLI owns the timing session");
        if args.worker.is_none() {
            eprintln!(
                "shared ({:.9}s)",
                measurements.total.saturating_sub(modules).as_secs_f64()
            );
            eprintln!("total ({:.9}s)", measurements.total.as_secs_f64());
        }
    }
    drop(cost_session);
    #[cfg(target_os = "linux")]
    if supervised && supervisor::interrupted() {
        std::process::exit(130);
    }
    let status = result?;
    if status != std::process::ExitCode::SUCCESS {
        std::process::exit(1);
    }
    Ok(())
}

fn init_tracing(show_typing_tree: bool) -> anyhow::Result<()> {
    use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

    let default_filter = if show_typing_tree {
        "ref_type=debug"
    } else {
        "ref_type=off"
    };
    let filter =
        EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new(default_filter));
    tracing_subscriber::registry()
        .with(filter)
        .with(
            tracing_tree::HierarchicalLayer::new(2)
                .with_writer(std::io::stderr)
                .with_ansi(std::io::stderr().is_terminal()),
        )
        .try_init()?;
    Ok(())
}

fn run_path(
    args: &Args,
    display: &mut progress::Display,
) -> anyhow::Result<std::process::ExitCode> {
    let cache_directory = match &args.cache_dir {
        Some(path) => path.clone(),
        None => sema::default_cache_directory(&args.path)?,
    };
    if args.clear_cache {
        clear_cache_directory(&cache_directory)?;
    }
    let mut database = if args.no_cache {
        sema::Database::new()
    } else {
        sema::Database::with_cache(cache_directory)
    };
    database.set_cache_budget(args.cache_budget_mib.saturating_mul(1024 * 1024));
    #[cfg(target_os = "linux")]
    let snapshot = if let Some(directory) = &args.worker {
        Some(supervisor::read_snapshot(directory)?)
    } else {
        None
    };
    #[cfg(not(target_os = "linux"))]
    let snapshot = None;
    let snapshot = match snapshot
        .map(Ok)
        .unwrap_or_else(|| database.read_snapshot(&args.path, args.full_check_local))
    {
        Ok(snapshot) => snapshot,
        Err(error) => {
            display.finish(false);
            let message = format!("Module Load Error: {error}");
            eprintln!("{message}");
            return Ok(std::process::ExitCode::FAILURE);
        }
    };
    if args.list_modules {
        return match database.module_paths(&snapshot) {
            Ok(paths) => {
                for path in paths {
                    println!("{}", path.join("."));
                }
                Ok(std::process::ExitCode::SUCCESS)
            }
            Err(diagnostics) => {
                for diagnostic in diagnostics {
                    eprintln!("{}", diagnostic.render(&snapshot));
                }
                Ok(std::process::ExitCode::FAILURE)
            }
        };
    }
    let messages = if args.parse_only {
        database
            .parse_project(&snapshot)
            .err()
            .unwrap_or_default()
            .iter()
            .map(|diagnostic| diagnostic.render(&snapshot))
            .collect::<Vec<_>>()
    } else {
        let options = sema::CheckOptions {
            force: args.trace || args.no_cache || args.full_check,
            force_local: args.full_check_local,
            progress: (!args.no_progress).then_some(show_progress),
            progress_events: display.enabled().then_some(progress::receive),
            collect_statistics: args.stats,
            module_only: args.module_only,
            checkpoint_interval: args.checkpoint_seconds.map(Duration::from_secs),
            diagnostics: match args.diagnostics {
                Some(DiagnosticMode::Compact) => sema::DiagnosticMode::Compact,
                Some(DiagnosticMode::Detailed) => sema::DiagnosticMode::Detailed,
                None => sema::DiagnosticMode::default(),
            },
            ..sema::CheckOptions::default()
        };
        #[cfg(target_os = "linux")]
        let options = if args.worker.is_some() {
            sema::CheckOptions {
                progress_events: Some(supervisor::send_event),
                ..options
            }
        } else {
            options
        };
        let result = match &args.module {
            Some(name) => {
                let path = name.split('.').map(str::to_owned).collect::<Vec<_>>();
                let result = database.module_with_options(&snapshot, &path, &options);
                if result.is_success() && !result.modules.iter().any(|module| module.path == path) {
                    display.finish(false);
                    let message = format!("Module Selection Error: module '{name}' was not found");
                    eprintln!("{message}");
                    return Ok(std::process::ExitCode::FAILURE);
                }
                result
            }
            None => database.check_with_options(&snapshot, &options),
        };
        display.finish(result.is_success());
        for output in result.outputs() {
            #[cfg(target_os = "linux")]
            if args.worker.is_some() {
                supervisor::send_output(output.clone());
                continue;
            }
            println!("{}", output.text);
        }
        for statistic in database.verification_statistics() {
            eprintln!("{statistic}");
        }
        result
            .all_diagnostics()
            .map(|diagnostic| diagnostic.render(&snapshot))
            .collect()
    };
    if args.cache_stats {
        eprintln!("queries: {:?}", database.stats());
        eprintln!("cache: {:?}", database.cache_store_stats());
        eprintln!("memory cache: {:?}", database.memory_cache_stats());
    }
    let error = (!messages.is_empty()).then(|| messages.join("\n"));
    if let Some(message) = &error {
        if std::io::stderr().is_terminal() {
            eprintln!("\x1b[31m{message}\x1b[0m");
        } else {
            eprintln!("{message}");
        }
    }
    Ok(if error.is_some() {
        std::process::ExitCode::FAILURE
    } else {
        std::process::ExitCode::SUCCESS
    })
}

fn show_progress(progress: &sema::ModuleProgress) {
    PROGRESS.with_borrow_mut(|events| events.push(progress.clone()));
}

fn clear_cache_directory(directory: &std::path::Path) -> anyhow::Result<()> {
    let entries = match std::fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    for entry in entries {
        let path = entry?.path();
        if path.is_dir() {
            std::fs::remove_dir_all(path)?;
        } else {
            std::fs::remove_file(path)?;
        }
    }
    Ok(())
}
