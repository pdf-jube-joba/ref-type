use clap::Parser;
use std::{cell::RefCell, io::IsTerminal, path::PathBuf, time::Duration};

thread_local! {
    static PROGRESS: RefCell<Vec<sema::ModuleProgress>> = const { RefCell::new(Vec::new()) };
}

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// パッケージのディレクトリ、または .ref ファイル
    path: PathBuf,
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
    /// 指定ライブラリだけを再検証し、依存先は自身の変更だけを確認してキャッシュを再利用する
    #[arg(long, conflicts_with_all = ["parse_only", "full_check", "no_cache", "trace", "stats"])]
    full_check_local: bool,
    /// module ごとの check / skip と所要秒数を表示しない
    #[arg(long)]
    no_progress: bool,
    /// キャッシュ保存先の中身を削除してから処理する
    #[arg(long)]
    clear_cache: bool,
    /// チェック済み semantic result の保存先（既定: 入力ディレクトリの refcache/）
    #[arg(long)]
    cache_dir: Option<PathBuf>,
    /// parse・チェック・キャッシュ再利用の件数を表示する
    #[arg(long)]
    cache_stats: bool,
    /// 簡潔な診断（compact）か制約を含む詳細診断（detailed）を選ぶ
    #[arg(long, value_enum)]
    diagnostics: Option<DiagnosticMode>,
}

#[derive(clap::ValueEnum, Clone, Copy, Debug)]
enum DiagnosticMode {
    Compact,
    Detailed,
}

fn main() -> anyhow::Result<()> {
    let timing = sema::timing::Session::start(true);
    let args = Args::parse();
    let timing = if args.no_progress || args.parse_only {
        drop(timing);
        sema::timing::Session::start(false)
    } else {
        timing
    };
    let cost_session = sema::timing::costs::Session::start();
    init_tracing(args.trace)?;
    let result = run_path(&args);
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
                eprintln!(
                    "{action} {} ({:.9}s)",
                    progress.path.join("."),
                    elapsed.as_secs_f64()
                );
            }
        });
        let measurements = timing.finish().expect("CLI owns the timing session");
        eprintln!(
            "shared ({:.9}s)",
            (measurements.total - modules).as_secs_f64()
        );
        eprintln!("total ({:.9}s)", measurements.total.as_secs_f64());
    }
    drop(cost_session);
    let err = result?;
    if err.is_some() {
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

fn run_path(args: &Args) -> anyhow::Result<Option<String>> {
    let cache_directory = args
        .cache_dir
        .clone()
        .unwrap_or_else(|| sema::SourceSnapshot::new(&args.path).default_cache_directory());
    if args.clear_cache {
        clear_cache_directory(&cache_directory)?;
    }
    let mut database = if args.no_cache {
        sema::Database::new()
    } else {
        sema::Database::with_cache(cache_directory)
    };
    let snapshot = match database.read_snapshot(&args.path, args.full_check_local) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            let message = format!("Module Load Error: {error}");
            eprintln!("{message}");
            return Ok(Some(message));
        }
    };
    let messages = if args.parse_only {
        database
            .parse_project(&snapshot)
            .err()
            .unwrap_or_default()
            .iter()
            .map(|diagnostic| diagnostic.render(&snapshot))
            .collect::<Vec<_>>()
    } else {
        let result = database.check_with_options(
            &snapshot,
            &sema::CheckOptions {
                force: args.trace || args.no_cache || args.full_check,
                force_local: args.full_check_local,
                progress: (!args.no_progress).then_some(show_progress),
                collect_statistics: args.stats,
                diagnostics: match args.diagnostics {
                    Some(DiagnosticMode::Compact) => sema::DiagnosticMode::Compact,
                    Some(DiagnosticMode::Detailed) => sema::DiagnosticMode::Detailed,
                    None => sema::DiagnosticMode::default(),
                },
                ..sema::CheckOptions::default()
            },
        );
        for output in result.outputs() {
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
    }
    let error = (!messages.is_empty()).then(|| messages.join("\n"));
    if let Some(message) = &error {
        if std::io::stderr().is_terminal() {
            eprintln!("\x1b[31m{message}\x1b[0m");
        } else {
            eprintln!("{message}");
        }
    }
    Ok(error)
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
