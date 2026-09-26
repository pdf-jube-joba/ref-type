use clap::Parser;
use std::{io::IsTerminal, path::PathBuf};

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
    /// チェック済み semantic result の保存先（既定: 入力ディレクトリの refcache/）
    #[arg(long)]
    cache_dir: Option<PathBuf>,
    /// parse・チェック・キャッシュ再利用の件数を表示する
    #[arg(long)]
    cache_stats: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    init_tracing(args.trace)?;
    let err = run_path(&args)?;
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
    let snapshot = match sema::SourceSnapshot::read(&args.path) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            let message = format!("Module Load Error: {error}");
            eprintln!("{message}");
            return Ok(Some(message));
        }
    };
    let mut database = if args.no_cache {
        sema::Database::new()
    } else {
        let directory = args.cache_dir.clone().unwrap_or_else(|| {
            let entry = snapshot.entry();
            let root = if entry
                .extension()
                .is_some_and(|extension| extension == "ref")
            {
                entry.parent().expect("source file has a parent directory")
            } else {
                entry
            };
            root.join("refcache")
        });
        sema::Database::with_cache(directory)
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
                collect_statistics: args.stats,
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
