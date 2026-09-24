use clap::Parser;
use std::{io::IsTerminal, path::PathBuf};

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// package のディレクトリ、ref.toml、または単独のルート .ref ファイル
    file: PathBuf,
    /// kernel の型検査・定義登録・評価ログを標準エラーへ木構造で表示する
    #[arg(long)]
    trace: bool,
    /// 処理後に raw / kernel の構文ノード数を標準エラーへ表示する
    #[arg(long, conflicts_with = "parse_only")]
    stats: bool,
    /// 読み込む source の構文解析だけを行う
    #[arg(long)]
    parse_only: bool,
    /// LSP の標準入出力サーバーを起動する
    #[arg(long, conflicts_with_all = ["parse_only", "stats", "mcp"])]
    lsp: bool,
    /// MCP の標準入出力サーバーを起動する
    #[arg(long, conflicts_with_all = ["parse_only", "stats", "lsp"])]
    mcp: bool,
}

mod protocol;

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    init_tracing(args.trace)?;
    if args.lsp || args.mcp {
        return protocol::serve(args.file, args.mcp);
    }
    let err = run_file_mode(args.file, args.stats, args.parse_only)?;
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

fn run_file_mode(path: PathBuf, stats: bool, parse_only: bool) -> anyhow::Result<Option<String>> {
    let mut host = sema::AnalysisHost::new(path)?;
    host.refresh_disk();
    let snapshot = host.snapshot();
    let diagnostics = if parse_only {
        snapshot.parse_diagnostics().diagnostics
    } else {
        let result = snapshot.check();
        for entry in &result.outputs {
            println!("{entry}");
        }
        if stats {
            for statistic in &result.statistics {
                eprintln!("{statistic}");
            }
        }
        result.diagnostics.clone()
    };
    let err_message = (!diagnostics.is_empty()).then(|| {
        diagnostics
            .iter()
            .map(|diagnostic| snapshot.render_diagnostic(diagnostic))
            .collect::<Vec<_>>()
            .join("\n\n")
    });
    if let Some(msg) = &err_message {
        if std::io::stderr().is_terminal() {
            eprintln!("\x1b[31m{msg}\x1b[0m");
        } else {
            eprintln!("{msg}");
        }
    }
    Ok(err_message)
}
