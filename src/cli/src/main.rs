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
    /// front 側の構文への変換だけを行う
    #[arg(long)]
    parse_only: bool,
}

mod printing;

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    init_tracing(args.trace)?;
    let err = run_path(args.path, args.stats, args.parse_only)?;
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

fn elaborate_and_format(
    modules: Vec<front::syntax::Module>,
    stats: bool,
) -> (Vec<String>, Option<String>) {
    let mut global = front::elaborator::GlobalEnvironment::default();
    let mut output_lines = Vec::new();
    let result = global.add_modules_to_root(&modules);
    if stats {
        eprintln!("raw nodes: {:?}", global.arena().node_counts());
        eprintln!("raw caches: {:?}", global.crate_env().cache_counts());
        eprintln!(
            "kernel nodes: {:?}",
            global.kernel_env().arena().node_counts()
        );
        eprintln!("kernel caches: {:?}", global.kernel_env().cache_counts());
        eprintln!(
            "kernel declaration nodes: {}",
            global.kernel_env().declaration_node_count()
        );
    }
    if let Err(err) = result {
        let detail = front::metavariables::format_elaboration_error(global.crate_env(), &err);
        push_outputs(&global, &mut output_lines);
        return (output_lines, Some(format!("Elaboration Error: {detail}")));
    }

    push_outputs(&global, &mut output_lines);
    (output_lines, None)
}

fn push_outputs(global: &front::elaborator::GlobalEnvironment, output_lines: &mut Vec<String>) {
    for output in global.outputs() {
        output_lines.push(printing::format_output(global.crate_env(), output));
    }
}

fn run_path(path: PathBuf, stats: bool, parse_only: bool) -> anyhow::Result<Option<String>> {
    let loaded = if path.is_dir() {
        front::package_loader::load_package(&path).map(|graph| graph.modules)
    } else {
        front::module_loader::load_modules_from_root(&path)
    };
    let (out, err_message) = match loaded {
        Ok(_) if parse_only => (Vec::new(), None),
        Ok(modules) => elaborate_and_format(modules, stats),
        Err(error) => (Vec::new(), Some(format!("Module Load Error: {error}"))),
    };
    for entry in out {
        println!("{entry}");
    }
    if let Some(msg) = &err_message {
        if std::io::stderr().is_terminal() {
            eprintln!("\x1b[31m{msg}\x1b[0m");
        } else {
            eprintln!("{msg}");
        }
    }
    Ok(err_message)
}
