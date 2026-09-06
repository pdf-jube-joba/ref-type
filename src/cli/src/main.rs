use clap::Parser;
use std::{io::IsTerminal, path::PathBuf};

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// ファイルをパースして結果を標準出力に出す
    file: PathBuf,
    /// kernel の型検査・定義登録・評価ログを標準エラーへ木構造で表示する
    #[arg(long)]
    trace: bool,
}

mod printing;

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    init_tracing(args.trace)?;
    let err = run_file_mode(args.file)?;
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

fn elaborate_and_format(modules: Vec<front::syntax::Module>) -> (Vec<String>, Option<String>) {
    let mut global = front::elaborator::GlobalEnvironment::default();
    let mut output_lines = Vec::new();
    for module in modules {
        match global.add_new_module_to_root(&module) {
            Ok(()) => {}
            Err(err) => {
                let detail =
                    front::metavariables::format_elaboration_error(global.crate_env(), &err);
                push_outputs(&global, &mut output_lines);
                return (output_lines, Some(format!("Elaboration Error: {detail}")));
            }
        }
    }

    push_outputs(&global, &mut output_lines);
    (output_lines, None)
}

fn push_outputs(global: &front::elaborator::GlobalEnvironment, output_lines: &mut Vec<String>) {
    for output in global.outputs() {
        output_lines.push(printing::format_output(global.crate_env(), output));
    }
}

fn run_file_mode(path: PathBuf) -> anyhow::Result<Option<String>> {
    let loaded = front::module_loader::load_modules_from_root(&path);
    let (out, err_message) = match loaded {
        Ok(modules) => elaborate_and_format(modules),
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
