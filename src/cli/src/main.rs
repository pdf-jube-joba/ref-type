use axum::{
    Json, Router,
    response::Html,
    routing::{get, post},
};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use std::{net::SocketAddr, path::PathBuf};
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// ファイルをパースして結果を標準出力に出す
    File {
        file: PathBuf,
        /// typing の span/event を木構造で表示する
        #[arg(long)]
        trace: bool,
    },

    /// ローカルサーバを起動して / と /run を提供する
    Serve {
        #[arg(long, default_value_t = 8080)]
        port: u16,
    },
}

#[derive(Deserialize)]
struct Req {
    text: String,
}

mod printing;

#[derive(Serialize, Debug)]
pub enum Log {
    Message(String),
}

#[derive(Serialize)]
struct Resp {
    result: Vec<Log>,
    error: Option<String>,
}

static INDEX_HTML: &str = include_str!("../index.html");

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    match args.cmd {
        Cmd::File { file, trace } => {
            init_tracing(trace)?;
            let err = run_file_mode(file).await?;
            if err.is_some() {
                std::process::exit(1);
            }
            Ok(())
        }
        Cmd::Serve { port } => {
            init_tracing(false)?;
            run_serve_mode(port).await?;
            Ok(())
        }
    }
}

fn init_tracing(show_typing_tree: bool) -> anyhow::Result<()> {
    use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

    let default_filter = if show_typing_tree {
        "ref_type::typing=debug"
    } else {
        "ref_type::typing=off"
    };
    let filter =
        EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new(default_filter));
    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_tree::HierarchicalLayer::new(2))
        .try_init()?;
    Ok(())
}

// ---- 共通処理 ---------------------------------------------
fn parse_and_format(src: String) -> (Vec<Log>, Option<String>) {
    let parsed = front::parse::str_parse_modules(&src);
    let modules = match parsed {
        Ok(modules) => modules,
        Err(e) => {
            let msg = format!("Parse Error: {}\n", e);
            return (vec![Log::Message(msg.clone())], Some(msg));
        }
    };

    elaborate_and_format(modules)
}

fn elaborate_and_format(modules: Vec<front::syntax::Module>) -> (Vec<Log>, Option<String>) {
    let mut global = front::elaborator::GlobalEnvironment::default();
    let mut logs: Vec<Log> = vec![];
    for module in modules {
        match global.add_new_module_to_root(&module) {
            Ok(_) => {}
            Err(err) => {
                let detail = match &err {
                    front::metavariables::ElaborationError::AmbiguousImplicit(_)
                    | front::metavariables::ElaborationError::UnsolvedGoals(_) => err.to_string(),
                    _ => front::metavariables::format_elaboration_error(global.crate_env(), &err),
                };
                let msg = format!("Elaboration Error: {detail}\n");
                logs.push(Log::Message(msg.clone()));
                push_internal_logs(&global, &mut logs);
                return (logs, Some(msg));
            }
        }
    }

    push_internal_logs(&global, &mut logs);
    (logs, None)
}

fn push_internal_logs(global: &front::elaborator::GlobalEnvironment, logs: &mut Vec<Log>) {
    for entry in global.logger().records() {
        logs.push(printing::log_record_to_log(global.crate_env(), entry));
    }
}

// ---- ファイルモード ---------------------------------------------
async fn run_file_mode(path: PathBuf) -> anyhow::Result<Option<String>> {
    let loaded =
        tokio::task::spawn_blocking(move || front::module_loader::load_modules_from_root(&path))
            .await?;
    let (out, err_message) = match loaded {
        Ok(modules) => tokio::task::spawn_blocking(move || elaborate_and_format(modules)).await?,
        Err(error) => {
            let message = format!("Module Load Error: {}\n", error);
            (vec![Log::Message(message.clone())], Some(message))
        }
    };
    for entry in out {
        match entry {
            Log::Message(mes) => {
                println!("{}", mes);
            }
        }
    }
    if let Some(msg) = &err_message {
        let trimmed = msg.trim_end_matches('\n');
        eprintln!("\x1b[31m{}\x1b[0m", trimmed);
    }
    Ok(err_message)
}

// ---- サーブモード ------------------------------------------------
async fn run_serve_mode(port: u16) -> anyhow::Result<()> {
    let app = Router::new()
        .route("/", get(|| async { Html(INDEX_HTML) }))
        .route("/run", post(run_api));

    let addr = SocketAddr::from(([127, 0, 0, 1], port));
    eprintln!("Serving on http://{addr}");
    axum::serve(TcpListener::bind(addr).await?, app).await?;
    Ok(())
}

async fn run_api(Json(req): Json<Req>) -> Json<Resp> {
    // 重いなら spawn_blocking(move || heavy(req.text)) を使う
    let content = req.text;
    let (out, err) = parse_and_format(content);
    Json(Resp {
        result: out,
        error: err,
    })
}
