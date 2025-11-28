use axum::{
    Json, Router,
    response::Html,
    routing::{get, post},
};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, net::SocketAddr, path::PathBuf};
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
    File { file: PathBuf },

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
pub enum TreeNode {
    Success(String),
    ErrorPropagate(String),
    ErrorCause(String),
    Pending(String),
}

impl Display for TreeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TreeNode::Success(s) => write!(f, "\x1b[90m{}\x1b[0m", s),
            TreeNode::ErrorPropagate(s) => write!(f, "\x1b[31m{}\x1b[0m", s),
            TreeNode::ErrorCause(s) => write!(f, "\x1b[31;1m{}\x1b[0m", s),
            TreeNode::Pending(s) => write!(f, "\x1b[33m{}\x1b[0m", s),
        }
    }
}

#[derive(Serialize, Debug)]
pub struct StringTree {
    pub head: TreeNode,
    pub children: Vec<StringTree>,
}

#[derive(Serialize, Debug)]
pub enum Log {
    Derivation(StringTree),
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
        Cmd::File { file } => {
            let err = run_file_mode(file).await?;
            if err.is_some() {
                std::process::exit(1);
            }
            Ok(())
        }
        Cmd::Serve { port } => {
            run_serve_mode(port).await?;
            Ok(())
        }
    }
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

    let mut global = front::elaborator::GlobalEnvironment::default();
    let mut logs: Vec<Log> = vec![];
    for module in modules {
        match global.add_new_module_to_root(&module) {
            Ok(_) => {}
            Err(err) => {
                let msg = format!("Elaboration Error: {}\n", err);
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
        logs.push(printing::log_record_to_log(entry));
    }
}

// ---- ファイルモード ---------------------------------------------
async fn run_file_mode(path: PathBuf) -> anyhow::Result<Option<String>> {
    // 軽い読み込みなら同期I/OでもOK
    // let txt = std::fs::read_to_string(&path)?;

    // パースが重くなる可能性があるなら spawn_blocking で逃がす
    let txt = tokio::task::spawn_blocking(move || std::fs::read_to_string(path)).await??;

    // ここで重い処理をする場合も spawn_blocking 推奨
    let (out, err_message) = tokio::task::spawn_blocking(move || parse_and_format(txt)).await?;
    for entry in out {
        match entry {
            Log::Derivation(der) => {
                fn print_tree(tree: &StringTree, indent: usize) {
                    let indent_str = "  ".repeat(indent);
                    println!("{}{}", indent_str, tree.head);
                    for child in &tree.children {
                        print_tree(child, indent + 1);
                    }
                }
                print_tree(&der, 0);
            }
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
