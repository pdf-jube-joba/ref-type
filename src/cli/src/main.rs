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

#[derive(Serialize, Debug)]
pub enum Node {
    Success(String),
    ErrorPropagate(String),
    ErrorCause(String),
    Pending(String),
}

impl From<kernel::printing::Node> for Node {
    fn from(value: kernel::printing::Node) -> Self {
        match value {
            kernel::printing::Node::Success(s) => Node::Success(s),
            kernel::printing::Node::ErrorPropagate(s) => Node::ErrorPropagate(s),
            kernel::printing::Node::ErrorCause(s) => Node::ErrorCause(s),
            kernel::printing::Node::Pending(s) => Node::Pending(s),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Success(s) => write!(f, "\x1b[32m{}\x1b[0m", s),
            Node::ErrorPropagate(s) => write!(f, "\x1b[31m{}\x1b[0m", s),
            Node::ErrorCause(s) => write!(f, "\x1b[31;1m{}\x1b[0m", s),
            Node::Pending(s) => write!(f, "\x1b[33m{}\x1b[0m", s),
        }
    }
}

#[derive(Serialize, Debug)]
pub struct StringTree {
    pub head: Node,
    pub children: Vec<StringTree>,
}

impl From<kernel::printing::StringTree> for StringTree {
    fn from(value: kernel::printing::StringTree) -> Self {
        StringTree {
            head: value.head.into(),
            children: value
                .children
                .into_iter()
                .map(|child| child.into())
                .collect(),
        }
    }
}

#[derive(Serialize, Debug)]
pub enum Log {
    Derivation(StringTree),
    Message(String),
}

#[derive(Serialize)]
struct Resp {
    result: Vec<Log>,
}

static INDEX_HTML: &str = include_str!("../index.html");

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    match args.cmd {
        Cmd::File { file } => {
            let flag = run_file_mode(file).await?;
            if flag {
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
fn parse_and_format(src: String) -> (Vec<Log>, bool) {
    let parsed = front::parse::str_parse_modules(&src);
    match parsed {
        Ok(modules) => {
            let mut global = front::elaborator::GlobalEnvironment::default();
            let mut logs: Vec<Log> = vec![];
            let mut flag = false;
            for module in modules {
                match global.new_module(&module) {
                    Ok(_) => {}
                    Err(err) => match err {
                        front::elaborator::ErrorKind::Msg(msg) => {
                            logs.push(Log::Message(format!("Error: {}\n", msg)));
                            flag = true;
                        }
                        front::elaborator::ErrorKind::DerivationFail(derivation_fail) => {
                            logs.push(Log::Derivation(
                                kernel::printing::map_derivation_fail(&derivation_fail).into(),
                            ));
                            flag = true;
                        }
                    },
                }
            }

            // append internal logs
            for entry in global.logs() {
                match entry {
                    either::Either::Left(der) => {
                        logs.push(Log::Derivation(
                            kernel::printing::map_derivation_success(der).into(),
                        ));
                    }
                    either::Either::Right(mes) => {
                        logs.push(Log::Message(mes.clone()));
                    }
                }
            }

            (logs, flag)
        }
        Err(e) => (vec![Log::Message(format!("Parse Error: {}\n", e))], true),
    }
}

// ---- ファイルモード ---------------------------------------------
async fn run_file_mode(path: PathBuf) -> anyhow::Result<bool> {
    // 軽い読み込みなら同期I/OでもOK
    // let txt = std::fs::read_to_string(&path)?;

    // パースが重くなる可能性があるなら spawn_blocking で逃がす
    let txt = tokio::task::spawn_blocking(move || std::fs::read_to_string(path)).await??;

    // ここで重い処理をする場合も spawn_blocking 推奨
    let (out, flag) = tokio::task::spawn_blocking(move || parse_and_format(txt)).await?;
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
    Ok(flag)
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
    let (out, _flag) = parse_and_format(content);
    Json(Resp { result: out })
}
