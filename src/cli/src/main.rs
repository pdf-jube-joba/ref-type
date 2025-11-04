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
#[derive(Serialize)]
struct Resp {
    result: String,
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
fn parse_and_format(src: String) -> (String, bool) {
    let parsed = front::parse::str_parse_modules(&src);
    match parsed {
        Ok(modules) => {
            let mut global = front::resolver::GlobalEnvironment::default();
            let mut output = String::new();
            let mut flag = false;
            for module in modules {
                match global.new_module(&module) {
                    Ok(_) => {}
                    Err(err) => {
                        output.push_str(&format!("Error: {}\n", err));
                        flag = true;
                    }
                }
            }
            output.push_str("--- LOG ---\n");
            for log in global.logs() {
                match log {
                    either::Either::Left(der) => {
                        output.push_str(&format!("{der}"));
                    }
                    either::Either::Right(mes) => {
                        output.push_str(mes);
                    }
                }
            }
            (output, flag)
        }
        Err(e) => (format!("Parse Error: {}\n", e), true),
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
    println!("{out}");
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
