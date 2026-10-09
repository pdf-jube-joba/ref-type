use axum::{
    Json, Router,
    extract::DefaultBodyLimit,
    http::StatusCode,
    response::Html,
    routing::{get, post},
};
use clap::Parser;
use sema::{Database, SourceSnapshot};
use serde::{Deserialize, Serialize};
use std::{net::Ipv4Addr, time::Instant};

#[derive(Parser)]
#[command(about = "Ref Type の Web playground")]
struct Args {
    /// 待ち受けポート（デフォルトは 3000、0 は空きポートを自動選択）
    #[arg(long, default_value_t = 3000)]
    port: u16,
}

#[derive(Deserialize)]
struct CheckRequest {
    source: String,
}

#[derive(Debug, Serialize)]
struct CheckResponse {
    success: bool,
    outputs: Vec<String>,
    diagnostics: Vec<String>,
    elapsed_ms: u128,
}

fn check_source(source: String) -> CheckResponse {
    let started = Instant::now();
    let mut snapshot = SourceSnapshot::new("/playground/root.ref");
    snapshot.insert("/playground/root.ref", source);
    let result = Database::new().check(&snapshot);
    CheckResponse {
        success: result.is_success(),
        outputs: result.outputs().map(|output| output.text.clone()).collect(),
        diagnostics: result
            .all_diagnostics()
            .map(|diagnostic| diagnostic.render(&snapshot))
            .collect(),
        elapsed_ms: started.elapsed().as_millis(),
    }
}

async fn check(
    Json(request): Json<CheckRequest>,
) -> Result<Json<CheckResponse>, (StatusCode, String)> {
    tokio::task::spawn_blocking(move || check_source(request.source))
        .await
        .map(Json)
        .map_err(|error| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("検証を完了できませんでした: {error}"),
            )
        })
}

fn app() -> Router {
    Router::new()
        .route("/", get(async || Html(include_str!("../web/index.html"))))
        .route(
            "/app.js",
            get(async || {
                (
                    [("content-type", "text/javascript; charset=utf-8")],
                    include_str!("../web/app.js"),
                )
            }),
        )
        .route(
            "/style.css",
            get(async || {
                (
                    [("content-type", "text/css; charset=utf-8")],
                    include_str!("../web/style.css"),
                )
            }),
        )
        .route("/api/check", post(check))
        .layer(DefaultBodyLimit::max(256 * 1024))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let listener = tokio::net::TcpListener::bind((Ipv4Addr::LOCALHOST, args.port)).await?;
    println!("Ref Type playground: http://{}/", listener.local_addr()?);
    println!("終了するには Ctrl+C を押してください。");
    axum::serve(listener, app())
        .with_graceful_shutdown(async {
            let _ = tokio::signal::ctrl_c().await;
        })
        .await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checks_definitions_and_returns_evaluation_output() {
        let response = check_source(
            r"\module Playground {
  \definition identity: \forall (A: \Prop) -> A -> A :=
    \fun (A: \Prop) => \fun (x: A) => x;
  \infer identity;
  \eval identity;
}"
            .into(),
        );
        assert!(response.success, "{:?}", response.diagnostics);
        assert_eq!(response.outputs.len(), 2);
        assert!(response.outputs.iter().all(|output| !output.is_empty()));
    }

    #[test]
    fn reports_source_locations_for_errors_and_recovers_on_next_check() {
        let response = check_source(
            r"\module Playground {
  \definition wrong: \Prop := missing;
}"
            .into(),
        );
        assert!(!response.success);
        assert!(!response.diagnostics.is_empty());
        assert!(response.diagnostics.join("\n").contains("missing"));
        assert!(response.diagnostics.join("\n").contains("root.ref"));
        let valid = check_source(
            r"\module Playground {
  \definition P: \Prop := \forall (A: \Prop) -> A -> A;
}"
            .into(),
        );
        assert!(valid.success, "{:?}", valid.diagnostics);
    }
}
