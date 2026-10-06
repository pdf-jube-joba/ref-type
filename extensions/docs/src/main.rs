mod catalog;
mod render;

use axum::{
    Router,
    extract::{Path, State},
    http::{HeaderValue, StatusCode},
    middleware,
    response::{Html, IntoResponse, Response},
    routing::get,
};
use catalog::Catalog;
use clap::Parser;
use std::{net::Ipv4Addr, path::PathBuf, sync::Arc};

#[derive(Parser)]
#[command(about = "Browse Ref Type library documentation locally")]
struct Args {
    /// Port to listen on; 0 selects a free port
    #[arg(long, default_value_t = 3030)]
    port: u16,
    /// Library directory (default: this checkout's libs/)
    #[arg(long, default_value_os_t = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../libs"))]
    libs: PathBuf,
}

fn app(catalog: Catalog) -> Router {
    Router::new()
        .route("/", get(async |State(c): State<Arc<Catalog>>| Html(render::directory(&c, 0))))
        .route("/dir/{id}", get(directory))
        .route("/file/{id}", get(file))
        .route("/source/{id}", get(source))
        .route("/search", get(async |State(c): State<Arc<Catalog>>| Html(render::search(&c))))
        .route("/style.css", get(async || ([("content-type", "text/css; charset=utf-8")], include_str!("../web/style.css"))))
        .route("/app.js", get(async || ([("content-type", "text/javascript; charset=utf-8")], include_str!("../web/app.js"))))
        .fallback(|| async { (StatusCode::NOT_FOUND, "Page not found. Open / to browse the library.") })
        .layer(middleware::map_response(|mut response: Response| async move {
            for (name, value) in [
                ("content-security-policy", "default-src 'none'; style-src 'self'; script-src 'self'; connect-src 'none'; img-src 'none'; base-uri 'none'; form-action 'self'; frame-ancestors 'none'"),
                ("x-content-type-options", "nosniff"),
                ("referrer-policy", "no-referrer"),
                ("cache-control", "no-store"),
            ] {
                response.headers_mut().insert(name, HeaderValue::from_static(value));
            }
            response
        }))
        .with_state(Arc::new(catalog))
}

async fn directory(State(c): State<Arc<Catalog>>, Path(id): Path<usize>) -> Response {
    if id < c.directories.len() {
        Html(render::directory(&c, id)).into_response()
    } else {
        StatusCode::NOT_FOUND.into_response()
    }
}
async fn file(State(c): State<Arc<Catalog>>, Path(id): Path<usize>) -> Response {
    if id < c.files.len() {
        Html(render::file(&c, id)).into_response()
    } else {
        StatusCode::NOT_FOUND.into_response()
    }
}
async fn source(State(c): State<Arc<Catalog>>, Path(id): Path<usize>) -> Response {
    if id < c.files.len() {
        Html(render::source(&c, id)).into_response()
    } else {
        StatusCode::NOT_FOUND.into_response()
    }
}

#[tokio::main]
async fn main() {
    if let Err(error) = run(Args::parse()).await {
        eprintln!("ref-docs: {error}");
        std::process::exit(1);
    }
}

async fn run(args: Args) -> Result<(), String> {
    let listener = tokio::net::TcpListener::bind((Ipv4Addr::LOCALHOST, args.port))
        .await
        .map_err(|error| {
            format!(
                "cannot listen on 127.0.0.1:{}: {error}. Try --port 0 or choose another port.",
                args.port
            )
        })?;
    let catalog = Catalog::read(&args.libs)?;
    let failures = catalog.files.iter().filter(|f| f.error.is_some()).count();
    println!(
        "Indexed {} source files ({} parse errors) from {}",
        catalog.files.len(),
        failures,
        args.libs.display()
    );
    println!(
        "Ref Type docs: http://{}/",
        listener.local_addr().map_err(|e| e.to_string())?
    );
    println!("Ctrl+C to stop. Restart to reload library changes.");
    axum::serve(listener, app(catalog))
        .with_graceful_shutdown(async {
            let _ = tokio::signal::ctrl_c().await;
        })
        .await
        .map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests;
