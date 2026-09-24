//! Thin stdio adapters over the versioned semantic service.
use kernel::control::CancellationToken;
use sema::*;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    io::{BufRead, Write},
    path::{Path, PathBuf},
    sync::{Arc, Mutex, mpsc},
};

type RpcResult = Result<Value, (i64, String)>;
type Controls = Arc<Mutex<Vec<(u64, Option<Value>, CancellationToken)>>>;

pub(super) fn serve(root: PathBuf, mcp: bool) -> anyhow::Result<()> {
    let mut server = Server::new(root, mcp)?;
    let controls: Controls = Arc::default();
    let (send, receive) = mpsc::channel();
    let reader_controls = controls.clone();
    let reader = std::thread::spawn(move || -> anyhow::Result<()> {
        let mut input = std::io::stdin().lock();
        let mut sequence = 0;
        while let Some(message) = read_message(&mut input, mcp)? {
            let method = message["method"].as_str().unwrap_or("");
            let mut controls = reader_controls.lock().unwrap();
            if matches!(method, "$/cancelRequest" | "notifications/cancelled") {
                let id = message["params"]
                    .get("id")
                    .or_else(|| message["params"].get("requestId"));
                for (_, request, token) in controls.iter() {
                    if request.as_ref() == id {
                        token.cancel();
                    }
                }
                continue;
            }
            if matches!(
                method,
                "textDocument/didOpen"
                    | "textDocument/didChange"
                    | "textDocument/didClose"
                    | "workspace/didChangeWatchedFiles"
            ) {
                for (_, _, token) in controls.iter() {
                    token.cancel();
                }
            }
            let token = CancellationToken::default();
            controls.push((sequence, message.get("id").cloned(), token.clone()));
            drop(controls);
            let exit = method == "exit";
            if send.send((sequence, message, token)).is_err() {
                break;
            }
            sequence += 1;
            if exit {
                break;
            }
        }
        Ok(())
    });
    let mut output = std::io::stdout().lock();
    for (sequence, message, token) in receive {
        if message["method"] == "exit" {
            break;
        }
        for response in server.handle(message, token) {
            write_message(&mut output, &response, mcp)?;
        }
        controls
            .lock()
            .unwrap()
            .retain(|(id, _, _)| *id != sequence);
    }
    reader
        .join()
        .map_err(|_| anyhow::anyhow!("protocol reader panicked"))??;
    Ok(())
}

fn read_message(input: &mut impl BufRead, mcp: bool) -> anyhow::Result<Option<Value>> {
    let mut line = String::new();
    if input.read_line(&mut line)? == 0 {
        return Ok(None);
    }
    if mcp {
        return Ok(Some(serde_json::from_str(&line)?));
    }
    let mut length = None;
    loop {
        if line.trim().is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':')
            && name.eq_ignore_ascii_case("Content-Length")
        {
            length = Some(value.trim().parse::<usize>()?);
        }
        line.clear();
        anyhow::ensure!(input.read_line(&mut line)? != 0, "truncated LSP header");
    }
    let length = length.ok_or_else(|| anyhow::anyhow!("missing Content-Length"))?;
    anyhow::ensure!(length <= 16 * 1024 * 1024, "protocol message is too large");
    let mut body = vec![0; length];
    input.read_exact(&mut body)?;
    Ok(Some(serde_json::from_slice(&body)?))
}

fn write_message(output: &mut impl Write, value: &Value, mcp: bool) -> anyhow::Result<()> {
    let body = serde_json::to_vec(value)?;
    if mcp {
        output.write_all(&body)?;
        output.write_all(b"\n")?;
    } else {
        write!(output, "Content-Length: {}\r\n\r\n", body.len())?;
        output.write_all(&body)?;
    }
    output.flush()?;
    Ok(())
}

struct Server {
    host: AnalysisHost,
    versions: BTreeMap<PathBuf, i64>,
    mcp: bool,
    initialized: bool,
    shutdown: bool,
}

impl Server {
    fn new(root: PathBuf, mcp: bool) -> std::io::Result<Self> {
        let mut host = AnalysisHost::new(root)?;
        host.refresh_disk();
        Ok(Self {
            host,
            versions: BTreeMap::new(),
            mcp,
            initialized: false,
            shutdown: false,
        })
    }

    fn handle(&mut self, message: Value, token: CancellationToken) -> Vec<Value> {
        let mut notifications = Vec::new();
        let method = message["method"].as_str().unwrap_or("");
        let result = if self.shutdown && method != "exit" {
            Err((-32600, "server is shut down".into()))
        } else if !self.initialized && !matches!(method, "initialize" | "ping") {
            Err((-32002, "server is not initialized".into()))
        } else {
            self.dispatch(method, &message["params"], token, &mut notifications)
        };
        if let Some(id) = message.get("id") {
            notifications.insert(
                0,
                match result {
                    Ok(result) => json!({"jsonrpc":"2.0", "id":id, "result":result}),
                    Err((code, message)) => {
                        json!({"jsonrpc":"2.0", "id":id, "error":{"code":code,"message":message}})
                    }
                },
            );
        }
        notifications
    }

    fn dispatch(
        &mut self,
        method: &str,
        params: &Value,
        token: CancellationToken,
        notifications: &mut Vec<Value>,
    ) -> RpcResult {
        match method {
            "initialize" => {
                self.initialized = true;
                Ok(if self.mcp {
                    json!({"protocolVersion":"2025-06-18", "capabilities":{"tools":{}}, "serverInfo":{"name":"ref-type", "version":env!("CARGO_PKG_VERSION")}})
                } else {
                    json!({"capabilities":{"positionEncoding":"utf-16", "textDocumentSync":{"openClose":true,"change":1,"save":true}, "definitionProvider":true,"hoverProvider":true,"documentSymbolProvider":true}, "serverInfo":{"name":"ref-type","version":env!("CARGO_PKG_VERSION")}})
                })
            }
            "initialized" | "notifications/initialized" | "ping" => Ok(json!({})),
            "shutdown" => {
                self.shutdown = true;
                Ok(Value::Null)
            }
            "textDocument/didOpen" | "textDocument/didChange" => {
                let document = &params["textDocument"];
                let path = document_path(document)?;
                let version = document["version"].as_i64().ok_or_else(invalid_params)?;
                if self
                    .versions
                    .get(&path)
                    .is_some_and(|previous| *previous >= version)
                {
                    return Ok(Value::Null);
                }
                let text = if method.ends_with("didOpen") {
                    document["text"].as_str()
                } else {
                    params["contentChanges"]
                        .as_array()
                        .and_then(|changes| changes.last())
                        .and_then(|change| change["text"].as_str())
                }
                .ok_or_else(invalid_params)?;
                self.versions.insert(path.clone(), version);
                self.host.sources_mut().set_overlay(&path, text.to_owned());
                self.host.refresh_disk();
                self.publish(token, notifications)?;
                Ok(Value::Null)
            }
            "textDocument/didClose" => {
                let path = document_path(&params["textDocument"])?;
                self.versions.remove(&path);
                self.host.sources_mut().close_overlay(&path);
                self.host.refresh_disk();
                self.publish(token, notifications)?;
                Ok(Value::Null)
            }
            "textDocument/didSave" | "workspace/didChangeWatchedFiles" => {
                self.host.refresh_disk();
                self.publish(token, notifications)?;
                Ok(Value::Null)
            }
            "textDocument/documentSymbol" => {
                let path = document_path(&params["textDocument"])?;
                let snapshot = self.host.snapshot();
                let file = snapshot
                    .sources()
                    .file_id(&path)
                    .ok_or_else(invalid_params)?;
                Ok(Value::Array(snapshot.outline().iter().filter(|item| item.location.file == file).map(|item| json!({
                    "name":item.key.name, "kind": if item.key.kind == ItemKind::Module {2} else {12},
                    "location":lsp_location(&snapshot, item.name_location.unwrap_or(item.location))
                })).collect()))
            }
            "textDocument/definition" | "textDocument/hover" => {
                let snapshot = self.host.snapshot();
                snapshot
                    .check_with_control(token, None)
                    .map_err(interrupted)?;
                let path = document_path(&params["textDocument"])?;
                let file = snapshot
                    .sources()
                    .file_id(&path)
                    .and_then(|id| snapshot.sources().file(id))
                    .ok_or_else(invalid_params)?;
                let offset = byte_offset(&file.source.text, &params["position"])
                    .ok_or_else(invalid_params)?;
                Ok(if method.ends_with("definition") {
                    snapshot
                        .definition_at(file.id, offset)
                        .map(|location| lsp_location(&snapshot, location))
                        .unwrap_or(Value::Null)
                } else {
                    snapshot
                        .type_at(file.id, offset)
                        .map(|ty| json!({"contents":{"kind":"plaintext","value":ty}}))
                        .unwrap_or(Value::Null)
                })
            }
            "tools/list" if self.mcp => Ok(json!({"tools": tools()})),
            "tools/call" if self.mcp => {
                let name = params["name"].as_str().ok_or_else(invalid_params)?;
                let result = self.tool(name, &params["arguments"], token);
                Ok(match result {
                    Ok(value) => {
                        json!({"content":[{"type":"text","text":value.to_string()}],"structuredContent":value,"isError":false})
                    }
                    Err((_, message)) => {
                        json!({"content":[{"type":"text","text":message}],"isError":true})
                    }
                })
            }
            _ => Err((-32601, format!("unsupported method: {method}"))),
        }
    }

    fn publish(
        &self,
        token: CancellationToken,
        notifications: &mut Vec<Value>,
    ) -> Result<(), (i64, String)> {
        let snapshot = self.host.snapshot();
        snapshot
            .check_with_control(token.clone(), None)
            .map_err(interrupted)?;
        if token.is_cancelled() {
            return Err(interrupted(kernel::control::Interrupted::Cancelled));
        }
        for file in snapshot.sources().files() {
            let mut params = json!({"uri":file_uri(&file.source.id.0), "diagnostics":snapshot.diagnostics(file.id).diagnostics.iter().map(|diagnostic| diagnostic_json(&snapshot, diagnostic)).collect::<Vec<_>>()});
            if let Some(version) = self.versions.get(&file.source.id.0) {
                params["version"] = json!(version);
            }
            notifications.push(
                json!({"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":params}),
            );
        }
        Ok(())
    }

    fn tool(&mut self, name: &str, args: &Value, token: CancellationToken) -> RpcResult {
        if name == "set_buffer" {
            let path = args["path"].as_str().ok_or_else(invalid_params)?;
            let text = args["text"].as_str().ok_or_else(invalid_params)?;
            self.host.sources_mut().set_overlay(path, text.to_owned());
            self.host.refresh_disk();
            return Ok(json!({"revision":self.host.sources().revision().0}));
        }
        if matches!(name, "give" | "refine") {
            let goal = &args["goal"];
            let id = GoalId {
                revision: RevisionId(goal["revision"].as_u64().ok_or_else(invalid_params)?),
                owner: ItemId(goal["owner"].as_u64().ok_or_else(invalid_params)?),
                local: goal["local"]
                    .as_u64()
                    .and_then(|id| u32::try_from(id).ok())
                    .ok_or_else(invalid_params)?,
            };
            let term = args["term"].as_str().ok_or_else(invalid_params)?;
            let proposal = kernel::control::run(token, None, || {
                if name == "give" {
                    self.host.give(id, term)
                } else {
                    self.host.refine(id, term)
                }
            })
            .map_err(interrupted)?
            .map_err(|error| (-32602, format!("{error:?}")))?;
            let snapshot = self.host.snapshot();
            return Ok(
                json!({"revision":proposal.revision.0,"edits":proposal.edits.iter().map(|edit| json!({
                "location":location_json(&snapshot, edit.location),"replacement":edit.replacement
            })).collect::<Vec<_>>(),"goals":proposal.goals.iter().map(goal_json).collect::<Vec<_>>(),
                "diagnostics":proposal.diagnostics.iter().map(|diagnostic| diagnostic.message.clone()).collect::<Vec<_>>() }),
            );
        }
        if !matches!(name, "check" | "goals") {
            return Err((-32602, format!("unknown tool: {name}")));
        }
        let snapshot = self.host.snapshot();
        let result = snapshot
            .check_with_control(token, None)
            .map_err(interrupted)?;
        Ok(
            json!({"revision":snapshot.revision().0,"status":format!("{:?}", result.status),
            "diagnostics":result.diagnostics.iter().map(|diagnostic| json!({"code":diagnostic.code,"message":diagnostic.message,
                "location":diagnostic.primary.map(|location| location_json(&snapshot, location))})).collect::<Vec<_>>(),
            "goals":result.goals.iter().map(goal_json).collect::<Vec<_>>() }),
        )
    }
}

fn tools() -> Vec<Value> {
    let goal = json!({"type":"object","properties":{"revision":{"type":"integer"},"owner":{"type":"integer"},"local":{"type":"integer"}},"required":["revision","owner","local"]});
    [
        ("check", "Check the current source snapshot", json!({"type":"object","properties":{}})),
        ("goals", "Read goals from the current snapshot", json!({"type":"object","properties":{}})),
        ("set_buffer", "Update an unsaved source buffer", json!({"type":"object","properties":{"path":{"type":"string"},"text":{"type":"string"}},"required":["path","text"]})),
        ("give", "Check a complete term and propose source edits", json!({"type":"object","properties":{"goal":goal,"term":{"type":"string"}},"required":["goal","term"]})),
        ("refine", "Check a term with holes and propose source edits", json!({"type":"object","properties":{"goal":goal,"term":{"type":"string"}},"required":["goal","term"]})),
    ].into_iter().map(|(name, description, schema)| json!({"name":name,"description":description,"inputSchema":schema})).collect()
}

fn goal_json(goal: &GoalSnapshot) -> Value {
    json!({"id":{"revision":goal.id.revision.0,"owner":goal.id.owner.0,"local":goal.id.local},
        "flavor":format!("{:?}",goal.flavor),"editable":goal.editable,"context":goal.context,"target":format!("{:?}",goal.target),
        "occurrences":goal.occurrences.iter().map(|location| json!({"file":location.file.0,"revision":location.revision.0,"start":location.range.start,"end":location.range.end})).collect::<Vec<_>>()})
}

fn location_json(snapshot: &AnalysisSnapshot, location: Location) -> Value {
    json!({"path":snapshot.sources().file(location.file).map(|file| file.source.id.0.clone()),"revision":location.revision.0,"start":location.range.start,"end":location.range.end})
}

fn diagnostic_json(snapshot: &AnalysisSnapshot, diagnostic: &Diagnostic) -> Value {
    let range = diagnostic
        .primary
        .map(|location| lsp_location(snapshot, location)["range"].clone())
        .unwrap_or_else(
            || json!({"start":{"line":0,"character":0},"end":{"line":0,"character":0}}),
        );
    json!({"range":range,"severity":1,"code":diagnostic.code,"source":"ref-type","message":diagnostic.message})
}

fn lsp_location(snapshot: &AnalysisSnapshot, location: Location) -> Value {
    let Some(file) = snapshot.sources().file(location.file) else {
        return Value::Null;
    };
    json!({"uri":file_uri(&file.source.id.0),"range":{"start":position(&file.source.text, location.range.start),"end":position(&file.source.text, location.range.end)}})
}

fn position(text: &str, byte: usize) -> Value {
    let prefix = &text[..byte.min(text.len())];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
    let start = prefix.rfind('\n').map_or(0, |position| position + 1);
    json!({"line":line,"character":prefix[start..].encode_utf16().count()})
}

fn byte_offset(text: &str, position: &Value) -> Option<usize> {
    let line = position["line"].as_u64()? as usize;
    let character = position["character"].as_u64()? as usize;
    let start = if line == 0 {
        0
    } else {
        text.match_indices('\n').nth(line - 1)?.0 + 1
    };
    let mut units = 0;
    for (offset, ch) in text[start..].char_indices() {
        if units == character {
            return Some(start + offset);
        }
        if ch == '\n' {
            return None;
        }
        units += ch.len_utf16();
    }
    (units == character).then_some(text.len())
}

fn file_uri(path: &Path) -> String {
    let mut uri = "file://".to_string();
    for byte in path.to_string_lossy().bytes() {
        if byte.is_ascii_alphanumeric() || b"/-._~:".contains(&byte) {
            uri.push(byte as char);
        } else {
            uri.push_str(&format!("%{byte:02X}"));
        }
    }
    uri
}

fn document_path(document: &Value) -> Result<PathBuf, (i64, String)> {
    let uri = document["uri"].as_str().ok_or_else(invalid_params)?;
    let path = uri.strip_prefix("file://").ok_or_else(invalid_params)?;
    if !path.starts_with('/') {
        return Err(invalid_params());
    }
    let bytes = path.as_bytes();
    let mut decoded = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            let hex = path.get(index + 1..index + 3).ok_or_else(invalid_params)?;
            decoded.push(u8::from_str_radix(hex, 16).map_err(|_| invalid_params())?);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    Ok(PathBuf::from(
        String::from_utf8(decoded).map_err(|_| invalid_params())?,
    ))
}

fn invalid_params() -> (i64, String) {
    (-32602, "invalid request parameters".into())
}
fn interrupted(error: kernel::control::Interrupted) -> (i64, String) {
    (-32800, format!("{error:?}"))
}

#[cfg(test)]
mod tests;
