use lsp_server::{Connection, Message, Notification, Request, Response};
use sema::{Database, SourceSnapshot};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    path::{Path, PathBuf},
};
use url::Url;

type Result<T> = std::result::Result<T, Box<dyn Error + Send + Sync>>;

struct Server {
    database: Database,
    documents: BTreeMap<PathBuf, String>,
    published: BTreeMap<PathBuf, BTreeSet<PathBuf>>,
}

impl Server {
    fn new() -> Self {
        Self {
            database: Database::new(),
            documents: BTreeMap::new(),
            published: BTreeMap::new(),
        }
    }

    fn entry(file: &Path) -> PathBuf {
        let directories: Vec<_> = file.ancestors().skip(1).collect();
        if let Some(directory) = directories
            .iter()
            .find(|dir| dir.join("ref.toml").is_file())
        {
            return directory.to_path_buf();
        }
        if let Some(directory) = directories
            .iter()
            .find(|dir| dir.join("root.ref").is_file())
        {
            return directory.join("root.ref");
        }
        file.to_path_buf()
    }

    fn snapshot(&self, file: &Path) -> Result<SourceSnapshot> {
        let mut snapshot = SourceSnapshot::read(Self::entry(file))?;
        for (path, text) in &self.documents {
            snapshot.insert(path, text.clone());
        }
        Ok(snapshot)
    }

    fn analyze(&mut self, connection: &Connection, file: &Path) -> Result<()> {
        let entry = Self::entry(file);
        let snapshot = match self.snapshot(file) {
            Ok(snapshot) => snapshot,
            Err(error) => {
                self.publish(connection, file, vec![json!({
                    "range": zero_range(), "severity": 1, "source": "ref", "message": error.to_string()
                })])?;
                self.published
                    .entry(entry)
                    .or_default()
                    .insert(file.to_path_buf());
                return Ok(());
            }
        };
        let result = self.database.check(&snapshot);
        let mut grouped: BTreeMap<PathBuf, Vec<Value>> = BTreeMap::new();
        for diagnostic in result.all_diagnostics() {
            let path = diagnostic
                .location
                .as_ref()
                .map_or(file, |location| location.file.as_path());
            let range = diagnostic
                .location
                .as_ref()
                .and_then(|location| {
                    snapshot
                        .source(&location.file)
                        .map(|source| range(&source.text, &location.range))
                })
                .unwrap_or_else(zero_range);
            grouped.entry(path.to_path_buf()).or_default().push(json!({
                "range": range, "severity": 1, "source": "ref", "message": diagnostic.message
            }));
        }
        let mut paths = self.published.remove(&entry).unwrap_or_default();
        paths.extend(grouped.keys().cloned());
        paths.insert(file.to_path_buf());
        for path in &paths {
            self.publish(connection, path, grouped.remove(path).unwrap_or_default())?;
        }
        self.published.insert(entry, paths);
        Ok(())
    }

    fn publish(&self, connection: &Connection, path: &Path, diagnostics: Vec<Value>) -> Result<()> {
        let uri = Url::from_file_path(path).map_err(|_| "invalid file path")?;
        connection
            .sender
            .send(Message::Notification(Notification::new(
                "textDocument/publishDiagnostics".into(),
                json!({ "uri": uri.as_str(), "diagnostics": diagnostics }),
            )))?;
        Ok(())
    }

    fn request(&mut self, request: &Request) -> Value {
        let Some(uri) = request
            .params
            .pointer("/textDocument/uri")
            .and_then(Value::as_str)
        else {
            return Value::Null;
        };
        let Some(file) = file_path(uri) else {
            return Value::Null;
        };
        let Some(position) = request.params.get("position") else {
            return Value::Null;
        };
        let Ok(snapshot) = self.snapshot(&file) else {
            return Value::Null;
        };
        let Some(source) = snapshot.source(&file) else {
            return Value::Null;
        };
        let Some(offset) = offset(&source.text, position) else {
            return Value::Null;
        };
        let result = self.database.check(&snapshot);
        match request.method.as_str() {
            "textDocument/definition" => result
                .definition_at(&file, offset)
                .and_then(|declaration| location(&snapshot, &declaration.location))
                .unwrap_or(Value::Null),
            "textDocument/hover" => result
                .goals()
                .find(|goal| goal.location.contains(&file, offset))
                .map(|goal| {
                    let mut detail = goal.context.clone();
                    if let Some(judgement) = &goal.judgement {
                        detail.push_str("\n⊢ ");
                        detail.push_str(judgement);
                    }
                    for constraint in &goal.constraints {
                        detail.push('\n');
                        detail.push_str(constraint);
                    }
                    detail
                })
                .or_else(|| result.type_at(&file, offset).map(str::to_owned))
                .map(|value| json!({ "contents": { "kind": "plaintext", "value": value } }))
                .unwrap_or(Value::Null),
            "textDocument/references" => {
                let declaration = result.definition_at(&file, offset).or_else(|| {
                    result
                        .declarations()
                        .find(|declaration| declaration.location.contains(&file, offset))
                });
                let Some(declaration) = declaration else {
                    return json!([]);
                };
                let mut references: Vec<_> = result
                    .references_to(&declaration.id)
                    .filter_map(|reference| location(&snapshot, &reference.location))
                    .collect();
                if request
                    .params
                    .pointer("/context/includeDeclaration")
                    .and_then(Value::as_bool)
                    .unwrap_or(false)
                    && let Some(location) = location(&snapshot, &declaration.location)
                {
                    references.push(location);
                }
                json!(references)
            }
            _ => Value::Null,
        }
    }

    fn notification(&mut self, connection: &Connection, notification: Notification) -> Result<()> {
        let params = notification.params;
        match notification.method.as_str() {
            "textDocument/didOpen" => {
                if let (Some(file), Some(text)) = (
                    document_path(&params),
                    params.pointer("/textDocument/text").and_then(Value::as_str),
                ) {
                    self.documents.insert(file.clone(), text.to_owned());
                    self.analyze(connection, &file)?;
                }
            }
            "textDocument/didChange" => {
                if let Some(file) = document_path(&params)
                    && let Some(text) = self.documents.get_mut(&file)
                {
                    if let Some(changes) = params.get("contentChanges").and_then(Value::as_array) {
                        for change in changes {
                            let Some(replacement) = change.get("text").and_then(Value::as_str)
                            else {
                                continue;
                            };
                            if let Some(span) = change.get("range") {
                                let Some(start) = span
                                    .get("start")
                                    .and_then(|position| offset(text, position))
                                else {
                                    continue;
                                };
                                let Some(end) =
                                    span.get("end").and_then(|position| offset(text, position))
                                else {
                                    continue;
                                };
                                if start <= end {
                                    text.replace_range(start..end, replacement);
                                }
                            } else {
                                *text = replacement.to_owned();
                            }
                        }
                    }
                    self.analyze(connection, &file)?;
                }
            }
            "textDocument/didSave" => {
                if let Some(file) = document_path(&params) {
                    self.analyze(connection, &file)?;
                }
            }
            "textDocument/didClose" => {
                if let Some(file) = document_path(&params) {
                    self.documents.remove(&file);
                    self.analyze(connection, &file)?;
                }
            }
            "workspace/didChangeWatchedFiles" => {
                let files: Vec<_> = self.documents.keys().cloned().collect();
                for file in files {
                    self.analyze(connection, &file)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn document_path(params: &Value) -> Option<PathBuf> {
    file_path(params.pointer("/textDocument/uri")?.as_str()?)
}

fn file_path(uri: &str) -> Option<PathBuf> {
    Url::parse(uri).ok()?.to_file_path().ok()
}

fn offset(text: &str, position: &Value) -> Option<usize> {
    let line = usize::try_from(position.get("line")?.as_u64()?).ok()?;
    let column = usize::try_from(position.get("character")?.as_u64()?).ok()?;
    let start = if line == 0 {
        0
    } else {
        text.match_indices('\n').nth(line - 1)?.0 + 1
    };
    let slice = text[start..].split('\n').next()?;
    let mut utf16 = 0;
    for (byte, ch) in slice.char_indices() {
        if utf16 == column {
            return Some(start + byte);
        }
        utf16 += ch.len_utf16();
        if utf16 > column {
            return None;
        }
    }
    (utf16 == column).then_some(start + slice.len())
}

fn position(text: &str, byte: usize) -> Value {
    let mut byte = byte.min(text.len());
    while !text.is_char_boundary(byte) {
        byte -= 1;
    }
    let before = &text[..byte];
    let line = before.bytes().filter(|b| *b == b'\n').count();
    let column = before
        .rsplit('\n')
        .next()
        .unwrap_or("")
        .encode_utf16()
        .count();
    json!({ "line": line, "character": column })
}

fn range(text: &str, span: &std::ops::Range<usize>) -> Value {
    json!({ "start": position(text, span.start), "end": position(text, span.end) })
}

fn zero_range() -> Value {
    json!({ "start": { "line": 0, "character": 0 }, "end": { "line": 0, "character": 0 } })
}

fn location(snapshot: &SourceSnapshot, location: &sema::Location) -> Option<Value> {
    let source = snapshot.source(&location.file)?;
    let uri = Url::from_file_path(&location.file).ok()?;
    Some(json!({ "uri": uri.as_str(), "range": range(&source.text, &location.range) }))
}

fn main() -> Result<()> {
    let (connection, io_threads) = Connection::stdio();
    let capabilities = json!({
        "capabilities": {
            "textDocumentSync": { "openClose": true, "change": 2, "save": { "includeText": false } },
            "definitionProvider": true, "hoverProvider": true, "referencesProvider": true
        },
        "serverInfo": { "name": "ref-lsp", "version": env!("CARGO_PKG_VERSION") }
    });
    let (id, _) = connection.initialize_start()?;
    connection.initialize_finish(id, capabilities)?;
    let mut server = Server::new();
    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    break;
                }
                let result = server.request(&request);
                connection
                    .sender
                    .send(Message::Response(Response::new_ok(request.id, result)))?;
            }
            Message::Notification(notification) if notification.method == "exit" => break,
            Message::Notification(notification) => {
                server.notification(&connection, notification)?
            }
            Message::Response(_) => {}
        }
    }
    drop(connection);
    io_threads.join()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_use_utf16_columns() {
        let text = "α😀x\nβ";
        for byte in [0, 2, 6, 7, 8, 10] {
            assert_eq!(offset(text, &position(text, byte)), Some(byte));
        }
        assert_eq!(offset(text, &json!({ "line": 0, "character": 2 })), None);
    }

    #[test]
    fn package_manifest_takes_priority_over_source_root() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let file = repository.join("libs/real/src/CauchyReal.ref");
        assert_eq!(Server::entry(&file), repository.join("libs/real"));
    }
}
