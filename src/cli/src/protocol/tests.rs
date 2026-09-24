use super::*;

#[test]
fn lsp_framing_and_unicode_positions_round_trip() {
    let value = json!({"jsonrpc":"2.0","method":"example","params":{"text":"日本語😀"}});
    let mut encoded = Vec::new();
    write_message(&mut encoded, &value, false).unwrap();
    let mut input = std::io::Cursor::new(encoded);
    assert_eq!(read_message(&mut input, false).unwrap(), Some(value));
    assert!(read_message(&mut input, false).unwrap().is_none());
    let text = "/* 日本語😀 */\nvalue";
    for offset in text
        .char_indices()
        .map(|(offset, _)| offset)
        .chain([text.len()])
    {
        assert_eq!(byte_offset(text, &position(text, offset)), Some(offset));
    }
    let path = Path::new("/virtual/日本語 file.ref");
    assert_eq!(document_path(&json!({"uri":file_uri(path)})).unwrap(), path);
}

#[test]
fn lsp_publishes_buffer_versions_and_resolves_definitions() {
    let mut server = Server::new("/virtual/root.ref".into(), false).unwrap();
    server.handle(
        json!({"id":1,"method":"initialize","params":{}}),
        Default::default(),
    );
    let text = r"\module M { \definition A: \SetKind := \Set; \definition B: \SetKind := A; }";
    let notifications = server.handle(json!({"method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///virtual/root.ref","version":1,"text":text}}}), Default::default());
    assert_eq!(notifications[0]["params"]["version"], 1);
    assert_eq!(notifications[0]["params"]["diagnostics"], json!([]));
    let result = server.handle(json!({"id":2,"method":"textDocument/definition","params":{"textDocument":{"uri":"file:///virtual/root.ref"},"position":position(text, text.rfind("A;").unwrap())}}), Default::default());
    assert_eq!(
        result[0]["result"]["range"]["start"],
        position(text, text.find("A:").unwrap())
    );
    let revision = server.host.sources().revision();
    server.handle(json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///virtual/root.ref","version":1},"contentChanges":[{"text":"broken"}]}}), Default::default());
    assert_eq!(server.host.sources().revision(), revision);
}

#[test]
fn mcp_goal_operations_use_the_same_snapshot_and_reject_stale_ids() {
    let mut server = Server::new("/virtual/root.ref".into(), true).unwrap();
    server.handle(
        json!({"id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}),
        Default::default(),
    );
    let source = r"\module M(A: \Set, a: A) { \definition pending: A := ?; }";
    server
        .tool(
            "set_buffer",
            &json!({"path":"/virtual/root.ref","text":source}),
            Default::default(),
        )
        .unwrap();
    let goals = server
        .tool("goals", &json!({}), Default::default())
        .unwrap();
    let goal = goals["goals"][0]["id"].clone();
    let proposal = server
        .tool("give", &json!({"goal":goal,"term":"a"}), Default::default())
        .unwrap();
    assert_eq!(proposal["edits"][0]["replacement"], "a");
    assert_eq!(
        server.host.snapshot().check().status,
        CheckStatus::Incomplete
    );
    server
        .tool(
            "set_buffer",
            &json!({"path":"/virtual/root.ref","text":format!("{source}\n")}),
            Default::default(),
        )
        .unwrap();
    assert!(
        server
            .tool("give", &json!({"goal":goal,"term":"a"}), Default::default())
            .unwrap_err()
            .1
            .contains("Stale")
    );
}
