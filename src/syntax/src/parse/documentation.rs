//! A source-level outline for documentation tools; no resolution or checking is performed.
use super::*;

#[derive(Debug)]
pub struct DocumentationItem {
    pub name: String,
    pub kind: &'static str,
    pub span: SourceSpan,
    pub signature: String,
    pub documentation: String,
    pub children: Vec<DocumentationItem>,
    pub external: bool,
}

/// Parse a file's declaration outline using the language's lexer and parser.
/// Consecutive block comments separated only by whitespace attach to the next item.
/// Source spelling is retained, including implicit types and mathematical notation.
pub fn parse_documentation(input: &str) -> Result<Vec<DocumentationItem>, ParseError> {
    let mut comments = Vec::new();
    let tokens = lex_with_comments(input, |span| comments.push(span))?;
    let mut parser = Parser::new(&tokens);
    let (items, spans) = parser.parse_module_items_with_spans()?;
    if let Some(extra) = tokens.get(parser.pos) {
        return Err(ParseError {
            kind: super::ParseErrorKind::Expected {
                expected: super::Expected::ModuleItem,
                found: Some(extra.kind.owned()),
            },
            start: extra.start,
            end: extra.end,
            source: None,
        });
    }
    Ok(outline(input, &tokens, &comments, &items, &spans))
}

fn outline(
    input: &str,
    tokens: &[SpannedToken<'_>],
    comments: &[SourceSpan],
    items: &[ModuleItem],
    spans: &[SourceSpan],
) -> Vec<DocumentationItem> {
    items
        .iter()
        .zip(spans)
        .filter_map(|(item, &span)| {
            let (name, kind) = match item {
                ModuleItem::Definition { name, owner, .. } => (
                    owner.as_ref().map_or_else(
                        || name.0.clone(),
                        |owner| format!("{}::{}", owner.type_name.0, name.0),
                    ),
                    "definition",
                ),
                ModuleItem::Inductive { type_name, .. } => (type_name.0.clone(), "inductive"),
                ModuleItem::Record { type_name, .. } => (type_name.0.clone(), "record"),
                ModuleItem::Structure { name, .. } => (name.0.clone(), "structure"),
                ModuleItem::ChildModule { module } => (module.name.0.clone(), "module"),
                ModuleItem::Import { import_name, .. } => (import_name.0.clone(), "import"),
                ModuleItem::MathMacro { name, .. } => (name.0.clone(), "math-macro"),
                ModuleItem::UserMacro { name, .. } => (name.0.clone(), "macro"),
                _ => return None,
            };
            let mut children = Vec::new();
            let mut external = false;
            if let ModuleItem::ChildModule { module } = item {
                match &module.body {
                    ModuleBody::Inline(items) => {
                        children =
                            outline(input, tokens, comments, items, &module.declaration_spans)
                    }
                    ModuleBody::External => external = true,
                }
            }
            // Only cut definition/macro bodies. Inductive constructors and structure
            // fields remain visible with their exact source types in the signature.
            let cut_assignment = matches!(
                item,
                ModuleItem::Definition { .. }
                    | ModuleItem::MathMacro { .. }
                    | ModuleItem::UserMacro { .. }
            );
            let cut_brace = matches!(item, ModuleItem::ChildModule { .. });
            let mut depth = 0usize;
            let mut end = span.end;
            for token in tokens
                .iter()
                .skip_while(|t| t.start < span.start)
                .take_while(|t| t.start < span.end)
            {
                if depth == 0
                    && ((cut_assignment && token.kind == Token::Assign)
                        || (cut_brace && token.kind == Token::LBrace))
                {
                    end = token.start;
                    break;
                }
                match token.kind {
                    Token::LParen | Token::MathLParen | Token::LBracket | Token::LBrace => {
                        depth += 1
                    }
                    Token::RParen | Token::MathRParen | Token::RBracket | Token::RBrace => {
                        depth = depth.saturating_sub(1)
                    }
                    _ => {}
                }
            }
            Some(DocumentationItem {
                name,
                kind,
                span,
                signature: input[span.start..end].trim().to_owned(),
                documentation: attached_comments(input, comments, span.start),
                children,
                external,
            })
        })
        .collect()
}

fn attached_comments(input: &str, comments: &[SourceSpan], start: usize) -> String {
    let mut cursor = start;
    let mut blocks = Vec::new();
    for comment in comments.iter().rev().filter(|comment| comment.end <= start) {
        if !input[comment.end..cursor].trim().is_empty() {
            break;
        }
        blocks.push(input[comment.start + 2..comment.end - 2].trim());
        cursor = comment.start;
    }
    blocks.reverse();
    blocks.join("\n\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_signatures_and_attaches_only_lexical_comments() {
        let input = r#"/* Module documentation. */
\module Demo {
  /* First paragraph. */ /* Second /* nested */ paragraph. */
  \definition id (A: \Set): \forall (x: A) -> A := \fun (x: A) => x;
  \definition T: \Set := A;
  /* A macro with a quoted comment delimiter. */
  \macro quoted ("/*", "*/") := \Prop;
  /* Structure docs. */
  \structure Pair[A: \Set]: \Set { first: A, second: A }
  \module Child;
}"#;
        let items = parse_documentation(input).unwrap();
        assert_eq!(items[0].documentation, "Module documentation.");
        let children = &items[0].children;
        assert_eq!(
            children[0].documentation,
            "First paragraph.\n\nSecond /* nested */ paragraph."
        );
        assert_eq!(
            children[0].signature,
            r"\definition id (A: \Set): \forall (x: A) -> A"
        );
        assert!(children[1].documentation.is_empty());
        assert_eq!(
            children[2].documentation,
            "A macro with a quoted comment delimiter."
        );
        assert!(children[3].signature.contains("first: A, second: A"));
        assert!(children[4].external);
    }

    #[test]
    fn nested_assignments_in_types_do_not_cut_the_signature() {
        let input = r"\definition f: \block { \let T: \Set := A \then \return T } := value;";
        let item = parse_documentation(input).unwrap().remove(0);
        assert_eq!(
            item.signature,
            r"\definition f: \block { \let T: \Set := A \then \return T }"
        );
    }
}
