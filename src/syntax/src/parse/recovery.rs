//! Recover declaration boundaries without replacing missing terms with holes.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxDiagnostic {
    pub span: SourceSpan,
    pub message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxTokenKind {
    Identifier,
    Hole,
    Keyword,
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxToken {
    pub kind: SyntaxTokenKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct ParsedSource {
    pub modules: Vec<Module>,
    pub items: Vec<ModuleItem>,
    pub item_spans: Vec<SourceSpan>,
    pub tokens: Vec<SyntaxToken>,
    pub diagnostics: Vec<SyntaxDiagnostic>,
}

/// Root files contain module declarations; external files contain module items.
/// Byte ranges always refer to the original, unmodified input, including comments.
pub fn parse_source_recovering(input: &str, root: bool) -> ParsedSource {
    let (tokens, errors) = lex_recovering(input);
    let mut parser = Parser::new(&tokens);
    parser.recovery = true;
    parser.errors = errors;
    let mut modules = Vec::new();
    let mut items = Vec::new();
    let mut item_spans = Vec::new();
    if root {
        while parser.pos < tokens.len() {
            let start = parser.pos;
            match parser.parse_module() {
                Ok(module) => modules.push(module),
                Err(error) => {
                    parser.errors.push(error);
                    parser.recover_declaration(start, true);
                }
            }
        }
    } else {
        while parser.pos < tokens.len() {
            let (more_items, more_spans) = parser
                .parse_module_items_with_spans()
                .expect("recovering item parser records errors");
            items.extend(more_items);
            item_spans.extend(more_spans);
            if parser.pos < tokens.len() {
                let span = parser.span_at(parser.pos);
                parser.errors.push(ParseError {
                    msg: "unexpected closing brace".into(),
                    start: span.start,
                    end: span.end,
                });
                parser.pos += 1;
            }
        }
    }
    ParsedSource {
        modules,
        items,
        item_spans,
        tokens: tokens
            .iter()
            .map(|token| SyntaxToken {
                kind: match token.kind {
                    Token::Ident(_) => SyntaxTokenKind::Identifier,
                    Token::Hole | Token::UnspecifiedVar(_) => SyntaxTokenKind::Hole,
                    Token::KeyWord(_) => SyntaxTokenKind::Keyword,
                    _ => SyntaxTokenKind::Other,
                },
                span: SourceSpan {
                    start: token.start,
                    end: token.end,
                },
            })
            .collect(),
        diagnostics: parser
            .errors
            .into_iter()
            .map(|error| SyntaxDiagnostic {
                span: if error.start == 0 && error.end == 0 {
                    SourceSpan {
                        start: input.len(),
                        end: input.len(),
                    }
                } else {
                    SourceSpan {
                        start: error.start,
                        end: error.end,
                    }
                },
                message: error.msg,
            })
            .collect(),
    }
}
