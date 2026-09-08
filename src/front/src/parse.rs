use crate::{parse::term_parse::TermParser, syntax::*};
use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
#[logos(skip r"[ \t\n\f]+")]
enum Token<'a> {
    // Keywords (start from "\" character)
    #[regex(r"\\[a-zA-Z][a-zA-Z0-9-]*")]
    KeyWord(&'a str), // any concatenation of non-alphanumeric symbols without spaces
    #[regex(r"\$[a-zA-Z][a-zA-Z0-9_]*")]
    MacroVar(&'a str),
    #[regex(r#""[^"\n]*""#)]
    QuotedMacro(&'a str),
    #[regex(r"\\[^a-zA-Z0-9\s(){}$\[\]_,]+")]
    EscapedMacro(&'a str),
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    Ident(&'a str),
    #[regex(r"[0-9]+")]
    Number(&'a str),
    #[regex(r"\?[a-zA-Z0-9_]*")]
    UnspecifiedVar(&'a str),
    #[token("_", priority = 3)]
    Hole,
    // any non-space sequence that does not include reserved delimiters or `_`/`?`
    #[token("/\\")]
    #[regex(r#"[^\s\\A-Za-z0-9?(){}$\[\]_\"]+"#)]
    Macro(&'a str),
    // special symbol tokens (which have their own meaning in parsing)
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("$(")]
    MathLParen,
    #[token("$)")]
    MathRParen,
    // comment tokens (will be ignored before lex_all output)
    #[token("/*")]
    CommentStart,
    #[token("*/")]
    CommentEnd,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    // mapped tokens (will be produced by mapping MacroToken in lex_all)
    // 2 char
    ComputationArrow, // "~>"
    BindArrow,        // "<-"
    Arrow,            // "->"
    DoubleArrow,      // "=>"
    Assign,           // ":="
    // 1 char
    Pipe,        // "|"
    Colon,       // ":"
    Semicolon,   // ";"
    Period,      // "."
    Comma,       // ","
    Equal,       // "="
    Exclamation, // "!"
    DoubleColon, // "::"
}

static SORT_KEYWORDS: &[&str] = &["\\Prop", "\\PropKind", "\\Set", "\\SetKind"];

static EXPRESSION_ATOM_KEYWORDS: &[&str] = &[
    "\\elim", // inductive eliminator
    "\\prec", // eliminator as primitive recursive form
    "\\Power",
    "\\Subset",
    "\\Pred",
    "\\Ty",
    "\\subsetinto", // usuals
    "\\fun",
    "\\forall",
    "\\cfun",
    "\\do",
    "\\case",
    "\\record",
    "\\VType",
    "\\U",
    "\\F",
    "\\thunk",
    "\\return",
    "\\force",
    "\\capp",
    "\\RunStep",
    "\\PRunStep",
    "\\continue",
    "\\Pcontinue",
    "\\finish",
    "\\Pfinish",
    "\\Acc",
    "\\run",
    "\\Prun",
    "\\runCase",
    "\\PrunCase",
    "\\runStepRec",
    "\\Box",
    "\\box",
    "\\Force",
    "\\boxapp",
    "\\exists", // \exists <Bind>
    "\\take",   // \take <Bind> => <body>
    "\\block",  // block expression
];

static PROOF_TERM_KEYWORDS: &[&str] = &[
    "\\exact",
    "\\bysub",
    "\\refl",
    "\\idelim",
    "\\axiom",
    "\\takeelim",
    "\\accintro",
    "\\accdescent",
];

fn lex_all<'a>(input: &'a str) -> Result<Vec<SpannedToken<'a>>, String> {
    let mut lexer = Token::lexer(input);
    let mut out = Vec::new();

    let mut comment_level = 0;

    while let Some(tok) = lexer.next() {
        match tok {
            Ok(Token::CommentStart) => {
                comment_level += 1;
            }
            Ok(Token::CommentEnd) => {
                if comment_level == 0 {
                    return Err(format!(
                        "unmatched comment end at {}..{}",
                        lexer.span().start,
                        lexer.span().end
                    ));
                }
                comment_level -= 1;
            }
            Ok(_) if comment_level > 0 => {
                continue; // skip tokens inside comments
            }
            Ok(Token::Macro(s)) => {
                // map known symbol sequences to specific token variants
                let mapped = match s {
                    "~>" => Token::ComputationArrow,
                    "<-" => Token::BindArrow,
                    "->" => Token::Arrow,
                    "=>" => Token::DoubleArrow,
                    ":=" => Token::Assign,
                    "|" => Token::Pipe,
                    ":" => Token::Colon,
                    ";" => Token::Semicolon,
                    "." => Token::Period,
                    "," => Token::Comma,
                    "=" => Token::Equal,
                    "!" => Token::Exclamation,
                    "::" => Token::DoubleColon,
                    _ => Token::Macro(s),
                };

                let span = lexer.span();
                out.push(SpannedToken {
                    kind: mapped,
                    start: span.start,
                    end: span.end,
                });
            }
            Ok(kind) => {
                let span = lexer.span();
                out.push(SpannedToken {
                    kind,
                    start: span.start,
                    end: span.end,
                });
            }
            Err(_) => {
                let span = lexer.span();
                let bad = &input[span.clone()];
                return Err(format!(
                    "lex error at {}..{}: {:?}",
                    span.start, span.end, bad
                ));
            }
        }
    }

    Ok(out)
}

#[derive(Debug, Clone, Copy)]
struct SpannedToken<'a> {
    kind: Token<'a>,
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct ParseError {
    msg: String,
    start: usize,
    end: usize,
}

mod term_parse;

trait TokenCursor<'a>: Sized {
    fn tokens(&self) -> &'a [SpannedToken<'a>];

    fn span_at(&self, position: usize) -> SourceSpan {
        self.tokens().get(position).map_or_else(
            || {
                let end = self.tokens().last().map_or(0, |token| token.end);
                SourceSpan { start: end, end }
            },
            |token| SourceSpan {
                start: token.start,
                end: token.end,
            },
        )
    }

    fn eof_error(&self, expect: &str) -> ParseError {
        let span = self.span_at(self.tokens().len());
        ParseError {
            msg: format!("expected {expect}, found <eof>"),
            start: span.start,
            end: span.end,
        }
    }

    fn position(&self) -> usize;
    fn set_position(&mut self, position: usize);

    fn peek(&self) -> Option<&'a Token<'a>> {
        self.tokens().get(self.position()).map(|token| &token.kind)
    }

    fn next(&mut self) -> Option<&'a SpannedToken<'a>> {
        let token = self.tokens().get(self.position());
        if token.is_some() {
            self.set_position(self.position() + 1);
        }
        token
    }

    fn bump_if_token(&mut self, expected: Token<'a>) -> bool {
        if self.peek() == Some(&expected) {
            self.set_position(self.position() + 1);
            return true;
        }
        false
    }

    fn bump_if_keyword(&mut self, keyword: &str) -> bool {
        if let Some(Token::KeyWord(actual)) = self.peek()
            && *actual == keyword
        {
            self.set_position(self.position() + 1);
            return true;
        }
        false
    }

    fn expect_token(&mut self, expected: Token<'a>) -> Result<SpannedToken<'a>, ParseError> {
        if let Some(token) = self.tokens().get(self.position()) {
            if token.kind == expected {
                self.set_position(self.position() + 1);
                Ok(*token)
            } else {
                Err(ParseError {
                    msg: format!("expected {expected:?}, found {:?}", token.kind),
                    start: token.start,
                    end: token.end,
                })
            }
        } else {
            Err(self.eof_error(&format!("{expected:?}")))
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(token) => match token.kind {
                Token::KeyWord(actual) if actual == keyword => Ok(actual),
                other => Err(ParseError {
                    msg: format!("expected keyword {keyword}, found {other:?}"),
                    start: token.start,
                    end: token.end,
                }),
            },
            None => Err(self.eof_error("keyword")),
        }
    }

    fn expect_ident(&mut self) -> Result<Identifier, ParseError> {
        match self.next() {
            Some(token) => match token.kind {
                Token::Ident(name) => Ok(Identifier(name.to_owned())),
                other => Err(ParseError {
                    msg: format!("expected identifier, found {other:?}"),
                    start: token.start,
                    end: token.end,
                }),
            },
            None => Err(self.eof_error("identifier")),
        }
    }
}

#[derive(Debug)]
struct Parser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
}

// `fn bump_if_*` consumes tokens only if matched
// `fn parse_*` consumes tokens whether succeed or fail, the parser position is advanced
// A selected production commits: errors never restore the cursor.
impl<'a> Parser<'a> {
    fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (sexp, consumed) = term_parser.parse_sexp_advanced()?;
        self.pos += consumed;
        Ok(sexp)
    }

    fn parse_macro_template(&mut self) -> Result<SExp, ParseError> {
        let mut term_parser = TermParser::new_macro_template(&self.tokens[self.pos..]);
        let (sexp, consumed) = term_parser.parse_sexp_advanced()?;
        self.pos += consumed;
        Ok(sexp)
    }

    fn parse_arrow_nosubset(&mut self) -> Result<(Vec<RightBind>, SExp), ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (rightbinds, sexp, consumed) = term_parser.parse_arrow_nosubset_advanced()?;
        self.pos += consumed;
        Ok((rightbinds, sexp))
    }

    // "(" <ident> ("," <ident>)* ":" <ty: SExp> ")"
    fn parse_rightbinds(&mut self) -> Result<Vec<RightBind>, ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (rightbind, advanced) = term_parser.parse_simple_binds_advanced()?;
        self.pos += advanced;
        Ok(rightbind)
    }

    // <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
    fn parse_definition(&mut self) -> Result<ModuleItem, ParseError> {
        let first_name = self.expect_ident()?;
        let mut first_binders = Vec::new();
        while self.peek() == Some(&Token::LParen) {
            let binders = self.parse_rightbinds()?;
            first_binders.extend(binders);
        }
        let (owner, name, binders) = if self.bump_if_token(Token::DoubleColon) {
            let name = self.expect_ident()?;
            let mut binders = Vec::new();
            while self.peek() == Some(&Token::LParen) {
                let parsed = self.parse_rightbinds()?;
                binders.extend(parsed);
            }
            (
                Some(AssociatedOwner {
                    type_name: first_name,
                    parameters: first_binders,
                }),
                name,
                binders,
            )
        } else {
            (None, first_name, first_binders)
        };
        self.expect_token(Token::Colon)?;
        let ty = self.parse_sexp()?;
        self.expect_token(Token::Assign)?;
        let body = self.parse_sexp()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Definition {
            owner,
            name,
            binders,
            ty,
            body,
        })
    }

    fn parse_program_definition(
        &mut self,
    ) -> Result<(Option<AssociatedOwner>, Identifier, SExp, SExp), ParseError> {
        let ModuleItem::Definition {
            owner,
            name,
            binders,
            ty,
            body,
        } = self.parse_definition()?
        else {
            unreachable!()
        };
        if !binders.is_empty() {
            return Err(ParseError {
                msg: "Program definitions use explicit \\cfun binders in their body".into(),
                start: self.span_at(self.pos.saturating_sub(1)).start,
                end: self.span_at(self.pos.saturating_sub(1)).end,
            });
        }
        Ok((owner, name, ty, body))
    }

    fn parse_structure_decl(&mut self) -> Result<ModuleItem, ParseError> {
        let type_name = self.expect_ident()?;
        let mut parameters = Vec::new();
        while self.peek() == Some(&Token::LParen) {
            let parsed = self.parse_rightbinds()?;
            parameters.extend(parsed);
        }
        self.expect_token(Token::Colon)?;
        let result = self.parse_sexp()?;
        let kind = match result {
            SExp::Sort(sort) => InductiveKind::Pts(sort),
            SExp::ValueType => InductiveKind::Program,
            _ => {
                return Err(ParseError {
                    msg: "expected PTS sort or \\VType in structure declaration".into(),
                    start: self.span_at(self.pos.saturating_sub(1)).start,
                    end: self.span_at(self.pos.saturating_sub(1)).end,
                });
            }
        };
        self.expect_token(Token::Assign)?;
        self.expect_token(Token::LBrace)?;
        let mut fields = Vec::new();
        while !self.bump_if_token(Token::RBrace) {
            let name = self.expect_ident()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            fields.push((name, ty));
            if self.bump_if_token(Token::RBrace) {
                break;
            }
            self.expect_token(Token::Comma)?;
        }
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Record {
            type_name,
            parameters,
            kind,
            fields,
        })
    }

    // (cosumed "\import" keyword) <path: ModuleAccessPath> "\as" <import_name: Ident> ";"
    fn parse_import(&mut self) -> Result<ModuleItem, ParseError> {
        let parent_num: Option<usize> = if self.bump_if_keyword("\\root") {
            self.expect_token(Token::Period)?; // expect '.'
            None
        } else {
            let mut count = 0;
            while self.bump_if_keyword("\\parent") {
                count += 1;
                self.expect_token(Token::Period)?; // expect '.'
            }
            Some(count)
        };

        let mut calls = vec![];

        if matches!(self.peek(), Some(Token::Ident(_))) {
            loop {
                calls.push(self.parse_module_access_path()?);
                if !self.bump_if_token(Token::Period) {
                    break;
                }
            }
        }

        // 3. "\as" <import_name: Ident> ";"
        self.expect_keyword("\\as")?;
        let import_name = self.expect_ident()?;
        self.expect_token(Token::Semicolon)?;

        let path = match parent_num {
            Some(num) => ModuleInstantiatePath::FromCurrent {
                back_parent: num,
                calls,
            },
            None => ModuleInstantiatePath::FromRoot { calls },
        };

        Ok(ModuleItem::Import { path, import_name })
    }

    // <specified_module> = <mod_name> "(" (<param: Ident> ":=" <arg: SExp> ",")* ")"
    fn parse_module_access_path(
        &mut self,
    ) -> Result<(Identifier, Vec<(Identifier, SExp)>), ParseError> {
        let module_name = self.expect_ident()?;
        self.expect_token(Token::LParen)?;

        let mut assign_pairs = Vec::new();
        if !self.bump_if_token(Token::RParen) {
            loop {
                let param = self.expect_ident()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let arg = self.parse_sexp()?;
                assign_pairs.push((param, arg));

                if self.bump_if_token(Token::RParen) {
                    break; // end of parameter list
                }
                self.expect_token(Token::Comma)?; // expect ','
            }
        }

        Ok((module_name, assign_pairs))
    }

    // "|" <ctor_name: Ident> ":" <rightbinds> "->" <SExp> ";"
    fn parse_ctor_decl(&mut self) -> Result<(Identifier, Vec<RightBind>, SExp), ParseError> {
        self.expect_token(Token::Pipe)?; // expect '|'
        let ctor_name = self.expect_ident()?;
        self.expect_token(Token::Colon)?; // expect ':'
        let (rightbinds, ends) = self.parse_arrow_nosubset()?;
        self.expect_token(Token::Semicolon)?; // expect ';'
        Ok((ctor_name, rightbinds, ends))
    }

    //  <type_name: Ident> ("(" <param: Ident> ":" <ty: SExp> ")")* ":" <arity> ":=" (<ctor_decl>)* ";"
    fn parse_inductive_decl(&mut self) -> Result<ModuleItem, ParseError> {
        let type_name = self.expect_ident()?;

        let mut parameters = vec![];

        while self.peek() == Some(&Token::LParen) {
            let param = self.parse_rightbinds()?;
            parameters.extend(param);
        }

        self.expect_token(Token::Colon)?;

        // <arity> = <indices> <Sort>
        // <indices> = <rightbinds>
        let (indices, expect_sort) = self.parse_arrow_nosubset()?;
        let kind = match expect_sort {
            SExp::Sort(s) => InductiveKind::Pts(s),
            SExp::ValueType if indices.is_empty() => InductiveKind::Program,
            SExp::ValueType => {
                return Err(ParseError {
                    msg: "Program datatype declarations cannot have indices".into(),
                    start: self.span_at(self.pos.saturating_sub(1)).start,
                    end: self.span_at(self.pos.saturating_sub(1)).end,
                });
            }
            _ => {
                return Err(ParseError {
                    msg: "expected PTS sort or \\VType in inductive declaration".into(),
                    start: self.span_at(self.pos.saturating_sub(1)).start,
                    end: self.span_at(self.pos.saturating_sub(1)).end,
                });
            }
        };

        // body of constructors
        self.expect_token(Token::Assign)?;
        let mut constructors = vec![];
        while self.peek() == Some(&Token::Pipe) {
            constructors.push(self.parse_ctor_decl()?);
        }
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Inductive {
            type_name,
            parameters,
            indices,
            kind,
            constructors,
        })
    }

    fn parse_macro_pattern_atom(&mut self) -> Result<MacroSeqAtom, ParseError> {
        match self.next() {
            Some(SpannedToken {
                kind: Token::MacroVar(name),
                ..
            }) => Ok(MacroSeqAtom::Capture(Identifier(name[1..].to_string()))),
            Some(SpannedToken {
                kind: Token::EscapedMacro(token),
                ..
            }) => Ok(MacroSeqAtom::Tok(MacroToken(token[1..].to_string()))),
            Some(SpannedToken {
                kind: Token::QuotedMacro(token),
                ..
            }) => Ok(MacroSeqAtom::Quoted(token[1..token.len() - 1].to_string())),
            Some(SpannedToken {
                kind: Token::LParen,
                ..
            }) => {
                let atoms = self.parse_macro_pattern_items(Token::RParen)?;
                self.expect_token(Token::RParen)?;
                Ok(MacroSeqAtom::Seq(atoms))
            }
            Some(token) => Err(ParseError {
                msg: format!(
                    "expected macro capture, escaped token, quoted literal, or nested pattern; found {:?}",
                    token.kind
                ),
                start: token.start,
                end: token.end,
            }),
            None => Err(self.eof_error("macro pattern atom")),
        }
    }

    fn parse_macro_pattern_items(
        &mut self,
        close: Token<'a>,
    ) -> Result<Vec<MacroSeqAtom>, ParseError> {
        let mut atoms = Vec::new();
        if self.peek() == Some(&close) {
            return Ok(atoms);
        }
        loop {
            atoms.push(self.parse_macro_pattern_atom()?);
            if self.peek() == Some(&close) {
                return Ok(atoms);
            }
            self.expect_token(Token::Comma)?;
        }
    }

    fn parse_macro_decl(&mut self, math: bool) -> Result<ModuleItem, ParseError> {
        let name = self.expect_ident()?;
        self.expect_token(Token::LParen)?;
        let before = self.parse_macro_pattern_items(Token::RParen)?;
        self.expect_token(Token::RParen)?;
        self.expect_token(Token::Assign)?;
        let after = self.parse_macro_template()?;
        self.expect_token(Token::Semicolon)?;
        Ok(if math {
            ModuleItem::MathMacro {
                name,
                before,
                after,
            }
        } else {
            ModuleItem::UserMacro {
                name,
                before,
                after,
            }
        })
    }

    fn parse_use_macro(&mut self) -> Result<ModuleItem, ParseError> {
        let import_name = self.expect_ident()?;
        self.expect_token(Token::Period)?;
        let macro_name = self.expect_ident()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::UseMacro {
            import_name,
            macro_name,
        })
    }

    fn try_parse_module_item(&mut self) -> Result<Option<ModuleItem>, ParseError> {
        let start_pos = self.pos;
        if self.bump_if_keyword("\\definition") {
            let def = self.parse_definition()?;
            return Ok(Some(def));
        }
        if self.bump_if_keyword("\\vdefinition") {
            let (owner, name, ty, body) = self.parse_program_definition()?;
            let ty = ty.try_into().map_err(|msg| ParseError {
                msg,
                start: self.span_at(start_pos).start,
                end: self.span_at(self.pos).end,
            })?;
            let body = body.try_into().map_err(|msg| ParseError {
                msg,
                start: self.span_at(start_pos).start,
                end: self.span_at(self.pos).end,
            })?;
            return Ok(Some(ModuleItem::ValueDefinition {
                owner,
                name,
                ty,
                body,
            }));
        }
        if self.bump_if_keyword("\\cdefinition") {
            let (owner, name, ty, body) = self.parse_program_definition()?;
            let ty = ty.try_into().map_err(|msg| ParseError {
                msg,
                start: self.span_at(start_pos).start,
                end: self.span_at(self.pos).end,
            })?;
            let body = body.try_into().map_err(|msg| ParseError {
                msg,
                start: self.span_at(start_pos).start,
                end: self.span_at(self.pos).end,
            })?;
            return Ok(Some(ModuleItem::ComputationDefinition {
                owner,
                name,
                ty,
                body,
            }));
        }
        if self.bump_if_keyword("\\import") {
            let imp = self.parse_import()?;
            return Ok(Some(imp));
        }
        if self.bump_if_keyword("\\inductive") {
            let ind = self.parse_inductive_decl()?;
            return Ok(Some(ind));
        }
        if self.bump_if_keyword("\\structure") {
            return self.parse_structure_decl().map(Some);
        }
        if self.bump_if_keyword("\\math-macro") {
            return self.parse_macro_decl(true).map(Some);
        }
        if self.bump_if_keyword("\\macro") {
            return self.parse_macro_decl(false).map(Some);
        }
        if self.bump_if_keyword("\\use") {
            return self.parse_use_macro().map(Some);
        }
        if self.peek() == Some(&Token::KeyWord("\\module")) {
            let module = self.parse_module()?;
            return Ok(Some(ModuleItem::ChildModule {
                module: module.into(),
            }));
        }
        if self.bump_if_keyword("\\eval") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Eval { exp }));
        }
        if self.bump_if_keyword("\\normalize") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Normalize { exp }));
        }
        if self.bump_if_keyword("\\ceval") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ComputationEval {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\cnormalize") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ComputationNormalize {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\vcheck") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ValueCheck {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
                ty: ty.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\ccheck") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ComputationCheck {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
                ty: ty.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\vinfer") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ValueInfer {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\cinfer") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::ComputationInfer {
                exp: exp.try_into().map_err(|msg| ParseError {
                    msg,
                    start: self.span_at(start_pos).start,
                    end: self.span_at(self.pos).end,
                })?,
            }));
        }
        if self.bump_if_keyword("\\check") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Check { exp, ty }));
        }
        if self.bump_if_keyword("\\infer") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Infer { exp }));
        }
        Ok(None)
    }

    // parse an inline or external module
    // "\module" <module_name: Ident> <parameters>? ("{" (<module_item>)* "}" | ";")
    fn parse_module(&mut self) -> Result<Module, ParseError> {
        let start = self.tokens.get(self.pos).map_or(0, |token| token.start);
        let mut declaration_spans = Vec::new();
        self.expect_keyword("\\module")?;
        let module_name = self.expect_ident()?;

        let parameters = if self.peek() == Some(&Token::LParen) {
            self.parse_rightbinds()?
        } else {
            Vec::new()
        };

        let body = if self.bump_if_token(Token::Semicolon) {
            ModuleBody::External
        } else {
            self.expect_token(Token::LBrace)?; // expect '{'
            let (declarations, spans) = self.parse_module_items_with_spans()?;
            declaration_spans = spans;
            self.expect_token(Token::RBrace)?; // expect '}'
            ModuleBody::Inline(declarations)
        };

        Ok(Module {
            name: module_name,
            parameters,
            body,
            span: SourceSpan {
                start,
                end: self.tokens[self.pos - 1].end,
            },
            declaration_spans,
            source: None,
            header_source: None,
        })
    }

    fn parse_module_items_with_spans(
        &mut self,
    ) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), ParseError> {
        let mut declarations = Vec::new();
        let mut spans = Vec::new();
        loop {
            let start = self.tokens.get(self.pos).map_or(0, |token| token.start);
            let Some(item) = self.try_parse_module_item()? else {
                break;
            };
            spans.push(SourceSpan {
                start,
                end: self.tokens[self.pos - 1].end,
            });
            declarations.push(item);
        }
        Ok((declarations, spans))
    }
}

impl<'a> TokenCursor<'a> for Parser<'a> {
    fn tokens(&self) -> &'a [SpannedToken<'a>] {
        self.tokens
    }

    fn position(&self) -> usize {
        self.pos
    }

    fn set_position(&mut self, position: usize) {
        debug_assert!(
            position >= self.pos,
            "parser cursor must never move backwards"
        );
        self.pos = position;
    }
}

pub fn str_parse_exp(input: &str) -> Result<SExp, String> {
    let v = lex_all(input)?;
    let mut parser = Parser::new(&v);

    let sexp = parser
        .parse_sexp()
        .map_err(|e| format!("parse error: {} ({}..{})", e.msg, e.start, e.end))?;

    if parser.pos < parser.tokens.len() {
        let extra = &parser.tokens[parser.pos];
        return Err(format!(
            "extra tokens after expression starting at {}..{}: {:?}",
            extra.start, extra.end, extra.kind
        ));
    }
    Ok(sexp)
}

pub fn str_parse_modules(input: &str) -> Result<Vec<Module>, String> {
    parse_modules(input, None)
}

pub fn parse_modules_from_source(
    source: &std::sync::Arc<SourceFile>,
) -> Result<Vec<Module>, String> {
    parse_modules(&source.text, Some(source))
}

fn source_parse_error(error: ParseError, source: Option<&std::sync::Arc<SourceFile>>) -> String {
    let message = format!(
        "parse error: {} ({}..{})",
        error.msg, error.start, error.end
    );
    match source {
        Some(source) => {
            let span = if error.start == 0 && error.end == 0 {
                SourceSpan {
                    start: source.text.len(),
                    end: source.text.len(),
                }
            } else {
                SourceSpan {
                    start: error.start,
                    end: error.end,
                }
            };
            format!(
                "{message}\n{}",
                SourceLocation {
                    source: source.clone(),
                    span
                }
                .render()
            )
        }
        None => message,
    }
}

fn parse_modules(
    input: &str,
    source: Option<&std::sync::Arc<SourceFile>>,
) -> Result<Vec<Module>, String> {
    let v = lex_all(input)?;
    let mut parser = Parser::new(&v);
    let mut modules = Vec::new();

    while parser.pos < parser.tokens.len() {
        let module = parser
            .parse_module()
            .map_err(|e| source_parse_error(e, source))?;
        modules.push(module);
    }

    Ok(modules)
}

/// Parse an external module file, preserving declaration spans for diagnostics.
pub fn parse_module_items_from_source(
    source: &std::sync::Arc<SourceFile>,
) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), String> {
    parse_module_items(&source.text, Some(source))
}

fn parse_module_items(
    input: &str,
    source: Option<&std::sync::Arc<SourceFile>>,
) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), String> {
    let v = lex_all(input)?;
    let mut parser = Parser::new(&v);
    let declarations = parser
        .parse_module_items_with_spans()
        .map_err(|e| source_parse_error(e, source))?;

    if parser.pos < parser.tokens.len() {
        let extra = &parser.tokens[parser.pos];
        return Err(format!(
            "expected a module item at {}..{}, found {:?}",
            extra.start, extra.end, extra.kind
        ));
    }

    Ok(declarations)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn logos_test() {
        fn tok_all_ok(input: &'static str) {
            let mut toks = Token::lexer(input);
            loop {
                match toks.next() {
                    Some(Ok(ok)) => {
                        println!("span[{:?}] slice[{}]", toks.span(), toks.slice());
                        println!("  {:?}", ok);
                    }
                    Some(Err(_)) => panic!("lex error in input: {}", input),
                    None => break,
                }
            }
        }
        tok_all_ok(r"\forall (x: X) -> Y => z");
        tok_all_ok(r"(x @ z # a");
        tok_all_ok(r"x $( y += z $)");
    }
    #[test]
    fn lexer_test() {
        fn print_and_unwrap(input: &'static str) {
            println!("Input: {:?}", input);
            let spantoks = &lex_all(input).unwrap();
            for tok in spantoks {
                println!("{:?}", tok);
            }
        }
        print_and_unwrap(r"\forall (x: X) -> Y => z");
        print_and_unwrap(r"x $( y + z $) l");
        print_and_unwrap(r"x mymacro!{ a + b c } l");
        print_and_unwrap(r"x /* this is a comment */ (y z)");
        print_and_unwrap(r"x :: y ++ := z");
        print_and_unwrap(r"\Prop \Set (0)");
        print_and_unwrap(r"(( $( $) ))");
        print_and_unwrap(r"x.y # name { hello: ");
    }

    #[test]
    fn malformed_declarations_do_not_end_optional_lists() {
        for input in [
            r"\definition f(x: A, y): A := x;",
            r"\module M(x: A, y) {}",
            r"\inductive T: \Set := | ctor: ; ;",
            r"\import M(x := ) \as Alias;",
            r"\import M(). \as Alias;",
        ] {
            let tokens = lex_all(input).unwrap();
            let mut parser = Parser::new(&tokens);
            let error = parser.try_parse_module_item().unwrap_err();
            assert!(error.start > 0, "lost failure position: {input}: {error:?}");
        }
        let input = r"\definition f: A := x";
        let tokens = lex_all(input).unwrap();
        let error = Parser::new(&tokens).try_parse_module_item().unwrap_err();
        assert_eq!((error.start, error.end), (input.len(), input.len()));
    }

    #[test]
    fn parse_rightbinds_test() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let binds = parser.parse_rightbinds().unwrap();
            println!("Parsed RightBinds: {:?} => {:?}", input, binds);
        }
        print_and_unwrap(r"(x: X)");
        print_and_unwrap(r"(x: X, y: Y, z: Z)");
        print_and_unwrap(r"(P1: \Prop,  p1: P1, )");
    }
    #[test]
    fn pares_ctor_decl_test() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let ctor = parser.parse_ctor_decl().unwrap();
            println!("Parsed CtorDecl: {:?} => {:?}", input, ctor);
        }
        print_and_unwrap(r"| true : Bool ;");
        print_and_unwrap(r"| succ : Nat -> Nat ;");
        print_and_unwrap(r"| u: A -> B -> U ;");
        print_and_unwrap(r"| cons : \forall (X : \Set) -> X -> List X -> List X ;");
    }
    #[test]
    fn parse_module_item() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let item = parser.try_parse_module_item();
            match item {
                Ok(Some(mi)) => {
                    println!("Parsed ModuleItem: {:?} => {:?}", input, mi);
                }
                Ok(None) => {
                    panic!("Failed to parse ModuleItem: {}", input);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap(r"\definition id : \forall (X : \Set) -> X -> X := \fun (x : X) => x ;");
        print_and_unwrap(r"\definition l : \forall (X : \Set) -> X -> X := \fun (x : X) => x ;");
        print_and_unwrap(
            r"\definition l: \forall (X, Y: \Set) -> \SetKind := \fun (_: \Set) => a;",
        );
        print_and_unwrap(r"\definition one: Nat := Nat::succ Nat::zero;");
        print_and_unwrap(r"\import MyModule () \as ImportedModule ;");
        print_and_unwrap(r"\import MyModule ( A := B, C := \fun (x: X) => y) \as T;");
        print_and_unwrap(r"\inductive Bool : \Set := | true : Bool ; | false : Bool ; ;");
        print_and_unwrap(r"\inductive Nat : \Set := | zero : Nat ; | succ : Nat -> Nat ; ;");
    }
}
