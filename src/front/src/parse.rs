use crate::{parse::term_parse::TermParser, syntax::*};
use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Token<'a> {
    // Keywords (start from "\" character)
    #[regex(r"\\[a-zA-Z][a-zA-Z0-9-]*")]
    KeyWord(&'a str), // any concatenation of non-alphanumeric symbols without spaces
    #[regex(r"\$[a-zA-Z][a-zA-Z0-9_]*")]
    MacroVar(&'a str),
    #[regex(r#""[^"\n]*""#)]
    QuotedMacroToken(&'a str),
    #[regex(r"\\[^a-zA-Z0-9\s(){}$\[\]_,]+")]
    EscapedMacroToken(&'a str),
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
    MacroToken(&'a str),
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
    Arrow,       // "->"
    DoubleArrow, // "=>"
    Assign,      // ":="
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
    "\\VType",
    "\\Type",
    "\\U",
    "\\F",
    "\\CFun",
    "\\thunk",
    "\\return",
    "\\force",
    "\\clam",
    "\\capp",
    "\\sequence",
    "\\vlet",
    "\\vcase",
    "\\RunStep",
    "\\continue",
    "\\finish",
    "\\Acc",
    "\\RfType",
    "\\RfTerm",
    "\\run",
    "\\runCase",
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

pub fn lex_all<'a>(input: &'a str) -> Result<Vec<SpannedToken<'a>>, String> {
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
            Ok(Token::MacroToken(s)) => {
                // map known symbol sequences to specific token variants
                let mapped = match s {
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
                    _ => Token::MacroToken(s),
                };

                let span = lexer.span();
                out.push(SpannedToken {
                    kind: mapped,
                    start: span.start,
                    end: span.end,
                });
            }
            Ok(Token::KeyWord(kw)) => {
                let mapped = Token::KeyWord(kw);
                let span = lexer.span();
                out.push(SpannedToken {
                    kind: mapped,
                    start: span.start,
                    end: span.end,
                });
            }
            Ok(Token::Ident(_))
            | Ok(Token::Number(_))
            | Ok(Token::UnspecifiedVar(_))
            | Ok(Token::MacroVar(_))
            | Ok(Token::QuotedMacroToken(_))
            | Ok(Token::EscapedMacroToken(_))
            | Ok(Token::Hole)
            | Ok(
                Token::LParen
                | Token::RParen
                | Token::MathLParen
                | Token::MathRParen
                | Token::LBrace
                | Token::RBrace
                | Token::LBracket
                | Token::RBracket,
            ) => {
                let span = lexer.span();
                out.push(SpannedToken {
                    kind: tok.unwrap(),
                    start: span.start,
                    end: span.end,
                });
            }
            Ok(_) => {
                unreachable!("logos does not produce other tokens here");
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

#[derive(Debug, Clone)]
pub struct SpannedToken<'a> {
    pub kind: Token<'a>,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub start: usize,
    pub end: usize,
}

impl ParseError {
    fn eof_error(expect: &str) -> Self {
        Self {
            msg: format!("expected {}, found <eof>", expect),
            start: 0,
            end: 0,
        }
    }
}

mod term_parse;

#[derive(Debug)]
pub struct Parser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
}

// `fn bump_if_*` consumes tokens only if matched
// `fn parse_*` consumes tokens whether succeed or fail, the parser position is advanced
// `fn try_parse_*` consumes tokens only if matched, otherwise rollbacks
impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<&SpannedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn bump_if_token(&mut self, expect: &Token<'a>) -> bool
    where
        Token<'a>: PartialEq,
    {
        if let Some(tok) = self.peek()
            && tok == expect
        {
            self.pos += 1;
            return true;
        }
        false
    }

    fn bump_if_keyword(&mut self, kw: &str) -> bool {
        if let Some(Token::KeyWord(s)) = self.peek()
            && *s == kw
        {
            self.pos += 1;
            return true;
        }
        false
    }

    fn expect_token(&mut self, expect: Token<'a>) -> Result<SpannedToken<'a>, ParseError> {
        if let Some(t) = self.tokens.get(self.pos) {
            if t.kind == expect {
                self.pos += 1;
                Ok(t.clone())
            } else {
                Err(ParseError {
                    msg: format!("expected {:?}, found {:?}", expect, t.kind),
                    start: t.start,
                    end: t.end,
                })
            }
        } else {
            Err(ParseError::eof_error(&format!("{:?}", expect)))
        }
    }

    fn expect_keyword<'b>(&mut self, kw: &'b str) -> Result<&'a str, ParseError>
    where
        'b: 'a,
    {
        match self.next() {
            Some(t) => match &t.kind {
                Token::KeyWord(name) if *name == kw => Ok(*name),
                other => Err(ParseError {
                    msg: format!("expected keyword {kw}, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("keyword")),
        }
    }

    fn expect_ident(&mut self) -> Result<Identifier, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Ident(name) => Ok(Identifier((*name).to_string())),
                other => Err(ParseError {
                    msg: format!("expected identifier, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("identifier")),
        }
    }

    // Try to parse with the given parsing function.
    // ... rollbacks on failure.
    fn try_parse<T, F>(&mut self, parse_fn: F) -> Result<Option<T>, ParseError>
    where
        F: Fn(&mut Self) -> Result<T, ParseError>,
    {
        let save_pos = self.pos;
        match parse_fn(self) {
            Ok(result) => Ok(Some(result)),
            Err(_) => {
                self.pos = save_pos; // rollback
                Ok(None)
            }
        }
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
        while let Some(binders) = self.try_parse(|p| p.parse_rightbinds())? {
            first_binders.extend(binders);
        }
        let (owner, name, binders) = if self.bump_if_token(&Token::DoubleColon) {
            let name = self.expect_ident()?;
            let mut binders = Vec::new();
            while let Some(parsed) = self.try_parse(|p| p.parse_rightbinds())? {
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

    fn parse_structure_decl(&mut self) -> Result<ModuleItem, ParseError> {
        let type_name = self.expect_ident()?;
        let mut parameters = Vec::new();
        while let Some(parsed) = self.try_parse(|p| p.parse_rightbinds())? {
            parameters.extend(parsed);
        }
        self.expect_token(Token::Colon)?;
        let result = self.parse_sexp()?;
        let kind = match result {
            SExp::Sort(sort) => StructureKind::Pts(sort),
            SExp::ValueType => StructureKind::Program,
            _ => {
                return Err(ParseError {
                    msg: "expected PTS sort or \\Type in structure declaration".into(),
                    start: 0,
                    end: 0,
                });
            }
        };
        self.expect_token(Token::Assign)?;
        self.expect_token(Token::LBrace)?;
        let mut fields = Vec::new();
        while !self.bump_if_token(&Token::RBrace) {
            let name = self.expect_ident()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            fields.push((name, ty));
            if self.bump_if_token(&Token::RBrace) {
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

        while let Some((mod_name, args)) = self.try_parse(|p| p.parse_module_access_path())? {
            calls.push((mod_name, args));

            if !self.bump_if_token(&Token::Period) {
                break;
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
        if !self.bump_if_token(&Token::RParen) {
            loop {
                let param = self.expect_ident()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let arg = self.parse_sexp()?;
                assign_pairs.push((param, arg));

                if self.bump_if_token(&Token::RParen) {
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

        while let Some(param) = self.try_parse(|p| p.parse_rightbinds())? {
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
                    start: 0,
                    end: 0,
                });
            }
            _ => {
                return Err(ParseError {
                    msg: "expected PTS sort or \\VType in inductive declaration".into(),
                    start: 0,
                    end: 0,
                });
            }
        };

        // body of constructors
        self.expect_token(Token::Assign)?;
        let mut constructors = vec![];
        loop {
            let save_pos = self.pos;
            if let Ok((ctor_name, ctor_type, ends)) = self.parse_ctor_decl() {
                constructors.push((ctor_name, ctor_type, ends));
            } else {
                self.pos = save_pos;
                break;
            }
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
                kind: Token::EscapedMacroToken(token),
                ..
            }) => Ok(MacroSeqAtom::Tok(MacroToken(token[1..].to_string()))),
            Some(SpannedToken {
                kind: Token::QuotedMacroToken(token),
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
            None => Err(ParseError::eof_error("macro pattern atom")),
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

    pub fn try_parse_module_item(&mut self) -> Result<Option<ModuleItem>, ParseError> {
        let save_pos = self.pos;
        if self.bump_if_keyword("\\definition") {
            let def = self.parse_definition()?;
            return Ok(Some(def));
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
        self.pos = save_pos;
        Ok(None)
    }

    // parse an inline or external module
    // "\module" <module_name: Ident> <parameters>? ("{" (<module_item>)* "}" | ";")
    pub fn parse_module(&mut self) -> Result<Module, ParseError> {
        self.expect_keyword("\\module")?;
        let module_name = self.expect_ident()?;

        let parameters = self
            .try_parse(|parser| parser.parse_rightbinds())?
            .unwrap_or_default();

        let body = if self.bump_if_token(&Token::Semicolon) {
            ModuleBody::External
        } else {
            self.expect_token(Token::LBrace)?; // expect '{'
            let declarations = self.parse_module_items()?;
            self.expect_token(Token::RBrace)?; // expect '}'
            ModuleBody::Inline(declarations)
        };

        Ok(Module {
            name: module_name,
            parameters,
            body,
        })
    }

    fn parse_module_items(&mut self) -> Result<Vec<ModuleItem>, ParseError> {
        let mut declarations = Vec::new();
        while let Some(item) = self.try_parse_module_item()? {
            declarations.push(item);
        }
        Ok(declarations)
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
    let v = lex_all(input)?;
    let mut parser = Parser::new(&v);
    let mut modules = Vec::new();

    while parser.pos < parser.tokens.len() {
        let module = parser
            .parse_module()
            .map_err(|e| format!("parse error: {} ({}..{})", e.msg, e.start, e.end))?;
        modules.push(module);
    }

    Ok(modules)
}

/// Parse an external module file. Its contents are the module body directly.
pub fn str_parse_module_items(input: &str) -> Result<Vec<ModuleItem>, String> {
    let v = lex_all(input)?;
    let mut parser = Parser::new(&v);
    let declarations = parser
        .parse_module_items()
        .map_err(|e| format!("parse error: {} ({}..{})", e.msg, e.start, e.end))?;

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
        tok_all_ok(r"(x: X) -> Y => z");
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
        print_and_unwrap(r"(x: X) -> Y => z");
        print_and_unwrap(r"x $( y + z $) l");
        print_and_unwrap(r"x mymacro!{ a + b c } l");
        print_and_unwrap(r"x /* this is a comment */ (y z)");
        print_and_unwrap(r"x :: y ++ := z");
        print_and_unwrap(r"\Prop \Set (0)");
        print_and_unwrap(r"(( $( $) ))");
        print_and_unwrap(r"x.y # name { hello: ");
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
        print_and_unwrap(r"| cons : (X : \Set) -> X -> List X -> List X ;");
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
        print_and_unwrap(r"\definition id : (X : \Set) -> X -> X := (x : X) => x ;");
        print_and_unwrap(r"\definition l : (X : \Set) -> X -> X := (x : X) => x ;");
        print_and_unwrap(r"\definition l: (X, Y: \Set) -> \SetKind := \Set => a;");
        print_and_unwrap(r"\definition one: Nat := Nat::succ Nat::zero;");
        print_and_unwrap(r"\import MyModule () \as ImportedModule ;");
        print_and_unwrap(r"\import MyModule ( A := B, C := (x: X) => y) \as T;");
        print_and_unwrap(r"\inductive Bool : \Set := | true : Bool ; | false : Bool ; ;");
        print_and_unwrap(r"\inductive Nat : \Set := | zero : Nat ; | succ : Nat -> Nat ; ;");
    }
}
