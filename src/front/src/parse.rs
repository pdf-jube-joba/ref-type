use crate::{parse::term_parse::TermParser, syntax::*};
use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Token<'a> {
    // Keywords (start from "\" character)
    #[regex(r"\\[a-zA-Z0-9]+")]
    KeyWord(&'a str), // any concatenation of non-alphanumeric symbols without spaces
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    Ident(&'a str),
    #[regex(r"[0-9]+")]
    Number(&'a str),
    #[regex(r"\?[a-zA-Z0-9_]*")]
    UnspecifiedVar(&'a str),
    // any non-space sequence that does not include backslash, alnum or '?()$'
    #[regex(r"[^\s\\A-Za-z0-9?(){}$\[\]]+")]
    MacroToken(&'a str),
    // special symbol tokens (which have their own meaning in parsing)
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("$(")]
    MathLParen,
    #[token(")$")]
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
    Field,
}

static SORT_KEYWORDS: &[&str] = &[
    "\\Prop",
    "\\PropKind",
    "\\Set",
    "\\SetKind",
    "\\Type",
    "\\TypeKind",
];

static EXPRESSION_ATOM_KEYWORDS: &[&str] = &[
    "\\elim", // inductive eliminator
    "\\prec", // eliminator as primitive recursive form
    "\\Proof", "\\Power", "\\Subset", "\\Pred", "\\Ty",     // usuals
    "\\exists", // \exists <Bind>
    "\\take",   // \take <Bind> => <body>
    "\\block",  // block expression
];

static EXPRESSION_SEPARATION_KEYWORDS: &[&str] =
    &["\\as", "\\with", "\\where", "\\in", "\\return", "\\goal"];

static BLOCK_KEYWORDS: &[&str] = &["\\let", "\\sufficient", "\\take", "\\fix"];

static PROOF_COMMAND_KEYWORDS: &[&str] = &[
    "\\term",
    "\\exact",
    "\\bysub",
    "\\refl",
    "\\idelim",
    "\\takeelim",
    "\\axiom:LEM",
    "\\axiom:FE",
    "\\axiom:EE",
];

static PROGRAM_KEYWORDS: &[&str] = &[
    "\\module",
    "\\import",
    "\\definition",
    "\\inductive",
    "\\mathmacro",
    "\\usermacro",
    "\\eval",
    "\\normalize",
    "\\check",
    "\\infer",
    "\\root",
    "\\parent",
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
                    "#" => Token::Field,
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
                let mapped = if !SORT_KEYWORDS.contains(&kw)
                    && !EXPRESSION_ATOM_KEYWORDS.contains(&kw)
                    && !EXPRESSION_SEPARATION_KEYWORDS.contains(&kw)
                    && !BLOCK_KEYWORDS.contains(&kw)
                    && !PROOF_COMMAND_KEYWORDS.contains(&kw)
                    && !PROGRAM_KEYWORDS.contains(&kw)
                {
                    // treat as macro token if not reserved keyword
                    Token::MacroToken(kw)
                } else {
                    Token::KeyWord(kw)
                };
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
            | Ok(
                Token::LParen
                | Token::RParen
                | Token::MathLParen
                | Token::MathRParen
                | Token::LBrace
                | Token::RBrace,
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

    #[allow(dead_code)]
    fn expect_number(&mut self) -> Result<usize, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Number(num_str) => match num_str.parse::<usize>() {
                    Ok(n) => Ok(n),
                    Err(_) => Err(ParseError {
                        msg: format!("invalid number: {}", num_str),
                        start: t.start,
                        end: t.end,
                    }),
                },
                other => Err(ParseError {
                    msg: format!("expected number, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("number")),
        }
    }

    #[allow(dead_code)]
    fn expect_othersymbol(&mut self) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::MacroToken(sym_str) => Ok(sym_str),
                other => Err(ParseError {
                    msg: format!("expected other symbol, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("other symbol")),
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
        let name = self.expect_ident()?;
        self.expect_token(Token::Colon)?;
        let ty = self.parse_sexp()?;
        self.expect_token(Token::Assign)?;
        let body = self.parse_sexp()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Definition { name, ty, body })
    }

    // (cosumed "\import" keyword) <path: ModuleAccessPath> "\as" <import_name: Ident> ";"
    fn parse_import(&mut self) -> Result<ModuleItem, ParseError> {
        let parent_num: Option<usize> = if self.bump_if_keyword("\\root") {
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

    // <specified_module: (Identifier, Vec<(Identifier, SExp)>)> = <mod_name> "(" (<param: Ident> ":=" <arg: SExp> ",")* ")"
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
        let sort = match expect_sort {
            SExp::Sort(s) => s,
            _ => {
                return Err(ParseError {
                    msg: "expected sort in inductive declaration".into(),
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
            sort,
            constructors,
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

    // parse a module
    // "\module" <module_name: Ident> ("(" (<param: Ident> ":" <ty: SExp> ",")* ")")? "{" (<module_item>)* "}"
    pub fn parse_module(&mut self) -> Result<Module, ParseError> {
        self.expect_keyword("\\module")?;
        let module_name = self.expect_ident()?;

        let parameters = self
            .try_parse(|parser| parser.parse_rightbinds())?
            .unwrap_or_default();

        self.expect_token(Token::LBrace)?; // expect '{'
        let mut declarations = Vec::new();
        while let Some(item) = self.try_parse_module_item()? {
            declarations.push(item);
        }
        self.expect_token(Token::RBrace)?; // expect '}'

        Ok(Module {
            name: module_name,
            parameters,
            declarations,
        })
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
        tok_all_ok(r"x $( y += z )$");
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
        print_and_unwrap(r"x $( y + z )$ l");
        print_and_unwrap(r"x ! mymacro { a + b c } l");
        print_and_unwrap(r"x /* this is a comment */ (y z)");
        print_and_unwrap(r"x :: y ++ := z");
        print_and_unwrap(r"\Prop \Set (0)");
        print_and_unwrap(r"(( $( )) )$");
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
        print_and_unwrap(r"\import MyModule () \as ImportedModule ;");
        print_and_unwrap(r"\import MyModule ( A := B, C := (x: X) => y) \as T;");
        print_and_unwrap(r"\inductive Bool : \Set := | true : Bool ; | false : Bool ; ;");
    }
}
