use crate::syntax::*;
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
    #[regex(r"\?[a-zA-Z_]+")]
    UnspecifiedVar(&'a str),
    // any non-space sequence that does not include backslash, alnum or '?()$'
    #[regex(r"[^\s\\A-Za-z0-9?(){}$]+")]
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
    // comment tokens (will be ignored in lexing)
    #[token("/*")]
    CommentStart,
    #[token("*/")]
    CommentEnd,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
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
    "\\check",
    "\\infer",
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

    /// Helper to parse a parenthesized expression.
    /// "(" <some: parse_inner> ")" where parse_inner is given as a closure.
    fn parse_parenthesized<F, T>(&mut self, parse_inner: F) -> Result<T, ParseError>
    where
        F: FnOnce(&mut Self) -> Result<T, ParseError>,
    {
        self.expect_token(Token::LParen)?; // expect '('
        let result = parse_inner(self)?;
        self.expect_token(Token::RParen)?; // expect ')'
        Ok(result)
    }

    // Try to parse a parenthesized number (e.g., "(0)").
    fn try_parse_parenthesized_number(&mut self) -> Result<Option<usize>, ParseError> {
        let save_pos = self.pos; // Save the current position for rollback.

        if self.bump_if_token(&Token::LParen)
            && let Ok(number) = self.expect_number()
            && self.bump_if_token(&Token::RParen)
        {
            return Ok(Some(number)); // Successfully parsed "(number)".
        }

        // Rollback if parsing failed.
        self.pos = save_pos;
        Ok(None)
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<kernel::exp::Sort, ParseError> {
        if self.bump_if_keyword("\\Prop") {
            return Ok(kernel::exp::Sort::Prop);
        }
        if self.bump_if_keyword("\\PropKind") {
            return Ok(kernel::exp::Sort::PropKind);
        }
        if self.bump_if_keyword("\\Set") {
            // check for optional parenthesized number
            if let Some(number) = self.try_parse_parenthesized_number()? {
                return Ok(kernel::exp::Sort::Set(number));
            }
            return Ok(kernel::exp::Sort::Set(0)); // Default to Set(0) if no number is provided.
        }
        if self.bump_if_keyword("\\SetKind") {
            // check for optional parenthesized number
            if let Some(number) = self.try_parse_parenthesized_number()? {
                return Ok(kernel::exp::Sort::SetKind(number));
            }
            return Ok(kernel::exp::Sort::SetKind(0)); // Default to SetKind(0) if no number is provided.
        }

        Err(ParseError {
            msg: "expected sort keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_keyword_head_atom(&mut self) -> Result<SExp, ParseError> {
        // simple cases (<keyword> "(" expressions with comma separated ")")
        if self.bump_if_keyword("\\Proof") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|term| SExp::ProveLater {
                    term: Box::new(term),
                })
            });
        }
        if self.bump_if_keyword("\\Power") {
            return self.parse_parenthesized(|parser| {
                parser
                    .parse_sexp()
                    .map(|set| SExp::PowerSet { set: Box::new(set) })
            });
        }
        if self.bump_if_keyword("\\Subset") {
            return self.parse_parenthesized(|parser| {
                let var = parser.expect_ident()?;
                parser.expect_token(Token::Comma)?;
                let set = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let predicate = parser.parse_sexp()?;
                Ok(SExp::SubSet {
                    var,
                    set: Box::new(set),
                    predicate: Box::new(predicate),
                })
            });
        }
        if self.bump_if_keyword("\\Pred") {
            return self.parse_parenthesized(|parser| {
                let superset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let element = parser.parse_sexp()?;
                Ok(SExp::Pred {
                    superset: Box::new(superset),
                    subset: Box::new(subset),
                    element: Box::new(element),
                })
            });
        }
        if self.bump_if_keyword("\\Ty") {
            return self.parse_parenthesized(|parser| {
                let superset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                Ok(SExp::TypeLift {
                    superset: Box::new(superset),
                    subset: Box::new(subset),
                })
            });
        }
        // elimination of inductive type
        if self.bump_if_keyword("\\elim") {
            // "\elim" <elim: SExp> "\in" <path: Path> "\\return" <return_type: SExp>
            let elim = self.parse_sexp()?;
            self.expect_keyword("\\in")?; // expect '\in'
            let path = self.parse_access_path()?;
            self.expect_keyword("\\return")?; // expect '\\return'
            let return_type = self.parse_sexp()?;

            // body of case branches
            let mut cases = Vec::new();
            self.expect_token(Token::LBrace)?; // expect '{'
            // loop until '}'
            while !self.bump_if_token(&Token::RBrace) {
                self.expect_token(Token::Pipe)?; // expect '|'
                let case_name = self.expect_ident()?; // expect case name
                self.expect_token(Token::DoubleArrow)?; // expect '=>'
                let case_type = self.parse_sexp()?; // parse case type
                self.expect_token(Token::Semicolon)?; // expect ';'
                cases.push((case_name, case_type));
            }

            return Ok(SExp::IndElim {
                path,
                elim: Box::new(elim),
                return_type: Box::new(return_type),
                cases,
            });
        }
        if self.bump_if_keyword("\\prec") {
            // "\prec" "(" <sort: Sort> "," <path: AccessPath> ")"
            self.expect_token(Token::LParen)?;
            let sort = self.parse_sort()?;
            self.expect_token(Token::Comma)?;
            let path = self.parse_access_path()?;
            self.expect_token(Token::RParen)?;

            return Ok(SExp::IndElimPrim { path, sort });
        }
        // "\exists" <binding>
        if self.bump_if_keyword("\\exists") {
            let bind = self.parse_left_arrow_head()?;
            return Ok(SExp::Exists { bind });
        }
        // "\take" <binding> "=>" <body>
        if self.bump_if_keyword("\\take") {
            let bind = self.parse_left_arrow_head()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let body = self.parse_sexp()?;
            return Ok(SExp::Take {
                bind,
                body: Box::new(body),
            });
        }
        if self.bump_if_keyword("\\block") {
            self.expect_token(Token::LBrace)?; // expect '{'
            let block = self.parse_block()?;
            self.expect_token(Token::RBrace)?; // expect '}'
            return Ok(SExp::Block(block));
        }

        Err(ParseError {
            msg: "expected expression starting with keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_proof_command(&mut self) -> Result<ProofBy, ParseError> {
        if self.bump_if_keyword("\\term") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(ProofBy::Construct {
                term: Box::new(term),
            });
        }

        if self.bump_if_keyword("\\exact") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::Comma)?; // expect ','
            let set = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(ProofBy::Exact {
                term: Box::new(term),
                set: Box::new(set),
            });
        }

        if self.bump_if_keyword("\\refl") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(ProofBy::IdRefl {
                term: Box::new(term),
            });
        }

        // \\idelim "(" <left: SExp> "=" <right: SExp> "\with" <var: Ident> ":" <ty: SExp> "=>" <predicate: SExp> ")"
        if self.bump_if_keyword("\\idelim") {
            self.expect_token(Token::LParen)?; // expect '('
            let left = self.parse_sexp()?;
            self.expect_token(Token::Equal)?; // expect '='
            let right = self.parse_sexp()?;
            self.expect_keyword("\\with")?; // expect '\with'
            let var = self.expect_ident()?;
            self.expect_token(Token::Colon)?; // expect ':'
            let ty = self.parse_sexp()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let predicate = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(ProofBy::IdElim {
                left: Box::new(left),
                right: Box::new(right),
                var,
                ty: Box::new(ty),
                predicate: Box::new(predicate),
            });
        }

        if self.bump_if_keyword("\\takeelim") {
            todo!("takeelim proof command not implemented yet");
        }

        Err(ParseError {
            msg: "expected expression starting with keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let mut statements = Vec::new();

        loop {
            if self.bump_if_keyword("\\fix") {
                // "\fix" ("(" RightBind ")" ",")* ";"
                let mut binds: Vec<RightBind> = Vec::new();
                while let Some(bind) = self.try_parse_simple_bind_paren()? {
                    binds.push(bind);
                    if !self.bump_if_token(&Token::Comma) {
                        break;
                    }
                }
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Fix(binds));
                continue;
            }

            if self.bump_if_keyword("\\let") {
                // "\let" <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
                let var = self.expect_ident()?;
                self.expect_token(Token::Colon)?; // expect ':'
                let ty = self.parse_sexp()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let body = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Let { var, ty, body });
                continue;
            }

            if self.bump_if_keyword("\\take") {
                // "\take" <bind: Bind> ";"
                let bind = self.parse_left_arrow_head()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Take { bind });
                continue;
            }

            if self.bump_if_keyword("\\return") {
                // "\return" <exp: SExp> ";"
                let result = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                return Ok(Block {
                    statements,
                    result: Box::new(result),
                });
            }

            break; // No more block statements.
        }

        Err(ParseError {
            msg: "expected block statement or \\return".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    // parse an access path
    // e.g. `x` or `x.y` or `x.y.z` or ...
    ///  or with parameter `x {<e0> "," ... ","  <en>}`
    fn parse_access_path(&mut self) -> Result<AccessPath, ParseError> {
        let mut path = Vec::new();

        // 1. expect first identifier
        let first_ident = self.expect_ident()?;
        path.push(first_ident);

        // 2. while next is '.', expect next identifier
        while self.bump_if_token(&Token::Period) {
            let next_ident = self.expect_ident()?;
            path.push(next_ident);
        }

        if self.bump_if_token(&Token::LBrace) {
            // parse parameters inside '{' ... '}'
            let mut params = Vec::new();
            loop {
                let param = self.parse_sexp()?;
                params.push(param);
                if !self.bump_if_token(&Token::Comma) {
                    break;
                }
            }
            self.expect_token(Token::RBrace)?; // expect '}'
            return Ok(AccessPath::WithParams {
                segments: path,
                parameters: params,
            });
        }

        Ok(AccessPath::Plain { segments: path })
    }

    // parse a single atom
    // e.g. `x`, `x.y`, `x.y.z`, `(x)`, `$( ... )$`, `! name { ... }`
    // or something start with keyword (sort, etc.)
    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            Some(Token::Ident(_)) => {
                let access_path = self.parse_access_path()?;
                Ok(SExp::AccessPath(access_path))
            }
            Some(Token::LParen) => {
                self.next(); // consume '('
                let expr = self.parse_sexp()?;
                self.expect_token(Token::RParen)?; // expect ')'
                Ok(expr)
            }
            Some(Token::MathLParen) => {
                self.next(); // consume '$('
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(Token::MathRParen)?; // expect ')$'
                Ok(SExp::MathMacro { tokens })
            }
            Some(Token::Exclamation) => {
                self.next(); // consume '!'
                let name = self.expect_ident()?;
                self.expect_token(Token::LBrace)?; // expect '{'
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(Token::RBrace)?; // expect '}'
                Ok(SExp::NamedMacro { name, tokens })
            }
            Some(Token::KeyWord(keyword)) if SORT_KEYWORDS.contains(keyword) => {
                // check if it's a reserved sort keyword
                self.parse_sort().map(SExp::Sort)
            }
            Some(Token::KeyWord(keyword)) if EXPRESSION_ATOM_KEYWORDS.contains(keyword) => {
                self.parse_keyword_head_atom()
            }
            Some(Token::KeyWord(keyword)) if PROOF_COMMAND_KEYWORDS.contains(keyword) => {
                Ok(SExp::ProofBy(self.parse_proof_command()?))
            }
            Some(Token::KeyWord(keyword)) => Err(ParseError {
                msg: format!("unexpected keyword in atom: {}", keyword),
                start: self.pos,
                end: self.pos,
            }),
            _ => Err(ParseError {
                msg: "expected atom".into(),
                start: self.pos,
                end: self.pos,
            }),
        }
    }

    // parse a sequence of atoms (AtomLike)
    // e.g. `x`, `(x)`, `x y`, `x (y z)`, `(x y) z`
    fn parse_atom_sequence(&mut self) -> Result<SExp, ParseError> {
        // 1. first atom
        let mut expr = self.parse_atom()?;

        loop {
            let save = self.pos;
            match self.parse_atom() {
                Ok(next_atom) => {
                    expr = SExp::App {
                        func: Box::new(expr),
                        arg: Box::new(next_atom),
                        piped: false,
                    };
                }
                Err(_) => {
                    // if not atom, rollback and break
                    self.pos = save;
                    break;
                }
            }
        }

        Ok(expr)
    }

    // parse a sequence splitted by pipes
    fn parse_piped_atom_sequence(&mut self) -> Result<SExp, ParseError> {
        // 1. parse first atom sequence
        let mut expr = self.parse_atom_sequence()?;
        // 2. while next is pipe, parse next atom sequence and combine
        while self.bump_if_token(&Token::Pipe) {
            let right = self.parse_atom_sequence()?;
            expr = SExp::App {
                arg: Box::new(expr),
                func: Box::new(right),
                piped: true,
            };
        }
        Ok(expr)
    }

    // parse "\\as" expression
    // <exp> \as <exp>
    fn parse_as_expression(&mut self) -> Result<SExp, ParseError> {
        let from_exp = self.parse_piped_atom_sequence()?;
        if self.bump_if_keyword("\\as") {
            let to_exp = self.parse_piped_atom_sequence()?;
            Ok(SExp::Cast {
                exp: Box::new(from_exp),
                to: Box::new(to_exp),
            })
        } else {
            Ok(from_exp)
        }
    }

    // pares "=" expression
    // <exp> = <exp>
    fn parse_equal_expression(&mut self) -> Result<SExp, ParseError> {
        let left_exp = self.parse_as_expression()?;
        if self.bump_if_token(&Token::Equal) {
            let right_exp = self.parse_as_expression()?;
            Ok(SExp::Equal {
                left: Box::new(left_exp),
                right: Box::new(right_exp),
            })
        } else {
            Ok(left_exp)
        }
    }

    // top level of not arrow expressions
    fn parse_combined(&mut self) -> Result<SExp, ParseError> {
        self.parse_equal_expression()
    }

    // Try to parse an annotation
    // Ident ("," Ident)* ":" SExp
    fn try_parse_annotate(&mut self) -> Result<Option<(Vec<Identifier>, SExp)>, ParseError> {
        let save_pos = self.pos;

        // 1. parse identifiers separated by commas
        let mut vars = vec![];
        loop {
            match self.expect_ident() {
                Ok(v) => vars.push(v),
                Err(_) => {
                    self.pos = save_pos;
                    return Ok(None);
                }
            }
            if !self.bump_if_token(&Token::Comma) {
                break;
            }
        }

        if vars.is_empty() {
            return Ok(None);
        }

        // 2. expect ":"
        if !self.bump_if_token(&Token::Colon) {
            self.pos = save_pos;
            return Ok(None);
        }

        // 3. parse the type
        let ty = match self.parse_sexp() {
            Ok(e) => e,
            Err(_) => {
                self.pos = save_pos;
                return Ok(None);
            }
        };

        Ok(Some((vars, ty)))
    }

    // "(" Ident ("," Ident) ":" SExp ")"
    fn try_parse_simple_bind_paren(&mut self) -> Result<Option<RightBind>, ParseError> {
        let save_pos = self.pos;

        // 1. [0] = LParen
        match self.next() {
            Some(t) if matches!(t.kind, Token::LParen) => {} // ok
            _ => {
                self.pos = save_pos;
                return Ok(None);
            }
        }

        // 2. [1..?n] = Ident ("," Ident)* where [?n] = ":"
        let mut vars = Vec::new();
        loop {
            match self.expect_ident() {
                Ok(v) => vars.push(v),
                Err(_) => {
                    self.pos = save_pos;
                    return Ok(None);
                }
            }
            if !self.bump_if_token(&Token::Comma) {
                break;
            }
        }

        // expect ":"
        if !self.bump_if_token(&Token::Colon) {
            self.pos = save_pos;
            return Ok(None);
        }
        // 2. [?n+1..?len-1] = SExp
        let ty = match self.parse_sexp() {
            Ok(e) => e,
            Err(_) => {
                self.pos = save_pos;
                return Ok(None);
            }
        };

        // 3. [?len] = RParen
        match self.next() {
            Some(t) if matches!(t.kind, Token::RParen) => Ok(Some(RightBind {
                vars,
                ty: Box::new(ty),
            })),
            _ => {
                // これは「バインダっぽく見えたのに閉じてない」ので、ちゃんとエラーを投げていい
                Err(ParseError {
                    msg: "expected ')' after binder".into(),
                    start: save_pos,
                    end: self.pos,
                })
            }
        }
    }

    // subset like bind
    // "(" "(" Ident ":" SExp ")" "|" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" Ident ":" SExp ")"
    fn try_parse_subsetbind(&mut self) -> Result<Option<Bind>, ParseError> {
        let save_pos = self.pos;

        // check "(" "(" <annotate> ... otherwise rollback
        if !self.bump_if_token(&Token::LParen) || !self.bump_if_token(&Token::LParen) {
            self.pos = save_pos;
            return Ok(None);
        }
        let Some((first_var, first_ty)) = self.try_parse_annotate()? else {
            self.pos = save_pos;
            return Ok(None);
        };

        // var should be exactly one ... Err
        if first_var.len() != 1 {
            self.pos = save_pos;
            return Err(ParseError {
                msg: "expected single identifier in subset bind".into(),
                start: self.pos,
                end: self.pos,
            });
        }

        let var = first_var.into_iter().next().unwrap();

        // there is "(" "(" <annot> ")" ... now ")" and "|" expected
        self.expect_token(Token::RParen)?;
        self.expect_token(Token::Pipe)?;

        // case 1: Ident ":" SExp
        if let Some((back_var, back_ty)) = self.try_parse_annotate()? {
            self.expect_token(Token::RParen)?; // expect closing ')'

            if back_var.len() != 1 {
                return Err(ParseError {
                    msg: "expected single identifier in proof annotation".into(),
                    start: self.pos,
                    end: self.pos,
                });
            };
            let pred_var = back_var.into_iter().next().unwrap();

            return Ok(Some(Bind::SubsetWithProof {
                var,
                ty: Box::new(first_ty),
                predicate: Box::new(back_ty),
                proof_var: pred_var,
            }));
        }

        // case 2: SExp
        let pred_ty = self.parse_sexp()?;

        self.expect_token(Token::RParen)?; // expect closing ')'
        Ok(Some(Bind::Subset {
            var,
            ty: Box::new(first_ty),
            predicate: Box::new(pred_ty),
        }))
    }

    // binder complex case
    // "(" Ident ":"" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" Ident ":" SExp ")"
    fn try_parse_complex_bind(&mut self) -> Result<Option<Bind>, ParseError> {
        let save_pos = self.pos;

        // try subset bind first
        // "(" "("
        if let Some(bind) = self.try_parse_subsetbind()? {
            return Ok(Some(bind));
        }

        // try simple bind next
        // "("
        if let Some(bind) = self.try_parse_simple_bind_paren()? {
            return Ok(Some(Bind::Named(bind)));
        }
        // rollback if neither worked
        self.pos = save_pos;
        Ok(None)
    }

    // parse an arrow expression
    // e.g. `bind -> x` or `bind => x` or just piped atom sequence
    fn parse_arrow_expr(&mut self) -> Result<SExp, ParseError> {
        let left_head = self.parse_left_arrow_head()?;

        if self.bump_if_token(&Token::Arrow) {
            let right = self.parse_sexp()?;
            return Ok(SExp::Prod {
                bind: left_head,
                body: Box::new(right),
            });
        }

        if self.bump_if_token(&Token::DoubleArrow) {
            let right = self.parse_sexp()?;
            return Ok(SExp::Lam {
                bind: left_head,
                body: Box::new(right),
            });
        }

        match left_head {
            Bind::Anonymous { ty } => Ok(*ty),
            _ => Err(ParseError {
                msg: "expected '->' or '=>' after bind".into(),
                start: self.pos,
                end: self.pos,
            }),
        }
    }

    // parse the left-hand side of an arrow expression
    // may be a bind or a simple expression or a parenthesized expression
    // e.g. `x y -> z`, `(x y) -> z`, `(x: y) -> z`, `((x: y) | P) -> z`
    fn parse_left_arrow_head(&mut self) -> Result<Bind, ParseError> {
        // 1. try to parse complex bind first
        if let Some(bind) = self.try_parse_complex_bind()? {
            return Ok(bind);
        }

        // 2. otherwise, parse simple expression as a bind
        let expr = self.parse_combined()?;
        Ok(Bind::Anonymous { ty: Box::new(expr) })
    }

    pub fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        let sexp = self.parse_arrow_expr()?;
        if self.bump_if_keyword("\\with") {
            // \\with "{" ("\\goal" <simple_bind_parend>* ":" <sexp> ":=" <sexp> ";" )* "}"
            self.expect_token(Token::LBrace)?; // expect '{'
            let mut proofs = vec![];
            while self.bump_if_keyword("\\goal") {
                // parse iteration of <simple_bind_parend>*
                let mut binds = vec![];
                while let Some(bind) = self.try_parse_simple_bind_paren()? {
                    binds.push(bind);
                }
                self.expect_token(Token::Colon)?;
                let goal = self.parse_sexp()?;
                self.expect_token(Token::Assign)?;
                let proofby = self.parse_proof_command()?;
                self.expect_token(Token::Semicolon)?;
                proofs.push(GoalProof {
                    extended_ctx: binds,
                    goal,
                    proofby,
                });
            }
            self.expect_token(Token::RBrace)?; // expect '}'
            Ok(SExp::WithProofs {
                exp: Box::new(sexp),
                proofs,
            })
        } else {
            Ok(sexp)
        }
    }

    pub fn try_parse_sexp(&mut self) -> Result<Option<SExp>, ParseError> {
        let save_pos = self.pos;
        match self.parse_sexp() {
            Ok(exp) => Ok(Some(exp)),
            Err(_) => {
                self.pos = save_pos;
                Ok(None)
            }
        }
    }

    // parse marco tokens
    fn parse_one_macro(&mut self) -> Result<MacroExp, ParseError> {
        // 1, challenge atom
        if let Ok(atom) = self.parse_atom() {
            return Ok(MacroExp::Exp(atom));
        }
        // 2. challenge one macro token
        // OthetSymbolStart or KeyWord which is not contained in *_KEYWORDS
        if let Some(Token::MacroToken(_)) = self.peek() {
            let sym = self.expect_othersymbol()?;
            return Ok(MacroExp::Tok(MacroToken(sym.to_string())));
        }
        // 3. Parended sequence of macro tokens
        if self.bump_if_token(&Token::LParen) {
            let mut exps = Vec::new();
            while !self.bump_if_token(&Token::RParen) {
                let exp = self.parse_one_macro()?;
                exps.push(exp);
            }
            return Ok(MacroExp::Seq(exps));
        }
        Err(ParseError {
            msg: "expected macro expression".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    // "\definition" <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
    fn parse_definition(&mut self) -> Result<ModuleItem, ParseError> {
        self.expect_keyword("\\definition")?;
        let name = self.expect_ident()?;
        self.expect_token(Token::Colon)?;
        let ty = self.parse_sexp()?;
        self.expect_token(Token::Assign)?;
        let body = self.parse_sexp()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Definition { name, ty, body })
    }

    // "\import" <module_name: Ident> "(" (<param: Ident> ":=" <arg: SExp> ",")* ")" "\as" <import_name: Ident> ";"
    fn parse_import(&mut self) -> Result<ModuleItem, ParseError> {
        // 1. "\import" <module_name: Ident> "("
        self.expect_keyword("\\import")?;
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

        // 3. "\as" <import_name: Ident> ";"
        self.expect_keyword("\\as")?;
        let import_name = self.expect_ident()?;
        self.expect_token(Token::Semicolon)?;

        Ok(ModuleItem::Import {
            import_name,
            path: ModuleInstantiated {
                module_name,
                arguments: assign_pairs,
            },
        })
    }

    // "|" <ctor_name: Ident> ":" <ctor_type: SExp> ";"
    fn parse_ctor_decl(&mut self) -> Result<(Identifier, SExp), ParseError> {
        self.expect_token(Token::Pipe)?; // expect '|'
        let ctor_name = self.expect_ident()?;
        self.expect_token(Token::Colon)?; // expect ':'
        let ctor_type = self.parse_sexp()?;
        self.expect_token(Token::Semicolon)?; // expect ';'
        Ok((ctor_name, ctor_type))
    }

    // "\inductive" <type_name: Ident> ("(" <param: Ident> ":" <ty: SExp> ")")* ":" <arity: SExp> ":=" (<ctor_decl>)* ";"
    fn parse_inductive_decl(&mut self) -> Result<ModuleItem, ParseError> {
        self.expect_keyword("\\inductive")?;
        let type_name = self.expect_ident()?;

        let mut parameters = vec![];
        while let Some(bind) = self.try_parse_simple_bind_paren()? {
            parameters.push(bind);
        }
        self.expect_token(Token::Colon)?;
        let arity = self.parse_sexp()?;

        // body of constructors
        self.expect_token(Token::Assign)?;
        let mut constructors = vec![];
        loop {
            let save_pos = self.pos;
            if let Ok((ctor_name, ctor_type)) = self.parse_ctor_decl() {
                constructors.push((ctor_name, ctor_type));
            } else {
                self.pos = save_pos;
                break;
            }
        }
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Inductive {
            type_name,
            parameters,
            arity,
            constructors,
        })
    }

    pub fn try_parse_module_item(&mut self) -> Result<Option<ModuleItem>, ParseError> {
        let save_pos = self.pos;
        match self.peek() {
            Some(Token::KeyWord(kw)) if *kw == "\\definition" => {
                let def = self.parse_definition()?;
                Ok(Some(def))
            }
            Some(Token::KeyWord(kw)) if *kw == "\\import" => {
                let imp = self.parse_import()?;
                Ok(Some(imp))
            }
            Some(Token::KeyWord(kw)) if *kw == "\\inductive" => {
                let ind = self.parse_inductive_decl()?;
                Ok(Some(ind))
            }
            Some(Token::KeyWord(kw)) if *kw == "\\eval" => {
                self.next();
                let exp = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?;
                Ok(Some(ModuleItem::Eval { exp }))
            }
            Some(Token::KeyWord(kw)) if *kw == "\\check" => {
                self.next();
                let exp = self.parse_sexp()?;
                self.expect_token(Token::Colon)?;
                let ty = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?;
                Ok(Some(ModuleItem::Check { exp, ty }))
            }
            Some(Token::KeyWord(kw)) if *kw == "\\infer" => {
                self.next();
                let exp = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?;
                Ok(Some(ModuleItem::Infer { exp }))
            }
            _ => {
                self.pos = save_pos;
                Ok(None)
            }
        }
    }

    // parse a module
    // "\module" <module_name: Ident> ("(" (<param: Ident> ":" <ty: SExp> ",")* ")")? "{" (<module_item>)* "}"
    pub fn parse_module(&mut self) -> Result<Module, ParseError> {
        self.expect_keyword("\\module")?;
        let module_name = self.expect_ident()?;

        let mut parameters = Vec::new();
        if self.bump_if_token(&Token::LParen) {
            while !self.bump_if_token(&Token::RParen) {
                let Some((vars, ty)) = self.try_parse_annotate()? else {
                    return Err(ParseError {
                        msg: "expected parameter annotation in module parameter list".into(),
                        start: self.pos,
                        end: self.pos,
                    });
                };
                parameters.push(RightBind {
                    vars,
                    ty: Box::new(ty),
                });

                if !self.bump_if_token(&Token::Comma) {
                    self.expect_token(Token::RParen)?; // ensure closing parenthesis
                    break;
                }
            }
        }

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
    fn parse_annotate_test() {
        fn print_and_unwrap_annotate(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for annotate test");
            let mut parser = Parser::new(lex);
            let result = parser.try_parse_annotate();
            match result {
                Ok(Some((var, ty))) => {
                    println!("Parsed SExp: {:?} => {:?}: {:?}", input, var, ty);
                }
                Ok(None) => {
                    panic!("Failed to parse annotate: {}", input);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_annotate(r"x: X");
        print_and_unwrap_annotate(r"y: (A -> B)");
        print_and_unwrap_annotate(r"x: X Y | h");
        print_and_unwrap_annotate(r"x, y, z: X -> Y");
    }

    #[test]
    fn parse_bind_test() {
        fn print_and_unwrap_complex_bind(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for complex bind test");
            let mut parser = Parser::new(lex);
            let result = parser.try_parse_complex_bind();
            match result {
                Ok(Some(bind)) => {
                    println!("Parsed SExp: {:?} => {:?}", input, bind);
                }
                Ok(None) => {
                    panic!("Failed to parse complex bind: {}", input);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_complex_bind(r"(x: X)");
        print_and_unwrap_complex_bind(r"((x: X) | P)");
        print_and_unwrap_complex_bind(r"((x: X) | p1 p2)");
        print_and_unwrap_complex_bind(r"((x: X) | h: p1 p2)");
    }
    #[test]
    fn parse_exp_test() {
        fn print_and_unwrap(input: &'static str) {
            let result = str_parse_exp(input);
            match result {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}", input, atomlike);
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        // identifier and lambda calcluluses
        print_and_unwrap(r"x");
        print_and_unwrap(r"x y");
        print_and_unwrap(r"x (y z)");
        print_and_unwrap(r"(x y) z");
        print_and_unwrap(r"x | y");
        print_and_unwrap(r"x | f");
        print_and_unwrap(r"x x | y u | f g");
        print_and_unwrap(r"(x: X) -> Y");
        print_and_unwrap(r"(x: X) => y");
        print_and_unwrap(r"(x: X) -> Y => z");
        print_and_unwrap(r"X -> Z");
        print_and_unwrap(r"x y z -> Y");
        print_and_unwrap(r"(x y) -> Y");
        print_and_unwrap(r"x y | z -> Y");
        print_and_unwrap(r"(x: X) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: X) | P) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: X) | h: P) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: P y | F) | h: (u | a) | b ) -> (y: Y) -> Z");
        print_and_unwrap(r"(X -> Y) Z ((t: T) => z)");
    }
    #[test]
    fn parse_special_exp_test() {
        fn print_and_unwrap(input: &'static str) {
            let result = str_parse_exp(input);
            match result {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}", input, atomlike);
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        // atom like: sort, access path, math macro, named macro
        print_and_unwrap("x");
        print_and_unwrap(r"\Prop");
        print_and_unwrap(r"\Set");
        print_and_unwrap(r"\Set(3)");
        print_and_unwrap(r"\Set(3) x");
        print_and_unwrap(r"x \Set(3)");
        print_and_unwrap(r"x.y.z");
        print_and_unwrap(r"x.a b (c. g)");
        print_and_unwrap(r"x $( y + z )$ l");
        print_and_unwrap(r"x ! mymacro { a + b c } l");
        // parse as, equal
        print_and_unwrap(r"x \as Y");
        print_and_unwrap(r"x = y");
        print_and_unwrap(r"x \as Y | z = h");
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
