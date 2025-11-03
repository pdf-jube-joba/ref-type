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
    #[regex(r#"[#%&"'~\+\^\*<>@\[\]/][^\s]*|:[^\s=]+|-[^\s>]+|=[^\s>]+"#)]
    OtherSymbolStart(&'a str),
    #[regex(r"\?[a-zA-Z_]+")]
    UnSPecifiedVar,
    // symbols of 2 or more characters
    #[token("->")]
    Arrow,
    #[token("=>")]
    DoubleArrow,
    #[token(":=")]
    Assign,
    #[token("$(")]
    MathLParen,
    #[token(")$")]
    MathRParen,
    // symbols of 1 character
    #[token("|")]
    Pipe,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(".")]
    Period,
    #[token(",")]
    Comma,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("=")]
    Equal,
    #[token("!")]
    Exclamation,
}

static RESERVED_SORT_KEYWORDS: &[&str] = &[
    "\\Prop",
    "\\PropKind",
    "\\Set",
    "\\SetKind",
    "\\Type",
    "\\TypeKind",
];

static EXPRESSION_KEYWORDS: &[&str] = &["\\fix", "\\as"];

static PROGRAM_KEYWORDS: &[&str] = &[
    "\\module",
    "\\import",
    "\\definition",
    "\\inductive",
    "\\mathmacro",
    "\\usermacro",
];

#[derive(Debug, Clone)]
pub struct SpannedToken<'a> {
    pub kind: Token<'a>,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug)]
pub struct Parser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
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

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_n(&self, n: usize) -> Option<&Token<'a>> {
        self.tokens.get(self.pos + n).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<&SpannedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn bump_if(&mut self, expect: &Token<'a>) -> bool
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

    fn bump_keyword(&mut self, kw: &str) -> bool {
        if let Some(Token::KeyWord(s)) = self.peek()
            && *s == kw
        {
            self.pos += 1;
            return true;
        }
        false
    }

    fn expect_token(&mut self, expect: &Token<'a>) -> Result<SpannedToken<'a>, ParseError> {
        if let Some(t) = self.tokens.get(self.pos) {
            if &t.kind == expect {
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

    fn expect_keyword(&mut self) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::KeyWord(name) => Ok(*name),
                other => Err(ParseError {
                    msg: format!("expected keyword, found {:?}", other),
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
                Token::OtherSymbolStart(sym_str) => Ok(sym_str),
                other => Err(ParseError {
                    msg: format!("expected other symbol, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("other symbol")),
        }
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<kernel::exp::Sort, ParseError> {
        if self.bump_keyword("\\Prop") {
            return Ok(kernel::exp::Sort::Prop);
        }
        if self.bump_keyword("\\PropKind") {
            return Ok(kernel::exp::Sort::PropKind);
        }
        if self.bump_keyword("\\Set") {
            // check for optional ["(", <number>, ..]
            if let (Some(Token::LParen), Some(Token::Number(_))) = (self.peek(), self.peek_n(1)) {
                self.next(); // consume '('
                let n = self.expect_number()?;
                self.expect_token(&Token::RParen)?;
                return Ok(kernel::exp::Sort::Set(n));
            } else {
                return Ok(kernel::exp::Sort::Set(0));
            }
        }
        if self.bump_keyword("\\SetKind") {
            // check for optional ["(", <number>, ..]
            if let (Some(Token::LParen), Some(Token::Number(_))) = (self.peek(), self.peek_n(1)) {
                self.next(); // consume '('
                let n = self.expect_number()?;
                self.expect_token(&Token::RParen)?;
                return Ok(kernel::exp::Sort::SetKind(n));
            } else {
                return Ok(kernel::exp::Sort::SetKind(0));
            }
        }

        Err(ParseError {
            msg: "expected sort keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    // parse an access path
    // e.g. `x` or `x.y` or `x.y.z` or ...
    fn parse_access_path(&mut self) -> Result<SExp, ParseError> {
        let mut path = Vec::new();

        // 1. expect first identifier
        let first_ident = self.expect_ident()?;
        path.push(first_ident);

        // 2. while next is '.', expect next identifier
        while self.bump_if(&Token::Period) {
            let next_ident = self.expect_ident()?;
            path.push(next_ident);
        }

        Ok(SExp::AccessPath(path))
    }

    // parse a single atom
    // e.g. `x`, `x.y`, `x.y.z`, `(x)`, `$( ... )$`, `! name { ... }`
    // or something start with keyword (sort, etc.)
    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            Some(Token::Ident(_)) => {
                let access_path = self.parse_access_path()?;
                Ok(access_path)
            }
            Some(Token::LParen) => {
                self.next(); // consume '('
                let expr = self.parse_sexp()?;
                self.expect_token(&Token::RParen)?; // expect ')'
                Ok(expr)
            }
            Some(Token::MathLParen) => {
                self.next(); // consume '$('
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(&Token::MathRParen)?; // expect ')$'
                Ok(SExp::MathMacro { tokens })
            }
            Some(Token::Exclamation) => {
                self.next(); // consume '!'
                let name = self.expect_ident()?;
                self.expect_token(&Token::LBrace)?; // expect '{'
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(&Token::RBrace)?; // expect '}'
                Ok(SExp::NamedMacro { name, tokens })
            }
            Some(Token::KeyWord(keyword)) => {
                // check if it's a reserved sort keyword
                if RESERVED_SORT_KEYWORDS.contains(keyword) {
                    let sort = self.parse_sort()?;
                    return Ok(SExp::Sort(sort));
                }
                Err(ParseError {
                    msg: format!("unexpected keyword in atom: {}", keyword),
                    start: self.pos,
                    end: self.pos,
                })
            }
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
        while self.bump_if(&Token::Pipe) {
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
        if self.bump_keyword("\\as") {
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
        if self.bump_if(&Token::Equal) {
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
    // Ident ":" SExp
    fn try_parse_annotate(&mut self) -> Result<Option<(Identifier, SExp)>, ParseError> {
        let save_pos = self.pos;

        // 1. [0] = Ident
        let var = match self.expect_ident() {
            Ok(v) => v,
            Err(_) => {
                self.pos = save_pos;
                return Ok(None);
            }
        };

        // 2. [1] = ":"
        if !self.bump_if(&Token::Colon) {
            self.pos = save_pos;
            return Ok(None);
        }

        // 3. [2..?len] = SExp
        let ty = match self.parse_sexp() {
            Ok(e) => e,
            Err(_) => {
                self.pos = save_pos;
                return Ok(None);
            }
        };

        Ok(Some((var, ty)))
    }

    // "(" Ident ":" SExp ")"
    fn try_parse_simple_bind_paren(&mut self) -> Result<Option<(Identifier, SExp)>, ParseError> {
        let save_pos = self.pos;

        // 1. [0] = LParen
        match self.next() {
            Some(t) if matches!(t.kind, Token::LParen) => {} // ok
            _ => {
                self.pos = save_pos;
                return Ok(None);
            }
        }

        // 2. [..?len] = binder
        let (var, ty) = match self.try_parse_annotate()? {
            Some(pair) => pair,
            None => {
                // （他の可能性があるので）rollback する
                self.pos = save_pos;
                return Ok(None);
            }
        };

        // 3. [?len] = RParen
        match self.next() {
            Some(t) if matches!(t.kind, Token::RParen) => Ok(Some((var, ty))),
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
        if !self.bump_if(&Token::LParen) || !self.bump_if(&Token::LParen) {
            self.pos = save_pos;
            return Ok(None);
        }
        let Some((var, ty)) = self.try_parse_annotate()? else {
            self.pos = save_pos;
            return Ok(None);
        };

        // there is "(" "(" <annot> ")" ... now ")" and "|" expected
        self.expect_token(&Token::RParen)?;
        self.expect_token(&Token::Pipe)?;

        // case 1: Ident ":" SExp
        if let Some((proof, pred_ty)) = self.try_parse_annotate()? {
            self.expect_token(&Token::RParen)?; // expect closing ')'
            return Ok(Some(Bind::SubsetWithProof {
                var,
                ty: Box::new(ty),
                predicate: Box::new(pred_ty),
                proof,
            }));
        }

        // case 2: SExp
        let pred_ty = self.parse_sexp()?;

        self.expect_token(&Token::RParen)?; // expect closing ')'
        Ok(Some(Bind::Subset {
            var,
            ty: Box::new(ty),
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
        if let Some(bind) = self.try_parse_subsetbind()? {
            return Ok(Some(bind));
        }
        // try simple bind next
        if let Some((var, ty)) = self.try_parse_simple_bind_paren()? {
            return Ok(Some(Bind::Named {
                var,
                ty: Box::new(ty),
            }));
        }
        // rollback if neither worked
        self.pos = save_pos;
        Ok(None)
    }

    // parse an arrow expression
    // e.g. `bind -> x` or `bind => x` or just piped atom sequence
    fn parse_arrow_expr(&mut self) -> Result<SExp, ParseError> {
        let left_head = self.parse_left_arrow_head()?;

        if self.bump_if(&Token::Arrow) {
            let right = self.parse_sexp()?;
            return Ok(SExp::Prod {
                bind: left_head,
                body: Box::new(right),
            });
        }

        if self.bump_if(&Token::DoubleArrow) {
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
        self.parse_arrow_expr()
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
        if let Some(tok) = self.peek() {
            match tok {
                Token::OtherSymbolStart(_) => {
                    let sym = self.expect_othersymbol()?;
                    return Ok(MacroExp::Tok(MacroToken(sym.to_string())));
                }
                Token::KeyWord(kw)
                    if !RESERVED_SORT_KEYWORDS.contains(kw)
                        && !EXPRESSION_KEYWORDS.contains(kw)
                        && !PROGRAM_KEYWORDS.contains(kw) =>
                {
                    let kw_str = self.expect_keyword()?;
                    return Ok(MacroExp::Tok(MacroToken(kw_str.to_string())));
                }
                _ => {}
            }
        }
        // 3. Parended sequence of macro tokens
        if self.bump_if(&Token::LParen) {
            let mut exps = Vec::new();
            while !self.bump_if(&Token::RParen) {
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
        self.expect_token(&Token::KeyWord("\\definition"))?;
        let name = self.expect_ident()?;
        self.expect_token(&Token::Colon)?;
        let ty = self.parse_sexp()?;
        self.expect_token(&Token::Assign)?;
        let body = self.parse_sexp()?;
        self.expect_token(&Token::Semicolon)?;
        Ok(ModuleItem::Definition { name, ty, body })
    }

    // "\import" <module_name: Ident> "(" (<param: Ident> ":=" <arg: SExp ";")* ")" "\as" <import_name: Ident> ";"
    fn parse_import(&mut self) -> Result<ModuleItem, ParseError> {
        // 1. "\import" <module_name: Ident> "("
        self.expect_token(&Token::KeyWord("\\import"))?;
        let module_name = self.expect_ident()?;
        self.expect_token(&Token::LParen)?;

        // 2. (<param: Ident> ":=" <arg: SExp> ";" )* until ")" is found
        let mut assign_pairs = vec![];
        while !self.bump_if(&Token::RParen) {
            let param = self.expect_ident()?;
            self.expect_token(&Token::Assign)?;
            let arg = self.parse_sexp()?;
            self.expect_token(&Token::Semicolon)?;
            assign_pairs.push((param, arg));
        }

        // 3. "\as" <import_name: Ident> ";"
        self.expect_token(&Token::KeyWord("\\as"))?;
        let import_name = self.expect_ident()?;
        self.expect_token(&Token::Semicolon)?;

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
        self.expect_token(&Token::Pipe)?;
        let ctor_name = self.expect_ident()?;
        self.expect_token(&Token::Colon)?;
        let ctor_type = self.parse_sexp()?;
        self.expect_token(&Token::Semicolon)?;
        Ok((ctor_name, ctor_type))
    }

    // "\inductive" <type_name: Ident> ("(" <param: Ident> ":" <ty: SExp> ")")* ":" <arity: SExp> ":=" (<ctor_decl>)* ";"
    fn parse_inductive_decl(&mut self) -> Result<ModuleItem, ParseError> {
        self.expect_token(&Token::KeyWord("\\inductive"))?;
        let type_name = self.expect_ident()?;

        let mut parameters = vec![];
        while let Some((var, ty)) = self.try_parse_simple_bind_paren()? {
            parameters.push((var, ty));
        }
        self.expect_token(&Token::Colon)?;
        let arity = self.parse_sexp()?;

        eprintln!("hello");

        // body of constructors
        self.expect_token(&Token::Assign)?;
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
        self.expect_token(&Token::Semicolon)?;
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
            _ => {
                self.pos = save_pos;
                Ok(None)
            }
        }
    }

    // parse a module
    // "\module" <module_name: Ident> ("(" (<param: Ident> ":" <ty: SExp> ";")* ")")? "{" (<module_item>)* "}"
    pub fn parse_module(&mut self) -> Result<Module, ParseError> {
        self.expect_token(&Token::KeyWord("\\module"))?;
        let module_name = self.expect_ident()?;
        let mut parameters = vec![];
        if self.bump_if(&Token::LParen) {
            while !self.bump_if(&Token::RParen) {
                let Some((var, ty)) = self.try_parse_annotate()? else {
                    return Err(ParseError {
                        msg: "expected parameter annotation in module parameter list".into(),
                        start: self.pos,
                        end: self.pos,
                    });
                };
                self.expect_token(&Token::Semicolon)?;
                parameters.push((var, ty));
            }
        }

        // body
        self.expect_token(&Token::LBrace)?;
        let mut declarations = vec![];
        while let Some(item) = self.try_parse_module_item()? {
            declarations.push(item);
        }
        self.expect_token(&Token::RBrace)?;
        Ok(Module {
            name: module_name,
            parameters,
            declarations,
        })
    }
}

pub fn lex_all<'a>(input: &'a str) -> Result<Vec<SpannedToken<'a>>, String> {
    let mut lexer = Token::lexer(input);
    let mut out = Vec::new();

    while let Some(tok) = lexer.next() {
        match tok {
            Ok(kind) => {
                let span = lexer.span(); // std::ops::Range<usize>
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
    fn a() {
        fn tok_all_ok(input: &'static str) {
            let mut toks = Token::lexer(input);
            loop {
                let Some(tok) = toks.next() else {
                    break;
                };
                println!("span[{:?}] slice[{}]", toks.span(), toks.slice());
                match tok {
                    Ok(ok) => println!("  {:?}", ok),
                    Err(_) => panic!("lex error in input: {}", input),
                }
            }
        }
        tok_all_ok(r"(x: X) -> Y => z");
        tok_all_ok(r"(x @ z # a");
        tok_all_ok(r"x $( y += z )$");
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
        print_and_unwrap(
            r"\definition const : (X : \Set) -> (Y : \Set) -> X := (x : X) => (y : Y) => x ;",
        );
        print_and_unwrap(r"\import MyModule () \as ImportedModule ;");
        print_and_unwrap(r"\import MyModule ( A := B; C := (x: X) => y ;) \as T;");
        print_and_unwrap(r"\inductive Bool : \Set := | true : Bool ; | false : Bool ; ;");
    }
}
