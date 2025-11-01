use std::fmt::Display;

use kernel::exp::Sort;
use lalrpop_util::lalrpop_mod;

use crate::{
    syntax::{self, Identifier, MacroToken},
    utils,
};

lalrpop_mod!(program);

#[derive(Debug, Clone)]
enum AtomTok {
    Sort(Sort),
    AccessPath(Vec<Identifier>),
}

impl Display for AtomTok {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomTok::Sort(sort) => write!(f, "{:?}", sort),
            AtomTok::AccessPath(path) => {
                let path_str = path
                    .iter()
                    .map(|id| id.to_string())
                    .collect::<Vec<String>>()
                    .join(".");
                write!(f, "{}", path_str)
            }
        }
    }
}

#[derive(Debug, Clone)]
enum AtomLike {
    AtomTok(AtomTok),
    ParenToks(Vec<SExpTok>),               // "(" t0 ... tn ")"
    CurlyToks(Vec<SExpTok>),               // "{" t0 ... tn "}" only for subset { x: T | P }
    MathMacro(Vec<MacroSeq>),              // "$(...$)"
    NamedMacro(Identifier, Vec<MacroSeq>), // "!name {...@}"
}

impl Display for AtomLike {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomLike::AtomTok(atom_tok) => write!(f, "{}", atom_tok),
            AtomLike::ParenToks(toks) => {
                let toks_str = toks
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<String>>()
                    .join(" ");
                write!(f, "({})", toks_str)
            }
            AtomLike::CurlyToks(toks) => {
                let toks_str = toks
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<String>>()
                    .join(" ");
                write!(f, "{{{}}}", toks_str)
            }
            AtomLike::MathMacro(seqs) => {
                let seqs_str = seqs
                    .iter()
                    .map(|s| format!("{}", s))
                    .collect::<Vec<String>>()
                    .join(" ");
                write!(f, "$({}$)", seqs_str)
            }
            AtomLike::NamedMacro(name, seqs) => {
                let seqs_str = seqs
                    .iter()
                    .map(|s| format!("{}", s))
                    .collect::<Vec<String>>()
                    .join(" ");
                write!(f, "!{} {{{}}}", name, seqs_str)
            }
        }
    }
}

#[derive(Debug, Clone)]
enum SExpTok {
    AtomLike(AtomLike), // "\Prop" "x" "x.y" "x.y.z" とか
    LambdaArrow,        // "=>"
    ProductTypeArrow,   // "->"
    Colon,              // ":"
    Mid,                // "|"
}

impl Display for SExpTok {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExpTok::AtomLike(atom_like) => write!(f, "{}", atom_like),
            SExpTok::LambdaArrow => write!(f, "=>"),
            SExpTok::ProductTypeArrow => write!(f, "->"),
            SExpTok::Colon => write!(f, ":"),
            SExpTok::Mid => write!(f, "|"),
        }
    }
}

// to display SExpTok vector for debugging
#[allow(dead_code)]
fn display_sexptoks(toks: &[SExpTok]) -> String {
    format!(
        "[{}]",
        toks.iter()
            .map(|t| format!("{}", t))
            .collect::<Vec<String>>()
            .join(" ")
    )
}

#[derive(Debug, Clone)]
enum MacroSeq {
    AtomLike(AtomLike),
    MacTok(MacroToken),
    Seq(Vec<MacroSeq>),
}

impl Display for MacroSeq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroSeq::AtomLike(atom_like) => write!(f, "{}", atom_like),
            MacroSeq::MacTok(mac_tok) => write!(f, "{}", mac_tok),
            MacroSeq::Seq(seqs) => {
                let seqs_str = seqs
                    .iter()
                    .map(|s| format!("{}", s))
                    .collect::<Vec<String>>()
                    .join(" ");
                write!(f, "{}", seqs_str)
            }
        }
    }
}

// [AtomLike] => SExp
fn parse_atomlike(tok: &AtomLike) -> Result<syntax::SExp, String> {
    match tok {
        AtomLike::AtomTok(atom_tok) => match atom_tok {
            AtomTok::Sort(sort) => Ok(syntax::SExp::Sort(*sort)),
            AtomTok::AccessPath(path) => Ok(syntax::SExp::AccessPath(path.clone())),
        },
        AtomLike::ParenToks(sexp_toks) => parse_exp(sexp_toks),
        AtomLike::CurlyToks(v) => {
            // find the first top-level "|"
            let Some(idx) = v.iter().position(|t| matches!(t, SExpTok::Mid)) else {
                return Err("Invalid subset type format: missing '|'".to_string());
            };
            let (var, set) = parse_simple_bind(&v[..idx])?;
            let predicate = parse_apply_all_from_sexptoks(&v[(idx + 1)..])?;
            Ok(syntax::SExp::Sub {
                var,
                ty: Box::new(set),
                predicate: Box::new(predicate),
            })
        }
        AtomLike::MathMacro(_) => todo!(),
        AtomLike::NamedMacro(_, _) => todo!(),
    }
}

// [AtomLike]+ = [a0: AtomLike] [a1: AtomLike] ... [an: AtomLik] => ((a0 a1) ... an)
fn parse_atomlikes(toks: &[AtomLike]) -> Result<syntax::SExp, String> {
    let v: Vec<_> = toks
        .iter()
        .map(parse_atomlike)
        .collect::<Result<Vec<_>, String>>()?;
    Ok(crate::utils::assoc_apply_vec(v))
}

// [AtomLike | "|" ]+ ... where "|" is pipeline operator
// => split by "|"
// e.g. 1: [x y z] => ((x y) z)
// e.g. 2: [x | f | g] => (g (f x))
// e.g. 3. [x y | f | g z] => ((g z) f) (x y)
fn parse_apply_all_from_sexptoks(toks: &[SExpTok]) -> Result<syntax::SExp, String> {
    let mut segments_applied: Vec<syntax::SExp> = Vec::new();
    for slice in toks.split(|t| matches!(t, SExpTok::Mid)) {
        if slice.is_empty() {
            return Err("Empty segment in pipeline".to_string());
        }
        let atomlikes: Vec<AtomLike> = slice
            .iter()
            .map(|t| match t {
                SExpTok::AtomLike(al) => Ok(al.clone()),
                _ => Err("Expected AtomLike in segment".to_string()),
            })
            .collect::<Result<Vec<_>, String>>()?;
        let exp = parse_atomlikes(&atomlikes)?;
        segments_applied.push(exp);
    }
    if segments_applied.is_empty() {
        return Err("No segments found in pipeline".to_string());
    }
    Ok(utils::assoc_apply_vec(segments_applied))
}

// take [x: Ident] [":"] ([] = Type )
// comsume everything until the next top-level SExpTok that is not part of the type
fn parse_simple_bind(v: &[SExpTok]) -> Result<(Identifier, syntax::SExp), String> {
    if let [
        SExpTok::AtomLike(AtomLike::AtomTok(AtomTok::AccessPath(var))),
        SExpTok::Colon,
        ..,
    ] = v
    {
        let var = var.first().ok_or("Invalid variable in bind")?.clone();
        let ty = parse_exp(&v[2..])?;
        Ok((var, ty))
    } else {
        Err("Invalid simple bind format".to_string())
    }
}

// <bind> = [AtomLike]+ | "(" <simple bind> ")" | "(" "(" <simple bind> ")" | [AtomLike]+ ")"
fn parse_bind(toks: &[SExpTok]) -> Result<syntax::Bind, String> {
    // case 1: Anonymous ... if succeeds, return Anonymous bind
    if let Ok(ty) = parse_apply_all_from_sexptoks(toks) {
        return Ok(syntax::Bind::Anonymous { ty: Box::new(ty) });
    }

    // other case should be parenthesized
    let [SExpTok::AtomLike(AtomLike::ParenToks(inner_toks))] = toks else {
        // not a parenthesized bind
        return Err("Invalid bind format".to_string());
    };

    // case 2: "(" <simple bind> ")"
    if let Ok((var, ty)) = parse_simple_bind(inner_toks) {
        return Ok(syntax::Bind::Named {
            var,
            ty: Box::new(ty),
        });
    }

    // case 3: "(" "(" <simple bind> ")" "|" "(" <simple bind> ")" ")"
    if let [
        SExpTok::AtomLike(AtomLike::ParenToks(simple_bind_toks)),
        SExpTok::Mid,
        SExpTok::AtomLike(AtomLike::ParenToks(proof_bind_toks)),
    ] = &inner_toks[..]
    {
        let (var, ty) = parse_simple_bind(simple_bind_toks)?;
        let (predicate_var, predicate) = parse_simple_bind(proof_bind_toks)?;
        if predicate_var.0 == "_" {
            return Err("Proof variable must be anonymous '_'".to_string());
        }
        return Ok(syntax::Bind::SubsetWithProof {
            var,
            ty: Box::new(ty),
            predicate: Box::new(predicate),
            proof: predicate_var,
        });
    }

    // case 4: "(" "(" <simple bind> ")" "|" [AtomLike]+ ")"
    if let [
        SExpTok::AtomLike(AtomLike::ParenToks(simple_bind_toks)),
        SExpTok::Mid,
        ..,
    ] = &inner_toks[..]
    {
        let (var, ty) = parse_simple_bind(simple_bind_toks)?;
        let predicate = parse_apply_all_from_sexptoks(&inner_toks[2..])?;
        return Ok(syntax::Bind::Subset {
            var,
            ty: Box::new(ty),
            predicate: Box::new(predicate),
        });
    }

    Err("Invalid bind format".to_string())
}

// <bind> "->" <exp> | <bind> "=>" <exp>
fn parse_pi_or_lambda(toks: &[SExpTok]) -> Result<syntax::SExp, String> {
    // find the first top-level "->" or "=>"
    let Some((idx, flag)) = toks.iter().enumerate().find_map(|(i, t)| {
        if matches!(t, SExpTok::ProductTypeArrow) {
            Some((i, true))
        } else if matches!(t, SExpTok::LambdaArrow) {
            Some((i, false))
        } else {
            None
        }
    }) else {
        return Err("No top-level arrow found".to_string());
    };

    let bind = parse_bind(&toks[..idx])?;
    let body_exp = parse_exp(&toks[idx + 1..])?;

    if flag {
        Ok(syntax::SExp::Prod {
            bind,
            body: Box::new(body_exp),
        })
    } else {
        Ok(syntax::SExp::Lam {
            bind,
            body: Box::new(body_exp),
        })
    }
}

fn parse_exp(toks: &[SExpTok]) -> Result<syntax::SExp, String> {
    // case 1: try parse as product type or lambda
    if let Ok(e) = parse_pi_or_lambda(toks) {
        return Ok(e);
    }
    // case 2: try parse as apply all
    parse_apply_all_from_sexptoks(toks)
}

pub fn str_parse_exp(input: &str) -> Result<syntax::SExp, String> {
    let toks: Vec<SExpTok> = program::SExpAllParser::new()
        .parse(input)
        .map_err(|e| format!("Parse error: {}", e))?;
    parse_exp(&toks)
}

enum ModItemDecl {
    Inductive {
        type_name: Identifier,
        parameter: Vec<(Identifier, Vec<SExpTok>)>,
        arity: Vec<SExpTok>,
        constructors: Vec<(Identifier, Vec<SExpTok>)>,
    },
    Import {
        module_name: Identifier,
        path: Vec<(Identifier, Vec<SExpTok>)>,
        import_name: Identifier,
    },
    Definition {
        name: Identifier,
        ty: Vec<SExpTok>,
        body: Vec<SExpTok>,
    },
}

struct ModDecl {
    pub name: Identifier,
    pub parameters: Vec<(Identifier, Vec<SExpTok>)>,
    pub declarations: Vec<ModItemDecl>,
}

fn parse_module(input: &ModDecl) -> Result<syntax::Module, String> {
    let ModDecl {
        name,
        parameters,
        declarations,
    } = input;
    let mut parameters_syntax: Vec<(Identifier, syntax::SExp)> = Vec::new();
    for (v, ty_toks) in parameters {
        let ty = parse_exp(ty_toks)?;
        parameters_syntax.push((v.clone(), ty));
    }
    let mut declarations_syntax: Vec<syntax::ModuleItem> = Vec::new();
    for it in declarations {
        let it_parsed = match it {
            ModItemDecl::Inductive {
                type_name,
                parameter,
                arity,
                constructors,
            } => {
                let parameter_syntax: Vec<(Identifier, syntax::SExp)> = parameter
                    .iter()
                    .map(|(v, ty_toks)| {
                        let ty = parse_exp(ty_toks)?;
                        Ok((v.clone(), ty))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                let arity_syntax = parse_exp(arity)?;
                let constructors_syntax: Vec<(Identifier, syntax::SExp)> = constructors
                    .iter()
                    .map(|(ctor_name, ctor_toks)| {
                        let ctor_ty = parse_exp(ctor_toks)?;
                        Ok((ctor_name.clone(), ctor_ty))
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                crate::syntax::ModuleItem::Inductive {
                    type_name: type_name.clone(),
                    parameter: parameter_syntax,
                    arity: arity_syntax,
                    constructors: constructors_syntax,
                }
            }
            ModItemDecl::Import {
                module_name,
                path,
                import_name,
            } => {
                let path_syntax: Vec<(Identifier, syntax::SExp)> = path
                    .iter()
                    .map(|(v, ty_toks)| {
                        let ty = parse_exp(ty_toks)?;
                        Ok((v.clone(), ty))
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                crate::syntax::ModuleItem::Import {
                    path: crate::syntax::ModuleInstantiated {
                        module_name: module_name.clone(),
                        arguments: path_syntax,
                    },
                    import_name: import_name.clone(),
                }
            }
            ModItemDecl::Definition { name, ty, body } => {
                let ty_syntax = parse_exp(ty)?;
                let body_syntax = parse_exp(body)?;
                crate::syntax::ModuleItem::Definition {
                    var: name.clone(),
                    ty: ty_syntax,
                    body: body_syntax,
                }
            }
        };
        declarations_syntax.push(it_parsed);
    }
    Ok(syntax::Module {
        name: name.clone(),
        parameters: parameters_syntax,
        declarations: declarations_syntax,
    })
}

pub fn str_parse_modules(input: &str) -> Result<Vec<syntax::Module>, String> {
    let mods: Vec<ModDecl> = program::ModuleAllParser::new()
        .parse(input)
        .map_err(|e| format!("Parse error: {}", e))?;
    let mut syntax_mods: Vec<syntax::Module> = Vec::new();
    for m in mods {
        let syntax_mod = parse_module(&m)?;
        syntax_mods.push(syntax_mod);
    }
    Ok(syntax_mods)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn parse_tok_unwrap(input: &'static str) -> Vec<SExpTok> {
        match program::SExpAllParser::new().parse(input) {
            Ok(toks) => {
                println!("input toks: {}", display_sexptoks(&toks));
                toks
            }
            Err(err) => {
                panic!("Error: {}", err);
            }
        }
    }
    #[test]
    fn atomlike_test() {
        fn print_and_unwrap(input: &'static str) {
            let toks = parse_tok_unwrap(input);
            match parse_apply_all_from_sexptoks(&toks) {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}", input, atomlike);
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        print_and_unwrap(r"x");
        print_and_unwrap(r"x y");
        print_and_unwrap(r"x | y");
        print_and_unwrap(r"x (y z)");
        print_and_unwrap(r"(x y) z");
    }
    #[test]
    fn parse_simple_bind_test() {
        fn print_and_unwrap_simplebind(input: &'static str) {
            match program::SExpAllParser::new().parse(input) {
                Ok(atomlike) => {
                    parse_simple_bind(&atomlike)
                        .map(|(id, ty)| {
                            println!("Parsed SimpleBind: {:?} => {:?}: {:?}", input, id, ty);
                        })
                        .unwrap();
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        print_and_unwrap_simplebind(r"x: X");
    }
    #[test]
    fn parse_bind_test() {
        fn print_and_unwrap_bind(input: &'static str) {
            match program::SExpAllParser::new().parse(input) {
                Ok(atomlike) => {
                    parse_bind(&atomlike)
                        .map(|bind| {
                            println!("Parsed Bind: {:?} => {:?}", input, bind);
                        })
                        .unwrap();
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        print_and_unwrap_bind(r"X");
        print_and_unwrap_bind(r"(x: X)");
        print_and_unwrap_bind(r"((x: X) | P)");
        print_and_unwrap_bind(r"((x: X) | (h: P))");
    }
    #[test]
    fn parse_lambda_or_pi_test() {
        fn print_and_unwrap_lambda_or_pi(input: &'static str) {
            match program::SExpAllParser::new().parse(input) {
                Ok(atomlike) => {
                    parse_pi_or_lambda(&atomlike)
                        .map(|exp| {
                            println!("Parsed Pi/Lam: {:?} => {:?}", input, exp);
                        })
                        .unwrap();
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        print_and_unwrap_lambda_or_pi(r"(x: X) -> Y");
        print_and_unwrap_lambda_or_pi(r"(x: X) => y");
        print_and_unwrap_lambda_or_pi(r"(x: X) -> Y => z");
        print_and_unwrap_lambda_or_pi(r"(x: X) => y h -> z");
    }
}
