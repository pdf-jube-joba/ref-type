//! Render retained kernel judgements using frontend names and surface syntax.
use crate::raw::environment::CrateEnv;
use kernel::{ids::SymbolId, metavariables::Error as CheckError, syntax::*};
mod names;
mod terms;
use names::Names;

pub(super) fn format_error(raw: &CrateEnv, error: &CheckError) -> String {
    let CheckError::TypeMismatch(error) = error else {
        return error.to_string();
    };
    let mut renderer = Renderer {
        raw,
        arena: &error.arena,
        names: Names::new(raw),
        locals: vec![],
        remaining: 512,
        depth: 0,
    };
    let mut context = Vec::new();
    for binding in &error.context {
        let ty = renderer.expression(binding.ty, 0);
        let name = renderer.bind(binding.var);
        context.push(format!("{name}: {ty}"));
    }
    renderer.remaining = 512;
    let inferred = renderer.expression(error.inferred, 0);
    renderer.remaining = 512;
    let expected = renderer.expression(error.expected, 0);
    let context = if context.is_empty() {
        String::new()
    } else {
        format!("\ncontext: {}", context.join(", "))
    };
    let frames = error.frames.join("\n");
    format!(
        "types are not convertible\ninferred: {inferred}\nexpected: {expected}{context}\n{frames}"
    )
}

pub(crate) fn format_expression(
    raw: &CrateEnv,
    context: &Context,
    expression: Expression,
) -> String {
    let mut renderer = Renderer {
        raw,
        arena: &raw.arena().core,
        names: Names::new(raw),
        locals: vec![],
        remaining: 512,
        depth: 0,
    };
    for binding in context {
        renderer.bind(binding.var);
    }
    renderer.expression(expression, 0)
}

struct Local {
    name: String,
    used: bool,
}
struct Renderer<'a> {
    raw: &'a CrateEnv,
    arena: &'a kernel::syntax::Arena,
    names: Names,
    locals: Vec<Local>,
    remaining: usize,
    depth: usize,
}

// Larger precedence binds more tightly: binders, equality, application, atoms.
struct Term {
    text: String,
    precedence: u8,
}
impl Term {
    fn new(text: impl Into<String>, precedence: u8) -> Self {
        Self {
            text: text.into(),
            precedence,
        }
    }
    fn atom(text: impl Into<String>) -> Self {
        Self::new(text, 3)
    }
}

impl Renderer<'_> {
    fn expression(&mut self, e: impl Into<Expression>, precedence: u8) -> String {
        let term = self.render(e.into());
        if term.precedence < precedence {
            format!("({})", term.text)
        } else {
            term.text
        }
    }

    fn render(&mut self, e: Expression) -> Term {
        if self.remaining == 0 || self.depth >= 64 {
            return Term::atom("…");
        }
        self.remaining -= 1;
        self.depth += 1;
        let term = self.term(e);
        self.depth -= 1;
        term
    }

    fn bind(&mut self, var: SymbolId) -> String {
        let base = if var == SymbolId::ANONYMOUS {
            "x"
        } else {
            self.raw.symbol(var)
        };
        let mut name = base.to_owned();
        let mut suffix = 1;
        while self.locals.iter().any(|local| local.name == name) {
            name = format!("{base}{suffix}");
            suffix += 1;
        }
        self.locals.push(Local {
            name: name.clone(),
            used: false,
        });
        name
    }

    fn bound(&mut self, index: usize) -> Term {
        match self.locals.len().checked_sub(index + 1) {
            Some(i) => {
                self.locals[i].used = true;
                Term::atom(self.locals[i].name.clone())
            }
            None => Term::atom(format!("#{index}")),
        }
    }

    fn binder(
        &mut self,
        var: SymbolId,
        domain: Expression,
        body: Expression,
        lambda: bool,
        program: bool,
    ) -> Term {
        let domain = self.expression(domain, 1);
        let name = self.bind(var);
        let body = self.expression(body, 0);
        let used = self.locals.pop().unwrap().used;
        let text = if lambda {
            let keyword = if program { "cfun" } else { "fun" };
            format!("\\{keyword} ({name}: {domain}) => {body}")
        } else if used {
            format!("\\forall ({name}: {domain}) -> {body}")
        } else {
            let arrow = if program { "~>" } else { "->" };
            format!("{domain} {arrow} {body}")
        };
        Term::new(text, 0)
    }

    fn application(&mut self, function: Expression, argument: Expression) -> Term {
        let function = self.expression(function, 2);
        let argument = self.expression(argument, 3);
        Term::new(format!("{function} {argument}"), 2)
    }

    fn definition(&mut self, id: kernel::ids::DefinitionId, arguments: &[Expression]) -> Term {
        let name = self
            .names
            .definitions
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("{id:?}"));
        if arguments.is_empty() {
            Term::atom(name)
        } else {
            self.call(&name, arguments)
        }
    }

    fn call(&mut self, name: &str, arguments: &[Expression]) -> Term {
        let args = arguments
            .iter()
            .map(|&e| self.expression(e, 0))
            .collect::<Vec<_>>();
        let text = match (name, args.as_slice()) {
            ("RunStep", [state, result]) => format!("\\RunStep[{state}, {result}]"),
            ("continue" | "finish", [state, result, value]) => {
                format!("\\{name}[{state}, {result}]({value})")
            }
            ("Acc" | "accintro" | "accdescent", [state, result, rest @ ..]) => {
                format!("\\{name}[{state}, {result}]({})", rest.join(", "))
            }
            ("run", [state, result, step, initial, proof]) => {
                format!("\\run[{state}, {result}]({step}, {initial}) \\by {{ {proof} }}")
            }
            (
                "runCase",
                [
                    state,
                    result,
                    step,
                    initial,
                    transition,
                    accessibility,
                    equality,
                ],
            ) => format!(
                "\\runCase[{state}, {result}]({step}, {initial}, {transition}) \\by {{ accessibility: {accessibility}, equality: {equality} }}"
            ),
            ("Box", [ty]) => format!("\\Box[{ty}]"),
            ("box" | "squash" | "Cast", [ty, value]) => format!("\\{name}[{ty}]({value})"),
            ("In", [ty, set, element]) => format!("\\In[{ty}] ({set}) ({element})"),
            ("into", [ty, set, element, proof]) => {
                format!("\\into[{ty}]({element}, {set}) \\by {{ {proof} }}")
            }
            ("Take", [domain, codomain, map, existence, uniqueness]) => format!(
                "\\Take({domain}, {codomain}, {map}) \\by {{ existence: {existence}, uniqueness: {uniqueness} }}"
            ),
            ("TakeProp", [domain, proposition, map, existence]) => {
                format!("\\TakeProp({domain}, {proposition}, {map}) \\by {{ {existence} }}")
            }
            ("takeelim", [func, domain, codomain, element, existence, uniqueness]) => format!(
                "\\takeelim({func}, {element}, {domain}, {codomain}) \\by {{ existence: {existence}, uniqueness: {uniqueness} }}"
            ),
            _ => format!("\\{name}({})", args.join(", ")),
        };
        Term::atom(text)
    }

    fn inductive(
        &mut self,
        id: kernel::ids::InductiveId,
        constructor: Option<usize>,
        parameters: Vec<Expression>,
    ) -> Term {
        let (name, constructors) = self
            .names
            .inductives
            .get(&id)
            .cloned()
            .unwrap_or_else(|| (format!("ind#{}", id.0), vec![]));
        self.named_application(name, constructors, constructor, parameters)
    }

    fn datatype(
        &mut self,
        id: kernel::ids::ProgramInductiveId,
        constructor: Option<usize>,
        parameters: Vec<Expression>,
    ) -> Term {
        let (name, constructors) = self
            .names
            .datatypes
            .get(&id)
            .cloned()
            .unwrap_or_else(|| (format!("datatype#{}", id.0), vec![]));
        self.named_application(name, constructors, constructor, parameters)
    }

    fn datatype_constructor(
        &mut self,
        id: kernel::ids::ProgramInductiveId,
        constructor: usize,
        parameters: Vec<Expression>,
        fields: Vec<Expression>,
    ) -> Term {
        let name = self.datatype(id, Some(constructor), parameters);
        if fields.is_empty() {
            return name;
        }
        let fields = fields
            .into_iter()
            .map(|e| self.expression(e, 3))
            .collect::<Vec<_>>()
            .join(" ");
        Term::new(format!("{} {fields}", name.text), 2)
    }

    fn named_application(
        &mut self,
        mut name: String,
        constructors: Vec<String>,
        constructor: Option<usize>,
        arguments: Vec<Expression>,
    ) -> Term {
        if !arguments.is_empty() {
            let arguments = arguments
                .into_iter()
                .map(|e| self.expression(e, 0))
                .collect::<Vec<_>>()
                .join(", ");
            name = format!("{name}[{arguments}]");
        }
        if let Some(index) = constructor {
            let constructor = constructors
                .get(index)
                .cloned()
                .unwrap_or_else(|| format!("constructor#{index}"));
            name = format!("{name}::{constructor}");
        }
        Term::atom(name)
    }
}

fn universe(name: &str, level: usize) -> String {
    if level == 0 {
        format!("\\{name}")
    } else {
        format!("\\{name}({level})")
    }
}

impl Renderer<'_> {
    fn subset(&mut self, var: SymbolId, set: Expression, predicate: Expression) -> Term {
        let set = self.expression(set, 0);
        let name = self.bind(var);
        let predicate = self.expression(predicate, 0);
        self.locals.pop();
        Term::atom(format!("{{ {name}: {set} \\where {predicate} }}"))
    }

    fn id_elim(
        &mut self,
        var: SymbolId,
        left: Expression,
        right: Expression,
        ty: Expression,
        predicate: Expression,
        base: Expression,
        equality: Expression,
    ) -> Term {
        let left = self.expression(left, 2);
        let right = self.expression(right, 2);
        let ty = self.expression(ty, 0);
        let name = self.bind(var);
        let predicate = self.expression(predicate, 0);
        self.locals.pop();
        let base = self.expression(base, 0);
        let equality = self.expression(equality, 0);
        Term::atom(format!(
            "\\idelim {left} = {right} \\with {name}: {ty} => {predicate} \\by {{ base: {base}, equality: {equality} }}"
        ))
    }

    fn let_term(
        &mut self,
        var: SymbolId,
        ty: Expression,
        value: Expression,
        body: Expression,
        computation: bool,
    ) -> Term {
        let ty = self.expression(ty, 0);
        let value = self.expression(value, 0);
        let name = self.bind(var);
        let body = self.expression(body, 0);
        self.locals.pop();
        let (keyword, assignment) = if computation {
            ("bind", "<-")
        } else {
            ("let", ":=")
        };
        Term::new(
            format!("\\{keyword} {name}: {ty} {assignment} {value} \\in {body}"),
            0,
        )
    }

    fn elimination(
        &mut self,
        induction: bool,
        id: kernel::ids::InductiveId,
        scrutinee: Expression,
        motive: Expression,
        branches: Vec<Expression>,
    ) -> Term {
        let scrutinee = self.expression(scrutinee, 0);
        let motive = self.expression(motive, 0);
        let constructors = self
            .names
            .inductives
            .get(&id)
            .map(|(_, cs)| cs.clone())
            .unwrap_or_default();
        let branches = branches
            .into_iter()
            .enumerate()
            .map(|(i, branch)| {
                let constructor = constructors
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("constructor#{i}"));
                format!("| {constructor} => {}", self.expression(branch, 0))
            })
            .collect::<Vec<_>>()
            .join("; ");
        let keyword = if induction { "induction" } else { "match" };
        Term::atom(format!(
            "\\{keyword} ({scrutinee}) \\return {motive} \\with {{ {branches} }}"
        ))
    }

    fn case(
        &mut self,
        id: kernel::ids::ProgramInductiveId,
        scrutinee: Expression,
        binders: &[Vec<SymbolId>],
        branches: Vec<Expression>,
    ) -> Term {
        let scrutinee = self.expression(scrutinee, 0);
        let constructors = self
            .names
            .datatypes
            .get(&id)
            .map(|(_, cs)| cs.clone())
            .unwrap_or_default();
        let branches = branches
            .into_iter()
            .enumerate()
            .map(|(i, branch)| {
                let constructor = constructors
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("constructor#{i}"));
                let depth = self.locals.len();
                let names = binders
                    .get(i)
                    .into_iter()
                    .flatten()
                    .map(|&var| self.bind(var))
                    .collect::<Vec<_>>()
                    .join(" ");
                let body = self.expression(branch, 0);
                self.locals.truncate(depth);
                format!("| {constructor} {names} => {body}")
            })
            .collect::<Vec<_>>()
            .join("; ");
        Term::atom(format!("\\match ({scrutinee}) \\with {{ {branches} }}"))
    }
}

#[cfg(test)]
mod tests;
