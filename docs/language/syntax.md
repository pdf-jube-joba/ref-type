# Surface syntax

In examples, `<...>` is a placeholder to replace with an actual name or expression.

## 1. Lexing and common notation

### Lexing

- Unicode whitespace separates tokens and is otherwise ignored.
- `/* ... */` delimits nestable comments.
- Identifiers start with an ASCII letter, followed by ASCII letters, digits, or `_`.
- Keywords have the form `\name`, where the name can contain ASCII letters, digits, and `-`.
- Numbers are nonnegative decimal integers.
- `"..."` is a quoted macro token without newlines or escape sequences.

The following symbols are syntax tokens.

```text
( ) \( \) { } [ ]
^ | : ; . , = ! :: ::#
-> ~> <- => :=
```

Other symbol sequences form single macro tokens.
Separate adjacent symbol tokens with whitespace when they must remain distinct.

### Parameters and names

Use square brackets for arguments to types, definitions, constructors, type-associated items, and modules. Empty `[]` is also allowed.

```text
Type[A, B]
Type[A, B]::item argument
\import my_package.M[A := T, x := value] \as Alias;
\import my_package.M[] \as Alias;
```

Use `.` and `::` to access names.

```text
name
Import.name
Type[A]::item
Import.Type[A]::item
```

Appending `^` to a Program name refers to its reflection into Set.

```text
Bool^
Bool^::true
Wrap^[Bool^]
value^
identity^
Import.Bool^
Import.value^
Pair[Bool]::first^
Pair[Bool]::#^
```

Parameters of Program datatypes, constructors, record literals, and type-associated items may be omitted or written as `_` when the context determines them.

### Metavariables

| Notation | Meaning |
| --- | --- |
| `_` | A fresh inference variable at each occurrence |
| `_0`, `_1` | Inference variables shared by number across a declaration's type annotation and body |
| `?` | An inspection hole for examining the expected type and context |

Inference variables are solved from constraints.
A definition's declared type is passed to lambdas in its body as an expected type, allowing `_` annotations on arguments used for projections or existential elimination.
Grouped binders, blocks, and local definitions with type annotations also use this expected type, preserving refinement types.

```text
\definition andElim[P, Q, R: \Prop]: (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value.left) (value.right);
```

The solution of a shared inference variable may depend on outer binders common to all its occurrences.
As a binder name, `_` is anonymous.

In Set/Prop expressions, `\assign` registers an equality with a numbered inference variable.
The constraint is solved when the expression is elaborated and shared across the declaration's type annotation and body.
The expression retains the value of its left operand; if a solution already exists, it is checked for consistency.
`\assign` binds more weakly than arrows.

```text
\definition Relation[A: \Set]: \PropKind := A -> A -> \Prop;
\definition diagonal[A: \Set][R: Relation[A] \assign _1]: _1 := R;
```

Elaborating a module containing `?` fails and reports the expected type, local variables, and relevant constraints at that position.
Even if constraints determine a term, the hole is still reported along with that term.
Unresolved inference variables in the same declaration are displayed as well.

Diagnostics distinguish insufficient information, waiting for other metavariables, constraints unsupported by the solver, and contradictory constraints.
Constraints display source metavariable numbers, origin locations, and expressions before and after solving.

## 2. Modules

A root file contains module declarations and may be empty. Modules may be nested.
Ordinary term names resolve in the context at their declaration, while macro definitions and use declarations apply throughout the body and child modules.

```text
\module Name(parameters) {
  <module-item>*
}

\module Name(parameters);
```

A declaration ending in `;` is an external module whose items reside in the corresponding `Name.ref` file.
Child module file paths follow the module nesting.

### Imports

```text
\import .Child[A := T] \as C;
\import \root.Top[A := T] \as RootTop;
\import \parent.Sibling[] \as S;
\import \parent.\parent.Outer[] \as O;
\import my_package.Top[A := T] \as T;
\import my_package.Top[A := T].Nested[] \as N;
\import ExistingAlias.Child[x := value] \as Child;
```

Argument counts, names, and order must match the parameter declaration.
A leading `.` starts lookup in the current module; `\parent.` starts one module above it.
`\root.` starts at the current package root; a package name starts at that package's root.
Metavariable inference is not performed in module arguments.

### Instantiation in expressions

```text
\definition carrier[A: \Set]: \Set := Family[A := A].Carrier;
\definition rootCarrier[A: \Set]: \Set := \root.Family[A := A].Carrier;
\definition disk[n: Nat^]: \Set := Euclidean.Dimension[n := n].Disk;
\structure Cell: \Set := {
  dimension: Nat^,
  point: Euclidean.Dimension[n := dimension].Disk,
};
```

Module arguments are checked at the reference site, which selects an item from the instantiated module.
Arguments may refer to function arguments or preceding record fields.
See the [module specialization tests](../../tests/packages/specialization.md) for inductive instantiation and Program local arguments.

## 3. Declarations

### Definitions

```text
\definition name: type := expression;
\definition name[x, y: A][z: B]: type := expression;
\definition Type[parameters]::item[arguments]: type := expression;
```

Binders to the left of `:` extend the declaration context used to check the result type and body.
The type and body classify the definition as Set/Prop, a Program value, or a Program computation.
`Type::item` declares a type-associated item with the owner's parameters first.

### Contextual definitions

```text
\definition Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;
\definition At[A: \Set, x: A, P: A -> \Prop]: \Prop := P x;
```

Application checks each argument and substitutes it into the declaration to instantiate the result.
A definition can be used as an ordinary function when it can form a product type.
After substituting supplied arguments, a partial application can become a function if the remaining arguments satisfy the existing product rules.

### Inductive types

```text
\inductive Type[parameters]: result-kind :=
| constructor1: constructor-type
| constructor2: constructor-type
;
```

The result kind must end in `\Prop`, `\PropKind`, `\Set`, `\SetKind`, or `\VType`.
Constructor types combine `->`, `\forall`, and ordinary expressions.
Program inductive parameters have type `\VType`, fields have value types, and Program datatypes cannot have indices.
Constructors must return the declared datatype, and recursive occurrences must be strictly positive.

```text
\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\inductive List[A: \VType]: \VType :=
| nil: List
| cons: A -> List[A] -> List
;
```

Set/Prop inductive types may bind indices before the result sort.
Parameters remain fixed across the entire type family; indices are specified separately in each constructor's result.

```text
\inductive Family[A: \Set]: \forall (x: A) -> \Set :=
| leaf: \forall (x: A) -> Family x
| next: \forall (x: A) -> Family x -> Family x
;
```

### Structures

Structures support declaration bundles of associated types, operations, and laws, as well as records with explicit sorts.
See [structures](structure.md) for declarations, literals, defaults, and quantification, and [type-associated items](types_and_items.md) for associated definitions and projections.

A record with an explicit sort and no laws has a constructor `#` taking fields in declaration order.
For induction, supply a function taking those fields as the `#` branch.

```text
\structure Pair[A, B: \Set]: \Set := {
  left: A,
  right: B,
};
\definition pair[A, B: \Set][a: A][b: B]: Pair[A, B] := Pair[A, B]::# a b;
\definition eta[A, B: \Set]: \forall (p: Pair[A, B]) -> Pair[A, B]::# p.left p.right = p :=
  \induction (p: Pair[A, B]) \return Pair[A, B]::# p.left p.right = p \with {
    | # : \fun (a: A)(b: B) => \refl(Pair[A, B]::# a b)
  };
```

### Implementations, specifications, and state transitions

`Correspondence`, `Machine`, and `runBox` are library definitions rather than built-in declarations.
The following example assumes a `std` dependency configured as described in [CLI usage](../../src/USAGE.md).
The [machine tests](../../tests/language/declarations/machines.md) contain self-contained definitions and executable examples of these bundles.

```text
\import std.Program[] \as P;
\definition identity: P.Correspondence := P.Correspondence {
  T := \U(A ~> \F(A)),
  program := \thunk(\cfun(x: A) => \return x),
  specification := \fun(x: A^) => x,
  coherence := \refl(\fun(x: A^) => x),
};
```

After supplying a `Machine`'s `State`, `Output`, `step`, and `terminates` fields, the default `run` implementation executes using the termination proof.
The `runBox` definition boxes the machine's execution.

```text
P.runBox machine
```

Boxes retain type and value parameters.
`\squash` reduces the Program computation as far as possible and reflects the residual term, including terms blocked on input, into Logic.

### Checking and evaluation

Set/Prop and Program use the same query statements.
`\check` checks an expression against a specified type; `\infer` displays its inferred type.
`\eval` displays one reduction step; `\normalize` displays the result of repeated reduction.
Evaluation queries can reduce ill-typed expressions, but Program runs and expressions containing inference variables require checking.

```text
\check expression: type;
\infer expression;
\eval expression;
\normalize expression;
```

## 4. Common expression syntax

### Binders

```text
(x, y: A, z: B)
(_: A)
(x: A \where predicate \as proof)
```

A binder with `\where` takes exactly one value name and introduces a condition with an optional proof name.
It can be used with `\forall` and `\fun`.

### Precedence

Precedence, from strongest to weakest:

| Syntax | Associativity |
| --- | --- |
| `atom`, parentheses | None |
| `expression::item`, `expression.field` | Left |
| `keyword atom` | Right |
| `function argument` | Left |
| `left = right` | Nonassociative |
| `A -> B`, `A ~> C` | Right |
| `a \of T`, `a \assign _1` | Left |

```text
f x y
x y.field z
(x y).field z
x = y
A -> B -> C
A ~> B ~> C
```

`\let` and `\bind` extend over the entire expression following `\in`. `\return` also consumes the entire following value expression.
Keywords taking a single atom associate to the right. Parenthesize compound expressions passed as their arguments.
`x y.field z` parses as `x (y.field) z`.

### Type ascription

```text
a \of T
f x \of A -> B
(\fun (x: _) => x) \of A -> A
(\return a) \of \F A
```

`a \of T` checks `a` against type `T` and gives the entire expression type `T`.
The ascription disappears during reduction.
It can be used with Set/Prop terms and Program values and computations.

## 5. Set/Prop

### Sorts

```text
\Prop
\PropKind
\Set
\Set(2)
\SetKind
\SetKind(2)
```

The level of `\Set` and `\SetKind` defaults to 0 when omitted.

### Products and lambdas

```text
A -> B
\forall (x: A) -> B
\forall (x, y: A) (z: B) -> C
\fun (x: A) => body
\fun (x, y: A) (z: B) => body
```

### Set operators

```text
\Pow A
{ x : A \where predicate }
\Cast[A] subset
\In[A] subset element
\into[A](element, subset) \by { membership-proof }
\exists A
\exists (x: A \where P x)
```

`\Pow` forms a powerset, `\Cast` forms a refinement type, `\In` is the membership predicate, and `\into` supplies an element with a membership proof.

### Choice

```text
\choice X
\by { existence: existence-proof, uniqueness: uniqueness-proof }

\take (x: A) => body
\by { existence-proof }

\block {
  \takefrom x: A \by existence-proof \then
  \return body
}
```

`\choice` returns the unique element of an inhabited singleton set.
`uniqueness-proof` proves `\forall (x, y: X) -> x = y`.
`\take` and `\takefrom` use an existence proof to prove a proposition.

### Equality and proof terms

```text
left = right
\refl element-atom
\exact(element, set)
\bysub(superset, subset, element)
\idelim left = right \with x: A => family \by { base: base-term, equality: equality-proof }
\transporteq index \with x: A => family \by { base: base-term }
\choiceeq element \of X
  \by { existence: existence-proof, uniqueness: uniqueness-proof }
```

The `family` in `\idelim` takes values in `\Prop` or `\Set(i)`.
`base-term` belongs to the family at the starting index; `equality-proof` transports it to the family at the ending index.
Transport in a set-valued family has a neutral head. Identity of transport to the same index is proved as a propositional equality with `\transporteq`.
For a set-valued family, `\transporteq` proves that transporting `base-term` from `index` to the same `index` equals `base-term`.
The index type `A` can be inferred with `_`. After type checking, transport's equality proof is erased when comparing definitional equality.

```text
\module Transport(A: \Set, F: A -> \Set, a, b: A) {
  \definition cast[value: F a][same: a = b]: F b :=
    \idelim a = b \with x: _ => F x \by { base: value, equality: same };
  \definition identity: \forall (value: F a)(same: a = a) ->
    (\idelim a = a \with x: _ => F x \by { base: value, equality: same }) = value :=
    \fun (value: F a)(same: a = a) =>
      \transporteq a \with x: _ => F x \by { base: value };
}
```

`\choiceeq` proves `element = \choice X \by { existence: existence-proof, uniqueness: uniqueness-proof }`.
It uses the uniqueness of elements of `X` through the typing of choice.
The set in `\of _` can be inferred when the expected equality's right-hand side unfolds to a choice.
Proof arguments to choice and choiceeq are type checked and erased when comparing definitional equality.

Built-in axioms:

```text
\axiom:setext(left, right, left-to-right, right-to-left)
\axiom:funext(left, right, pointwise)
\axiom:classicalIndefiniteChoice(domain, family, inhabited)
```

### Inductive elimination

```text
\match scrutinee \in Type \return motive \with {
| constructor1 : branch1
| constructor2 field : branch2
}

\induction (x: Type[parameters]) \return result-type \with {
| constructor1 : branch1
| constructor2 : branch2
}
```

Branches of `\match` and `\induction` end at `|` or `}`.
For Set/Prop `\match`, `\return` accepts either a constant result type or a motive: a function from the matched value to its result type.
For an indexed datatype, an explicit motive takes the indices before the value.
Each branch header binds the constructor arguments, and its body has the motive applied to that constructor.

```text
\definition copy[n: Nat]: Nat :=
  \match n \in Nat \return \fun (_: Nat) => Nat \with {
    | zero: Nat::zero
    | succ previous: Nat::succ previous
  };
```

`\induction` binds `x` in the result type and constructs a function over the inductive type.
Each branch body is a function taking the constructor arguments and induction hypotheses.
For indexed inductive types, bind the indices before the element.

```text
\induction (n: Nat) (xs: Vec[A] n) \return P n xs \with {
| nil: base
| cons: step
}
```

The result type is checked as a type in the binder context.
For example, `\return \Prop` and `\return Real -> Real -> \Prop` are classified by `\PropKind`, allowing recursive construction of propositions or predicates from Set inductive types.
Each branch has the result type with its constructor substituted, and receives an induction hypothesis for each recursive argument immediately after that argument.

### Logical blocks

```text
\block {
  \fun (x, y: A) (h: P x) \then
  \let z: B := term \then
  \enough C \by { map } \then
  \return result
}
```

A logical block contains zero or more `\fun`, `\let`, `\enough`, or `\takefrom` statements and ends with a required `\return`.
`\fun` adds binders before the goal.
`\let` introduces a local definition that can be unfolded in subsequent terms and types.
`\enough A \by { map } \then` uses `map: A -> B` to change the remaining goal to `A`.

## 6. Program (CBPV)

Program distinguishes value types, computation types, values, and computations.

### Types

```text
\VType
\F value-type-atom
\U computation-type-atom
A ~> C
\RunStep[A, B]
```

`\F` forms a computation type returning a value; `\U` forms the value type of a thunk; `~>` forms a computation function type; `\RunStep` is the value type representing one execution step of a run.

`A -> B` is CBV syntax sugar. In a computation type position it means `A ~> \F(B)`; in a value type position it means `\U(A ~> \F(B))`. A bare `A -> B` as a definition's type is treated as a computation type.
Write `\U(A -> B)` for the type of a function value.

### Values and computations

```text
\return value
\thunk computation-atom
\force value-atom
\cfun (x: A) => computation
function value
```

Computation application takes a value argument.
Use `\force` explicitly before applying a function stored as a thunk, and `\bind` to receive a computation's result.
Curried CBV functions return intermediate functions as thunks, so successive arguments need both operations.

```text
\definition apply[f: \U(A ~> \F(A))][a: A]: \F(A) := (\force f) a;
\definition applyTwo[f: \U(A -> A -> A)][a, b: A]: \F(A) :=
  \bind next: \U(A -> A) <- (\force f) a \in
  (\force next) b;
```

Here `A: \VType`; see the [Program tests](../../tests/language/program/cases.md) for accepted forms and rejected implicit forcing or sequencing.

`\fun` and `->` are also CBV syntax sugar in Program contexts. In a computation position, `\fun` becomes `\cfun`; in a value position, it becomes a thunked computation. With multiple arguments, intermediate functions are returned as `\return(\thunk(...))`.

### Local bindings and Program blocks

```text
\let x: A := value \in computation
\bind y: B <- computation1 \in computation2

\program {
  \let x: A := value \then
  \bind y: B <- computation \then
  \return result
}
```

`\let` binds a value; `\bind` binds the result of a computation. Type annotations are required, and the name is in scope only after `\in`. Intermediate statements in a Program block are `\let` and `\bind`, connected by `\then`. The block ends with `\return value`.
Within a block, `\let` requires an ordinary identifier; `\bind` also allows `_`.

### Case analysis

```text
\match scrutinee \in Datatype \with {
| constructor1 : computation1
| constructor2 field1 field2 : computation2
}
```

The scrutinee and branch fields are values; branch bodies are computations.
The datatype name is required, and there must be exactly one branch per constructor in declaration order.
Do not put `;` after a branch.

## 7. General recursion, Run, and Box

### RunStep

```text
\continue[state-type, result-type](next-state)
\finish[state-type, result-type](output)
\step-match x: \RunStep[state-type, result-type] \return P \with {
  | \continue next-state: M
  | \finish output: N
}
\step-match \RunStep[state-type, result-type] \return C \with {
  | \continue next-state: M
  | \finish output: N
}
```

`\continue` and `\finish` are values of type `\RunStep[state-type, result-type]`.
With a variable `x`, `\step-match` constructs the Set dependent function `(x: \RunStep[state-type, result-type]) -> P`, with each branch returning a term of the corresponding type `P`.
Without a variable, `\step-match` constructs a Program value of type `\U(\RunStep[state-type, result-type] ~> C)`, where `C` is a fixed computation type and each branch is a computation.

### Termination

For Set types `State` and `Output` and a step function `step: State -> \RunStep[State, Output]`, termination is defined as an ordinary proposition.
The following `T` names refer to the `std` library, not built-in syntax; the [termination tests](../../tests/language/general-recursion/termination.md) also express the required proposition directly.

```ref
\import std.Logic[].Termination[
  State := State, Output := Output, step := step
] \as T;
```

`T.Holds initial` unfolds to the following type.

```ref
\forall (P: State -> \Prop) ->
  (\forall (x: State) -> T.ready P (step x) -> P x) -> P initial
```

`T.ready P` returns `P next` for `continue next` and `\forall (Q: \Prop) -> Q -> Q` for `finish output`.
`T.intro state certificate` proves `T.Holds state` from `certificate: T.ready T.Holds (step state)`.
`T.descent from to termination edge` proves `T.Holds to` from `termination: T.Holds from` and `edge: step from = \continue[State, Output](to)`.

### Run

```text
\run[state-type, result-type](step, initial) \by { accessibility }
\runCase[state-type, result-type](step, initial, transition) \by { accessibility: accessibility-proof, equality: transition-equality }
```

Here `step` is the step function and `accessibility` is a proof of the termination proposition above.
Program uses the termination condition for the reflections of the state type, result type, step function, and initial state.
`\runCase` takes one transition and a proof of its equality to the step result. In Program, it takes a transition computation and an equality proof between their reflections.

### Box

```text
\Box[program-computation-type]
\box[program-computation-type](computation)
\squash[program-computation-type](boxed)
\boxapp(boxed-function, boxed-argument)
```

Box takes a computation type. To box a value, use `\F(A)` and `\return value`.
The computation type and payload may retain Program type and value parameters from modules or definitions.
`\squash` reduces the Program computation as far as possible and reflects the residual term, including terms blocked on input, into Set/Prop.
The type argument of `\box` and `\squash` can be `_` when inference determines it.

```text
\module Boxed(A: \VType, a: A, pending: \U(\F(A))) {
  \definition boxed: \Box[\F(A)] :=
    \box[_](\bind ignored: A <- \force pending \in \return a);
  \definition result: \squash[_](boxed) = a^ := \refl(a^);
}
```

See the [Box parameter tests](../../tests/language/program/box-parameters.md) for local arguments, module instantiation, and residual thunks.

## 8. Macros

Call math macros with `\( ... \)` and named macros with `name!{ ... }`.
Declare them with `\math-macro` and `\macro`, respectively, and introduce macros from other modules with `\use`.
Named macro templates can branch on token sequences with `\tmatch`.
See [macros](macro.md) for definitions, patterns, and expansion rules.

See [CLI usage](../../src/USAGE.md) for execution and diagnostics.
