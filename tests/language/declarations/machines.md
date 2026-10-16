# declarations / machines

## machine box parameters

Box の computation type と payload に module parameter を使える。

```toml case
id = "accept-declarations.machine_box_parameters"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BundleSignatures {
/* Program implementations, specifications, and terminating transitions. */
\structure Correspondence {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
}

\definition Ready(State, Output: \Set)(P: State -> \Prop): \RunStep[State, Output] -> \Prop :=
  \step-match t: \RunStep[State, Output] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };

\definition Terminates(State, Output: \Set)(step: State -> \RunStep[State, Output])(s: State): \Prop :=
  \forall (P: State -> \Prop) ->
    (\forall (x: State) -> Ready State Output P (step x) -> P x) -> P s;

\structure Machine {
  State: \VType,
  Output: \VType,
  step: \U(State ~> \F(\RunStep[State, Output])),
  terminates: \forall (s: State^) -> Terminates State^ Output^ step^ s,
  run: \U(State ~> \F(Output)) := \thunk (\cfun (s: State) =>
    \run[State, Output](step, s) \by { terminates s }),
}
\definition runBox(machine: Machine): \Box[machine.State ~> \F(machine.Output)] :=
  \box[_](\force machine.run);
}
\module Open(A: \VType, a: A) {
  \import \root.BundleSignatures[] \as Signatures;
  \definition echo: Signatures.Machine := Signatures.Machine {
    State := A, Output := A,
    step := \thunk(\cfun(s: A) => \return(\finish[A, A](s))),
    terminates := \fun(s: A^)(P: _)(h: _) => h s (\fun(Q: \Prop)(q: Q) => q),
  };
  \definition runbox: \Box[A ~> \F(A)] := Signatures.runBox echo;
  \definition agrees:
    \squash[_](\boxapp(runbox, \box[_](\return a))) = a^ := \refl(a^);
}
```

## machine step

machine の遷移が要求される型を持たない。

```toml case
id = "reject-declarations.machine_step"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module BundleSignatures {
/* Program implementations, specifications, and terminating transitions. */
\structure Correspondence {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
}

\definition Ready(State, Output: \Set)(P: State -> \Prop): \RunStep[State, Output] -> \Prop :=
  \step-match t: \RunStep[State, Output] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };

\definition Terminates(State, Output: \Set)(step: State -> \RunStep[State, Output])(s: State): \Prop :=
  \forall (P: State -> \Prop) ->
    (\forall (x: State) -> Ready State Output P (step x) -> P x) -> P s;

\structure Machine {
  State: \VType,
  Output: \VType,
  step: \U(State ~> \F(\RunStep[State, Output])),
  terminates: \forall (s: State^) -> Terminates State^ Output^ step^ s,
  run: \U(State ~> \F(Output)) := \thunk (\cfun (s: State) =>
    \run[State, Output](step, s) \by { terminates s }),
}
}
\module WrongStep {
  \import \root.BundleSignatures[] \as Signatures;
  \inductive Unit: \VType := | unit: Unit;
  \definition invalid: Signatures.Machine := Signatures.Machine {
    State := Unit, Output := Unit,
    step := \thunk(\cfun(s: Unit) => \return s),
    terminates := \fun(s: Unit^) => \refl(s),
  };
}
```

## bundles

bundle の実装と仕様と停止証明が対応している。

```toml case
id = "accept-declarations.bundles"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BundleSignatures {
/* Program implementations, specifications, and terminating transitions. */
\structure Correspondence {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
}

\definition Ready(State, Output: \Set)(P: State -> \Prop): \RunStep[State, Output] -> \Prop :=
  \step-match t: \RunStep[State, Output] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };

\definition Terminates(State, Output: \Set)(step: State -> \RunStep[State, Output])(s: State): \Prop :=
  \forall (P: State -> \Prop) ->
    (\forall (x: State) -> Ready State Output P (step x) -> P x) -> P s;

\structure Machine {
  State: \VType,
  Output: \VType,
  step: \U(State ~> \F(\RunStep[State, Output])),
  terminates: \forall (s: State^) -> Terminates State^ Output^ step^ s,
  run: \U(State ~> \F(Output)) := \thunk (\cfun (s: State) =>
    \run[State, Output](step, s) \by { terminates s }),
}
}
\module Bundles {
  \import \root.BundleSignatures[] \as Signatures;
  \inductive Unit: \VType := | unit: Unit;
  \structure Fixed: \Set { value: Unit^, fixed: value = Unit^::unit }
  \definition fixed: Fixed := Fixed { value := Unit^::unit, fixed := \refl(Unit^::unit) };
  \definition value(s: Fixed): Unit^ := s.value;
  \definition law(s: Fixed): s.value = Unit^::unit := s.fixed;
  \check law fixed: Unit^::unit = Unit^::unit;
  \definition computation: value fixed = Unit^::unit := \refl(Unit^::unit);

  \definition identityProgram: \U(Unit ~> \F(Unit)) := \thunk(\cfun(x: Unit) => \return x);
  \definition identity: Signatures.Correspondence := Signatures.Correspondence {
    T := \U(Unit ~> \F(Unit)),
    program := identityProgram,
    specification := \fun(x: Unit^) => x,
    coherence := \refl(identityProgram^),
  };
  \definition copy: identity.T := identity.program;
  \check identity.coherence: copy^ = identity.specification;

  \definition echo: Signatures.Machine := Signatures.Machine {
    State := Unit,
    Output := Unit,
    step := \thunk(\cfun(s: Unit) => \return(\finish[Unit, Unit](s))),
    terminates := \fun(s: Unit^) (P: _) (h: _) => h s (\fun(Q: \Prop)(q: Q) => q),
  };
  \structure Nested { machine: Signatures.Machine, correspondence: Signatures.Correspondence }
  \definition wrapped: Nested := Nested {
    machine := echo,
    correspondence := Signatures.Correspondence {
      T := identity.T,
      program := echo.run,
      specification := identity.specification,
      coherence := \axiom:funext(echo.run^, identity.specification, \fun(s: Unit^) => \refl(s)),
    },
  };
  \check wrapped.correspondence.coherence: wrapped.correspondence.program^ = identity.specification;
  \definition output: \F(echo.Output) := (\force echo.run) Unit::unit;
  \definition runbox: \Box[echo.State ~> \F(echo.Output)] := \box[echo.State ~> \F(echo.Output)](\force echo.run);
  \definition input: \Box[\F(echo.State)] := \box[\F(echo.State)](\return Unit::unit);
  \definition boxedResult: \squash[_](\boxapp(runbox, input)) = Unit^::unit := \refl(Unit^::unit);
  \definition inlineBoxedResult:
    \squash[_](\boxapp(\box[echo.State ~> \F(echo.Output)](\force echo.run), input)) = Unit^::unit :=
    \refl(Unit^::unit);
  \definition implicitBeforeRun: echo.run^ Unit^::unit = Unit^::unit :=
    (\fun (x: _) (h: x = Unit^::unit) => h) _ (\refl(echo.run^ Unit^::unit));
  \check echo.terminates Unit^::unit: Signatures.Terminates Unit^ Unit^ echo.step^ Unit^::unit;
}
```

## closed program namespace

閉じた Program namespace を Box の型に使える。

```toml case
id = "accept-declarations.closed_program_namespace"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Generic(A: \VType) {
  \structure Correspondence { T: \VType, program: T, specification: T^, coherence: program^ = specification }

  \module Identity {
    \definition T: \VType := \U(A ~> \F(A));
    \definition program: T := \thunk(\cfun(x: A) => \return x);
  }
  \definition boxed: Correspondence := Correspondence {
    T := \U(A ~> \F(A)), program := Identity[].program,
    specification := \fun(x: A^) => x, coherence := \refl(Identity[].program^),
  };
}
\module Use {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Generic[A := Unit] \as G;
  \definition program: \U(Unit ~> Unit ~> Unit ~> \F(Unit)) :=
    \thunk(\cfun(x: Unit)(y: Unit)(z: Unit) => (\force G.boxed.program) x);
  \definition read(x: Unit^): Unit^ := G.boxed.program^ x;
  \definition identity: read Unit^::unit = Unit^::unit := \refl(Unit^::unit);
}
```

## machines

machine の状態と遷移と停止証明の型が対応している。

```toml case
id = "accept-declarations.machines"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BundleSignatures {
/* Program implementations, specifications, and terminating transitions. */
\structure Correspondence {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
}

\definition Ready(State, Output: \Set)(P: State -> \Prop): \RunStep[State, Output] -> \Prop :=
  \step-match t: \RunStep[State, Output] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };

\definition Terminates(State, Output: \Set)(step: State -> \RunStep[State, Output])(s: State): \Prop :=
  \forall (P: State -> \Prop) ->
    (\forall (x: State) -> Ready State Output P (step x) -> P x) -> P s;

\structure Machine {
  State: \VType,
  Output: \VType,
  step: \U(State ~> \F(\RunStep[State, Output])),
  terminates: \forall (s: State^) -> Terminates State^ Output^ step^ s,
  run: \U(State ~> \F(Output)) := \thunk (\cfun (s: State) =>
    \run[State, Output](step, s) \by { terminates s }),
}
}
\module Machines {
  \import \root.BundleSignatures[] \as Signatures;
  \inductive State: \VType := | first: State | last: State;
  \definition step: \U(State ~> \F(\RunStep[State, State])) :=
    \thunk(\cfun(s: State) => \match s \in State \with {
      | first: \return(\continue[State, State](State::last))
      | last: \return(\finish[State, State](State::last))
    });
  \definition Terminates(s: State^): \Prop := Signatures.Terminates State^ State^ step^ s;
  \definition lastTerminates: Terminates State^::last :=
    \fun(predicate: State^ -> \Prop)(h: _) => h State^::last (\fun(Q: \Prop)(q: Q) => q);
  \definition certificate: \forall(s: State^) -> Terminates s :=
    \induction(s: State^) \return Terminates s \with {
      | first: \fun(predicate: State^ -> \Prop)(h: _) => h State^::first (lastTerminates predicate h)
      | last: lastTerminates
    };
  \definition walk: Signatures.Machine := Signatures.Machine { State := State, Output := State, step := step, terminates := certificate };
  \definition first: walk.State := walk.State::first;
  \definition result: \F(walk.Output) := (\force walk.run) first;
  \definition computed: result^ = walk.Output^::last := \refl(walk.Output^::last);
  \definition runbox: \Box[walk.State ~> \F(walk.Output)] := \box[walk.State ~> \F(walk.Output)](\force walk.run);
  \definition input: \Box[\F(walk.State)] := \box[\F(walk.State)](\return first);
  \definition boxedComputed: \squash[_](\boxapp(runbox, input)) = walk.Output^::last := \refl(walk.Output^::last);
  \definition specification: State^ -> State^ :=
    \induction(s: State^) \return State^ \with {
      | first: State^::last
      | last: State^::last
    };
  \definition finish: Signatures.Correspondence := Signatures.Correspondence {
    T := \U(walk.State ~> \F(walk.Output)),
    program := walk.run,
    specification := specification,
    coherence := \axiom:funext(walk.run^, specification,
      \induction(s: State^) \return walk.run^ s = specification s \with {
        | first: \refl(State^::last)
        | last: \refl(State^::last)
      }),
  };
}
\module Consumer {
  \import \root.Machines[] \as M;
  \definition run: M.walk.State ~> \F(M.walk.Output) := \force M.walk.run;
  \definition input: \Box[\F(M.walk.State)] := \box[\F(M.walk.State)](\return M.walk.State::first);
  \definition computed: \squash[_](\boxapp(M.runbox, input)) = M.walk.Output^::last := \refl(M.walk.Output^::last);
}
```

