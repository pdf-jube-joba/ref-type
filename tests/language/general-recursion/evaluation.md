# general-recursion / evaluation

## bind wrong value

bind で束縛する値の型が computation の結果型と一致しない。

```toml case
id = "reject-general-recursion.bind-wrong-value"
scope = "module"
expect = "reject"
name = "InvalidBind"
parameters = '''A: \VType, a: A'''
```

```ref
\definition bad: \F(A) := (\bind x: A <- \thunk (\return a) \in
  \return x);
```

## finish wrong result

finish に渡した値が結果の型を持たない。

```toml case
id = "reject-general-recursion.finish-wrong-result"
scope = "module"
expect = "reject"
name = "FinishWrongResult"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition bad: \RunStep[A, B] := \finish[A, B](a);
```

## let wrong computation

let の束縛対象が要求される Program value になっていない。

```toml case
id = "reject-general-recursion.let-wrong-computation"
scope = "module"
expect = "reject"
name = "InvalidLet"
parameters = '''A: \VType, a: A'''
```

```ref
\definition bad: \F(A) := (\let x: A := \return a \in
  \return x);
```

## program case wrong branch count

Program case の分岐数が constructor の数と一致しない。

```toml case
id = "reject-general-recursion.program-case-wrong-branch-count"
scope = "module"
expect = "reject"
name = "IncompleteProgramCase"
```

```ref
\inductive Bit: \VType :=
| zero: Bit
| one: Bit
;
\definition bad: (Bit ~> \F(Bit)) :=
  (\cfun (x: Bit) => \match (x) \in Bit \with {
    | zero : \return(Bit::zero)
    });
```

## block syntax

block 内の sequencing が Program value と computation の束縛を保つ。

```toml case
id = "accept-general-recursion.block-syntax"
scope = "module"
expect = "accept"
name = "Blocks"
```

```ref
\inductive Bit: \VType :=
| zero: Bit
| one: Bit
;
\definition identity[x: Bit]: \F(Bit) := \return x;
\definition first[x, y: Bit]: \F(Bit) := \return x;
\definition second[x: Bit][y: Bit]: \F(Bit) := \return y;
\definition suspended: \U(Bit ~> \F(Bit)) := \thunk identity;
\definition result: \F(Bit) :=
  \program {
    \let x: Bit := Bit::one \then
    \bind x: Bit <- \force suspended x \then
    \bind x: Bit <- first x Bit::zero \then
    \bind result: Bit <- \match x \in Bit \with {
      | zero : \return Bit::zero
      | one :
          \let y: Bit := x \in
          second Bit::zero y
    } \then
    \return result
  };
\eval result;
\check result: \F(Bit);
```

## continue

continue の状態を遷移に渡して実行を継続できる。

```toml case
id = "accept-general-recursion.continue"
scope = "module"
expect = "accept"
name = "RunContinue"
```

```ref
\inductive State: \VType :=
| first: State
| last: State
;

\definition step: \U((State ~> \F(\RunStep[State, State]))) :=
  \thunk((\cfun (state: State) => \match (state) \in State \with {
    | first : \return(\continue[State, State](State::last))
    | last : \return(\finish[State, State](State::last))
    }));


\definition Terminates [s: State^]: \Prop :=
  \forall (P: State^ -> \Prop) ->
    (\forall (x: State^) ->
      (\step-match t: \RunStep[State^, State^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ x) -> P x) -> P s;
\definition lastTerminates: Terminates State^::last :=
  \fun (predicate: State^ -> \Prop) (h: _) => h State^::last (\fun (Q: \Prop) (q: Q) => q);
\definition firstTerminates: Terminates State^::first :=
  \fun (predicate: State^ -> \Prop) (h: _) => h State^::first (lastTerminates predicate h);

\definition result: \F(State) :=
  \run[State, State](step, State::first) \by { firstTerminates };
\normalize \run[State, State](step, State::first) \by { firstTerminates };
```

## finish

finish が持つ結果を run の結果として取り出せる。

```toml case
id = "accept-general-recursion.finish"
scope = "module"
expect = "accept"
name = "RunFinish"
parameters = '''A: \VType,
  B: \VType,
  a: A,
  b: B'''
```

```ref
\definition step: \U((A ~> \F(\RunStep[A, B]))) :=
  \thunk((\cfun (x: A) => \return(\finish[A, B](b))));
\definition Terminates [s: A^]: \Prop :=
  \forall (P: A^ -> \Prop) ->
    (\forall (x: A^) ->
      (\step-match t: \RunStep[A^, B^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ x) -> P x) -> P s;
\definition terminates: \forall (s: A^) -> Terminates s :=
  \fun (s: A^) (P: _) (h: _) => h s (\fun (Q: \Prop) (q: Q) => q);
\definition result: \F(B) := \run[A, B](step, a) \by { terminates a^ };

\eval \run[A, B](step, a) \by { terminates a^ };
\normalize \run[A, B](step, a) \by { terminates a^ };
```

## forms

Program の value と computation の各構文を対応する型で使える。

```toml case
id = "accept-general-recursion.forms"
scope = "module"
expect = "accept"
name = "ProgramForms"
parameters = '''A: \VType,
  a: A,
  suspended: \U(\F(A))'''
```

```ref
\definition identity[x: A]: \F(A) := \return x;
\definition inferred[x: _]: \F(A) := \return x;
\definition thunked: \U(A ~> \F(A)) := \thunk identity;
\definition forced: A ~> \F(A) := \force thunked;
\definition applied: \F(A) := identity a;
\definition sequenced: \F(A) :=
  \bind x: A <- \return a \in \return x;
\definition valueLet: \F(A) :=
  \let x: A := a \in \return x;
\definition forceParameter: \F(A) := \force suspended;
\eval identity;
\eval applied;
```

## ill typed evaluation

Set/Prop の型が合わない適用も、評価用の query では簡約できる。

```toml case
id = "accept-general-recursion.ill-typed-evaluation"
scope = "module"
expect = "accept"
name = "IllTypedEvaluation"
```

```ref
\eval (\fun (x: \SetKind(0)) => x) \Set(0);
\normalize (\fun (x: \SetKind(0)) => x) \Set(0);
```

## mccarthy 91

停止証明を持つ McCarthy 91 の再帰的実行を記述できる。

```toml case
id = "accept-general-recursion.mccarthy-91"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
/* McCarthy's 91 function as a CBPV state machine.
 *
 *   M(n) = n - 10       when n > 100
 *          M(M(n + 11)) otherwise
 *
 * `pending` is the continuation for the outer call in M(M(n + 11)).
 * Inspecting the threshold and adding constants are also explicit machine
 * states, so every transition remains a CBPV computation returning RunStep.
 */
\module McCarthy91 {
  \inductive Nat: \VType :=
  | zero: Nat
  | succ: Nat -> Nat
  ;

  \inductive Continuation: \VType :=
  | done: Continuation
  | pending: Continuation -> Continuation
  ;

  \inductive State: \VType :=
  | call: Nat -> Continuation -> State
  | inspect: Nat -> Nat -> Nat -> Continuation -> State
  | raise: Nat -> Nat -> Continuation -> State
  | raiseAndCall: Nat -> Nat -> Continuation -> State
  ;

  \definition ten: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ Nat::zero)))))))));
  \definition eleven: Nat := Nat::succ ten;
  \definition twenty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ ten)))))))));
  \definition thirty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ twenty)))))))));
  \definition forty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ thirty)))))))));
  \definition fifty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ forty)))))))));
  \definition sixty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ fifty)))))))));
  \definition seventy: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ sixty)))))))));
  \definition eighty: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ seventy)))))))));
  \definition ninety: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ eighty)))))))));
  \definition ninetyOne: Nat := Nat::succ ninety;
  \definition hundred: Nat :=
    Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ
      (Nat::succ (Nat::succ (Nat::succ (Nat::succ (Nat::succ ninety)))))))));
  \definition hundredOne: Nat := Nat::succ hundred;

  \definition step:
    \U((State ~> \F(\RunStep[State, Nat]))) :=
    \thunk((\cfun (state: State) => \match (state) \in State \with {
      | call argument continuation :
          \return(\continue[State, Nat](State::inspect
              argument
              argument
              hundredOne
              continuation))
      | inspect original remaining threshold continuation :
          \match (threshold) \in Nat \with {
          | zero :
              /* original >= 101, and remaining + 91 = original - 10. */
              \return(\continue[State, Nat](State::raise remaining ninetyOne continuation))
          | succ smallerThreshold :
              \match (remaining) \in Nat \with {
              | zero :
                  /* original <= 100: first evaluate M(original + 11),
                   * then the pending continuation evaluates M once more.
                   */
                  \return(\continue[State, Nat](State::raiseAndCall
                      original
                      eleven
                      (Continuation::pending continuation)))
              | succ smallerRemaining :
                  \return(\continue[State, Nat](State::inspect
                      original
                      smallerRemaining
                      smallerThreshold
                      continuation))
              }
          }
      | raise result additions continuation :
          \match (additions) \in Nat \with {
          | zero :
              \match (continuation) \in Continuation \with {
              | done :
                  \return(\finish[State, Nat](result))
              | pending rest :
                  \return(\continue[State, Nat](State::call result rest))
              }
          | succ smallerAdditions :
              \return(\continue[State, Nat](State::raise
                  (Nat::succ result)
                  smallerAdditions
                  continuation))
          }
      | raiseAndCall argument additions continuation :
          \match (additions) \in Nat \with {
          | zero :
              \return(\continue[State, Nat](State::call argument continuation))
          | succ smallerAdditions :
              \return(\continue[State, Nat](State::raiseAndCall
                  (Nat::succ argument)
                  smallerAdditions
                  continuation))
          }
      }));

  /* This execution fixture takes the termination theorem as an explicit premise. */

  \module Certified(terminates: \forall (n: Nat^) ->
    (\forall (P: State^ -> \Prop) ->
      (\forall (s: State^) ->
        (\step-match t: \RunStep[State^, Nat^] \return \Prop \with {
          | \continue next: P next
          | \finish output: \forall (Q: \Prop) -> Q -> Q
        }) (step^ s) -> P s) -> P (State^::call n Continuation^::done))) {
  \definition mcCarthy91: (Nat ~> \F(Nat)) :=
    (\cfun (argument: Nat) => \run[State, Nat](step, State::call argument Continuation::done) \by { terminates argument });

  \normalize (mcCarthy91 hundred);
  }
}
```

## 型が合わない Program application の評価

Program の return を関数として適用した式も、評価用の query では簡約不能な式として保持できる。

```toml case
id = "accept-general-recursion.raw-ill-typed-program-application-evaluation"
scope = "module"
expect = "accept"
name = "RawIllTypedProgramEvaluation"
parameters = '''A: \VType,
  a: A'''
```

```ref
\eval ((\return(a)) a);
\normalize ((\return(a)) a);
```

## rose map

再帰的な木を停止証明付きの Program で写せる。

```toml case
id = "accept-general-recursion.rose-map"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
/* Rose-tree map as a CBPV state machine.
 *
 * A rose value is a forest in first-child / next-sibling representation.  A
 * single tree is a node whose siblings field is empty.  The continuation
 * remembers enough context to rebuild both the children and the siblings
 * after their recursive traversals have returned.
 */
\module RoseMap(
  A: \VType,
  B: \VType,
  function: \U((A ~> \F(B)))
) {
  \inductive InputRose: \VType :=
  | empty: InputRose
  | node: A -> InputRose -> InputRose -> InputRose
  ;

  \inductive OutputRose: \VType :=
  | empty: OutputRose
  | node: B -> OutputRose -> OutputRose -> OutputRose
  ;

  \inductive Continuation: \VType :=
  | done: Continuation
  | afterChildren:
      B -> InputRose -> Continuation -> Continuation
  | afterSiblings:
      B -> OutputRose -> Continuation -> Continuation
  ;

  \inductive State: \VType :=
  | visit: InputRose -> Continuation -> State
  | resume: Continuation -> OutputRose -> State
  ;

  \definition step:
    \U((State ~> \F(\RunStep[State, OutputRose]))) :=
    \thunk((\cfun (state: State) => \match (state) \in State \with {
      | visit input continuation :
          \match (input) \in InputRose \with {
          | empty :
              \return(\continue[State, OutputRose](State::resume
                  continuation
                  OutputRose::empty))
          | node label children siblings :
              (\bind mappedLabel: B <- ((\force(function)) label) \in \return(\continue[State, OutputRose](State::visit
                    children
                    (Continuation::afterChildren
                      mappedLabel
                      siblings
                      continuation))))
          }
      | resume continuation mapped :
          \match (continuation) \in Continuation \with {
          | done :
              \return(\finish[State, OutputRose](mapped))
          | afterChildren mappedLabel siblings rest :
              \return(\continue[State, OutputRose](State::visit
                  siblings
                  (Continuation::afterSiblings
                    mappedLabel
                    mapped
                    rest)))
          | afterSiblings mappedLabel mappedChildren rest :
              \return(\continue[State, OutputRose](State::resume
                  rest
                  (OutputRose::node mappedLabel mappedChildren mapped)))
          }
      }));

  /* The state-machine fixture receives its termination theorem at this boundary. */
  \module Certified(terminates: \forall (input: InputRose^) ->
    (\forall (P: State^ -> \Prop) ->
      (\forall (s: State^) ->
        (\step-match t: \RunStep[State^, OutputRose^] \return \Prop \with {
          | \continue next: P next
          | \finish output: \forall (Q: \Prop) -> Q -> Q
        }) (step^ s) -> P s) -> P (State^::visit input Continuation^::done))) {
  \definition map: (InputRose ~> \F(OutputRose)) :=
    (\cfun (input: InputRose) => \run[State, OutputRose](step, State::visit
          input
          Continuation::done) \by { terminates input });
  }
}
```

## run case

runCase は実行中の遷移 computation と対応する証明を使える。

```toml case
id = "accept-general-recursion.run-case"
scope = "module"
expect = "accept"
name = "ExplicitRunCase"
parameters = '''A: \VType,
  B: \VType,
  step: \U((A ~> \F(\RunStep[A, B]))),
  initial: A,
  termination: (\forall (P: A^ -> \Prop) ->
    (\forall (s: A^) ->
      (\step-match t: \RunStep[A^, B^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ s) -> P s) -> P initial^)'''
```

```ref
\definition result: \F(B) :=
  \runCase[A, B](step, initial, ((\force(step)) initial)) \by { accessibility: termination, equality:
      \refl(step^ initial^) };
```

## step match

parameter を持つ遷移の結果を case で分解できる。

```toml case
id = "accept-general-recursion.step-match"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ParameterizedStepMatch(A: \VType) {
  \definition select: \U(\RunStep[A, A] ~> \F(A)) :=
    \step-match \RunStep[A, A] \return \F(A) \with {
      | \continue next: \return next
      | \finish output: \return output
    };
}

\module StepMatch {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Bit: \VType :=
  | zero: Bit
  | one: Bit
  ;
  \import \root.ParameterizedStepMatch[A := Bit] \as Param;

  \definition same: \forall (x: \RunStep[Unit, Unit]) -> x = x :=
    \step-match x: \RunStep[Unit, Unit] \return x = x \with {
      | \continue next: \refl(\continue[Unit, Unit](next))
      | \finish output: \refl(\finish[Unit, Unit](output))
    };
  \definition finishedStep: \RunStep[Unit, Unit] :=
    \finish[Unit, Unit](Unit::unit);
  \definition choose: \U(\RunStep[Bit, Bit] ~> \F(Bit)) :=
    \step-match \RunStep[Bit, Bit] \return \F(Bit) \with {
      | \continue next: \return next
      | \finish output: \return output
    };
  \definition continueResult: \F(Bit) :=
    (\force choose) (\continue[Bit, Bit](Bit::zero));
  \definition finishResult: \F(Bit) :=
    (\force choose) (\finish[Bit, Bit](Bit::one));
  \definition boxedContinue: \Box[\F(Bit)] := \box[_](continueResult);

  \check same (\continue[Unit, Unit](Unit::unit)):
    \continue[Unit, Unit](Unit::unit) = \continue[Unit, Unit](Unit::unit);
  \normalize same (\finish[Unit, Unit](Unit::unit));
  \normalize same finishedStep;
  \normalize continueResult;
  \normalize finishResult;
  \normalize (\force Param.select) (\finish[Bit, Bit](Bit::one));
  \normalize \squash[_](boxedContinue);
}
```

## stuck

開いた thunk の force は簡約できない computation として保持される。

```toml case
id = "accept-general-recursion.stuck"
scope = "module"
expect = "accept"
name = "StuckComputation"
parameters = '''A: \VType,
  suspended: \U(\F(A))'''
```

```ref
\normalize \force(suspended);
```


## branch と結果の異なる universe

高い universe の RunStep を消去し、低い universe の固定した値を返せる。

```toml case
id = "step_match_distinguishes_branch_and_result_sorts"
scope = "module"
expect = "accept"
name = "InvalidMotive"
parameters = '''A: \Set(2), a: A, B: \Set(0), b: B'''
```

```ref
\definition bad: B := (\step-match r: \RunStep[A, A] \return B \with {
  | \continue x: b
  | \finish x: b
}) \finish[A, A](a);
```
