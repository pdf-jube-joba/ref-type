# Source acceptance and rejection tests

`python3 tests/run.py` extracts sources from Markdown into temporary directories and checks whether the implementation accepts or rejects them.
It uses the Python 3.11+ standard library.
`documents.py` owns case models, Markdown parsing, validation, and discovery.
`run.py` owns temporary sources, checker processes, and result reporting.
The runner invokes a prebuilt CLI independently of the benchmark tools.
Its default binary is `target/debug/cli`, with `CARGO_TARGET_DIR` honored.

```sh
cargo build -p cli --locked
python3 tests/run.py
python3 tests/run.py tests/language --keep-failed
python3 tests/run.py --filter application-inference
python3 tests/run.py --list
python3 tests/run.py --command '/path/to/checker'
python3 -m unittest discover -s tests -v
```

`--command` accepts a command with arguments.
The runner starts it directly as an argument list.
Select test documents or directories with positional arguments; `--filter` narrows cases by name substring or glob.
`--keep-failed` retains failed temporary directories and prints their paths.
`logs/` retains each step's command, stdout, and stderr.
Each invocation has a 30-second timeout, configurable with the runner's `--timeout` option.

## Compatibility contract

Keep this suite tied to the language's external acceptance contract: pass an input path to the checker in its ordinary checking mode and compare the exit code with the expected acceptance or rejection.
The runner must append only the generated entry path to the selected command.
Every case must remain runnable with a checker executable that accepts that path without additional options.

Cases must not depend on optional checker flags, diagnostic wording, JSON report schemas, profiling counters, or implementation APIs.
Standard output and standard error are captured to explain failures; they are not expected-output assertions.
`--command` can select another executable or add options for local experiments, but those options must not become requirements of the cases.

Implementation-specific CLI options, reports, cache statistics, and recovery behavior belong in the owning Rust crates' tests under `src/`.
Internal refactoring must preserve acceptance and rejection for unchanged language rules without requiring changes to this suite's invocation contract.

## Cases

Compare acceptance and rejection conditions for the same topic in one document and explain the reasons in prose.
Each case runs in an independent source directory.

Use lowercase, hyphen-separated case IDs that name the behavior being checked.
The document path already identifies the topic, and `expect` records acceptance or rejection, so IDs do not need either repeated as a prefix.
Use headings that distinguish cases without relying on serial numbers.

Keep examples self-contained and retain only the declarations needed to demonstrate the behavior.
Use names that describe language constructs rather than the mathematical library where a regression was first observed.
Preserve the nesting, instantiation, binding, and refinement relationships needed to reproduce a regression when simplifying it.
For rejection cases, keep unrelated declarations valid and explain the specific invalid operation.
When an example is intended to check a computed result, state the result as a checked equality rather than relying only on query output.

````markdown
## Identity function

The argument proof proves the resulting proposition.

```toml case
id = "identity"
scope = "module"
expect = "accept"
```

```ref
\definition identity[P: \Prop][p: P]: P := p;
```
````

Sources with `scope = "module"` are written as a module body.
The runner generates an external module declaration in `root.ref` and saves its body in `Test.ref`.
Specify a module name and parameters as follows when needed.

```toml
name = "Identity"
parameters = '''A: \Set, a: A'''
```

`scope = "package"` and `scope = "workspace"` extract files from code blocks to relative paths.
If a package manifest is omitted, the runner generates a package named `test`.

See [imports.md](packages/imports.md) for file-layout examples.

Write manifests as `toml file=ref.toml` and other contents as `text file=...`.
`entry` is the input path relative to the source directory; it defaults to `root.ref` for modules and `.` for packages and workspaces.

## Scenarios

Scenarios retain the source directory and run each step in a separate process.
Files immediately after `scenario` form the initial state; files in each `step` replace them before that step runs.
Step settings inherit scenario settings and can override them.
Settings specific to a previous step do not carry over to the next step.

````markdown
```toml scenario
id = "source-change"
scope = "module"
```

```toml step
id = "before"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

```toml step
id = "after"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P;
```
````

`remove = ["src/Base.ref"]` deletes the specified files or directories before execution.

## Observed results

Specify expectations with `accept` or `reject`.
Exit code 0 means acceptance; 1 means rejection.
Other exit codes, crashes, and timeouts are test failures.
Unknown settings, duplicate IDs, unclosed fences, and cases without sources are document errors.

Rust unit and integration tests remain in their owning crates under `src/` and run with `cargo test --workspace --locked`.
The benchmark tool tests run with `python3 -m unittest discover -s benchmarks -v`.

See [libs](https://github.com/pdf-jube-joba/ref-type-libs/tree/main/libs) for mathematical definitions and proofs.
