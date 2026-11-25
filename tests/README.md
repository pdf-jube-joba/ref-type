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
python3 tests/run.py --filter application_inference
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

## Cases

Compare acceptance and rejection conditions for the same topic in one document and explain the reasons in prose.
Each case runs in an independent source directory.

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
