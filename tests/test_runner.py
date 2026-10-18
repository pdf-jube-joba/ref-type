"""Check that the acceptance runner cannot mistake broken execution for rejection."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("acceptance_runner", ROOT / "tests/tests.py")
runner = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = runner
spec.loader.exec_module(runner)


class RunnerTests(unittest.TestCase):
    def document(self, directory, text):
        path = Path(directory) / "test.md"
        path.write_text(text, encoding="utf-8")
        return path

    def test_definition_errors_are_not_silently_skipped(self):
        valid = '```toml case\nid="test"\nscope="module"\nexpect="accept"\n```\n```ref\nbody\n```\n'
        malformed = [
            valid.replace('expect="accept"', 'expect=["accept"]'),
            valid.replace('scope="module"', 'scope=["module"]'),
            valid.replace('expect="accept"', 'expect="accept"\nexepct="accept"'),
            valid.replace('toml case', 'toml caes'),
            valid.replace('```ref', '```ref file=../escaped.ref'),
            valid.replace('```ref', '```ref file=/tmp/escaped.ref'),
            valid.replace('```ref', '```rust file=root.ref'),
            valid.replace('```ref\nbody\n```\n', ''),
            valid + valid,
            valid.removesuffix('```\n'),
            valid.replace('toml case', 'toml step'),
            valid.replace('expect="accept"', 'expect="accept"\nargs=["--report-json=/tmp/fake.json"]'),
            valid.replace('expect="accept"', 'expect="accept"\nstdout_same_as="missing"'),
            valid.replace('expect="accept"', 'expect="accept"\nchecks=[{stream="stderr", pattern="["}]'),
            valid.replace('expect="accept"', 'expect="accept"\nchecks=[{stream="stderr", count=1}]'),
            valid.replace('expect="accept"', 'expect="accept"\nchecks=[{stream="stderr", pattern="x", sum_equals="y"}]'),
            valid.replace('expect="accept"', 'expect="accept"\nchecks=[{stream="stderr", contains=["x"], typo=1}]'),
            valid.replace('expect="accept"', 'expect="interrupted"'),
            valid.replace('expect="accept"', 'expect="accept"\ninterrupt={stderr="ready"}'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            for text in malformed:
                with self.subTest(text=text), self.assertRaises(runner.DefinitionError):
                    runner.parse_document(self.document(directory, text))
            with self.assertRaises(runner.DefinitionError):
                runner.discover([self.document(directory, "# Empty document\n")])

    def test_variable_fences_and_unicode_sources_preserve_content(self):
        text = '# 文書\n\n~~~~toml case\nid="test"\nscope="module"\nexpect="accept"\n~~~~\n\n````ref\n/* 日本語と ``` */\nbody\n````\n'
        with tempfile.TemporaryDirectory() as directory:
            case, = runner.parse_document(self.document(directory, text))
            self.assertEqual(case.sources[0].text, '/* 日本語と ``` */\nbody\n')

    def test_crashes_missing_reports_and_exit_disagreements_fail_negative_cases(self):
        config = {"expect": "reject"}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            for status, report in [
                (1, None), (1, "malformed"), (-11, {"outcome": "rejected"}),
                (2, {"outcome": "internal-error"}), (0, {"outcome": "rejected"}),
                (1, {"outcome": "accepted"}),
            ]:
                with self.subTest(status=status, report=report):
                    if report is None:
                        path.unlink(missing_ok=True)
                    elif isinstance(report, str):
                        path.write_text(report)
                    else:
                        path.write_text(json.dumps({"version": 1, **report}))
                    with self.assertRaises(AssertionError):
                        runner.check_result(config, status, b"", b"", path, {})

    def test_scenario_mutates_real_files_and_invokes_separate_processes(self):
        document = '''```toml scenario
id="sequence"
scope="module"
```
```toml step
id="first"
expect="accept"
stdout="first\\n"
```
```ref
first
```
```toml step
id="repeat"
expect="accept"
stdout_same_as="first"
```
```toml step
id="edit"
expect="accept"
stdout="second\\n"
```
```ref
second
```
'''
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            checker = directory / "checker.py"
            pids = directory / "pids"
            checker.write_text('''import json, os, sys
from pathlib import Path
source = Path(sys.argv[2]).parent / "Test.ref"
with Path(sys.argv[1]).open("a") as file:
    file.write(str(os.getpid()) + "\\n")
sys.stdout.write(source.read_text())
report = Path(sys.argv[sys.argv.index("--report-json") + 1])
report.write_text(json.dumps({"version": 1, "outcome": "accepted"}))
''')
            case, = runner.parse_document(self.document(directory, document))
            runner.run_case(case, [sys.executable, str(checker), str(pids)])
            self.assertEqual(len(set(pids.read_text().splitlines())), 3)

    def test_output_checks_detect_missing_repeated_and_misordered_results(self):
        streams = {"stderr": b"start\npart 1\npart 2\ntotal 3\nfinish\n"}
        checks = [
            {"stream": "stderr", "contains": ["start"], "absent": ["error"],
             "ordered": ["start", "finish"]},
            {"stream": "stderr", "pattern": r"^part (\d+)$", "count": 2,
             "sum_equals": r"^total (\d+)$", "positive": True},
        ]
        runner.check_output(checks, streams)
        failures = [
            {"contains": ["missing"]}, {"absent": ["start"]},
            {"ordered": ["finish", "start"]}, {"pattern": "missing"},
            {"pattern": "part", "count": 1},
            {"pattern": r"^part (\d+)$", "sum_equals": r"^part (\d+)$"},
            {"pattern": r"^part (\d+)$", "sum_equals": r"^part (2)$"},
        ]
        for check in failures:
            with self.subTest(check=check), self.assertRaises(AssertionError):
                runner.check_output([{"stream": "stderr", **check}], streams)

    def test_timeout_stops_the_checker_and_retains_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = root / "wait.py"
            script.write_text('import os, time\nprint(os.getpid(), flush=True)\ntime.sleep(60)\n')
            with self.assertRaisesRegex(AssertionError, 'exceeded'):
                runner.invoke([sys.executable, str(script)], root, os.environ.copy(), 0.2, root / 'logs')
            pid = int((root / 'logs/stdout').read_text())
            if os.name == 'posix':
                with self.assertRaises(ProcessLookupError):
                    os.kill(pid, 0)

    def test_keep_failed_preserves_only_failed_directories(self):
        with runner.work_directory(True) as successful:
            (successful / 'source').write_text('success')
        self.assertFalse(successful.exists())
        captured = io.StringIO()
        failed = None
        try:
            with contextlib.redirect_stderr(captured), self.assertRaises(RuntimeError):
                with runner.work_directory(True) as failed:
                    (failed / 'source').write_text('failure')
                    raise RuntimeError('failed')
            self.assertEqual((failed / 'source').read_text(), 'failure')
            self.assertIn(str(failed), captured.getvalue())
        finally:
            if failed is not None:
                shutil.rmtree(failed)


if __name__ == "__main__":
    unittest.main()
