"""Check test isolation, execution failures, and explicit expectations."""
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
            valid.replace('expect="accept"', 'expect="accept"\ncache=["reused"]'),
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
            valid.replace('expect="accept"', 'expect="accept"\nfiles=[{path="../escape"}]'),
            valid.replace('expect="accept"', 'expect="accept"\nfiles=[{path="cache", same_as="missing"}]'),
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

    def test_result_checks_only_the_expected_exit_status(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "absent.json"
            for expectation, code in runner.EXPECTATIONS.items():
                with self.subTest(expectation=expectation):
                    runner.check_result({"expect": expectation}, code, path)
                    for status in (-11, 2, 101, 1 - code):
                        with self.subTest(status=status), self.assertRaises(AssertionError):
                            runner.check_result({"expect": expectation}, status, path)

    def test_cache_checks_only_explicit_reuse_expectations(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            for reused in (False, True):
                config = {"expect": "accept", "cache": "reused" if reused else "unused"}
                # Only the field being measured is needed, regardless of other metadata.
                path.write_text(json.dumps({"cache": {"verification_reused": reused}}))
                runner.check_result(config, 0, path)
                with self.assertRaises(AssertionError):
                    runner.check_result({**config, "cache": "unused" if reused else "reused"}, 0, path)
            for report in ('malformed', '[]', '{}', '{"cache":{"verification_reused":0}}'):
                path.write_text(report)
                with self.subTest(report=report), self.assertRaises(AssertionError):
                    runner.check_result(config, 0, path)
            path.unlink()
            with self.assertRaises(AssertionError):
                runner.check_result(config, 0, path)

    def test_scenario_mutates_real_files_and_invokes_separate_processes(self):
        document = '''```toml scenario
id="sequence"
scope="module"
```
```toml step
id="cold"
expect="accept"
```
```ref
first
```
```toml step
id="warm"
expect="accept"
```
```toml step
id="edit"
expect="accept"
```
```ref
second
```
'''
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            checker = directory / "checker.py"
            observations = directory / "observations"
            checker.write_text('''import json, os, sys
from pathlib import Path
assert "--report-json" not in sys.argv
source = Path(sys.argv[2]).parent / "Test.ref"
with Path(sys.argv[1]).open("a") as file:
    file.write(json.dumps([os.getpid(), source.read_text()]) + "\\n")
sys.stdout.buffer.write(b"query" * 20000)
sys.stderr.buffer.write(b"diagnostics" * 20000)
''')
            case, = runner.parse_document(self.document(directory, document))
            runner.run_case(case, [sys.executable, str(checker), str(observations)])
            records = [json.loads(line) for line in observations.read_text().splitlines()]
            self.assertEqual([source for _, source in records], ["first\n", "first\n", "second\n"])
            self.assertEqual(len({pid for pid, _ in records}), 3)

    def test_file_snapshots_detect_changes_additions_and_removals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / "cache"
            cache.mkdir()
            entry = cache / "entry"
            entry.write_bytes(b"original")
            saved = runner.check_files([{"path": "cache", "nonempty": True}], root, {})
            checks = [{"path": "cache", "same_as": "saved"}]
            runner.check_files(checks, root, {"saved": saved})
            entry.write_bytes(b"changed")
            with self.assertRaises(AssertionError):
                runner.check_files(checks, root, {"saved": saved})
            entry.write_bytes(b"original")
            extra = cache / "extra"
            extra.write_bytes(b"extra")
            with self.assertRaises(AssertionError):
                runner.check_files(checks, root, {"saved": saved})
            extra.unlink()
            entry.unlink()
            with self.assertRaises(AssertionError):
                runner.check_files(checks, root, {"saved": saved})
            with self.assertRaises(AssertionError):
                runner.check_files([{"path": "cache", "nonempty": True}], root, {})

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
