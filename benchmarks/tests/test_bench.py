"""Check measurement, cancellation, and analysis using small temporary workloads."""
import contextlib
import io
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from unittest.mock import patch

import bench
from common import log_analysis, measurements, sources
from scaling import generators
from workloads.run import coverage


class BenchmarkTests(unittest.TestCase):
    @staticmethod
    def make_checker(checker):
        checker.parent.mkdir(parents=True, exist_ok=True)
        checker.write_text('''#!/usr/bin/env python3
import json, sys
from pathlib import Path
if '--report-json' in sys.argv:
    Path(sys.argv[sys.argv.index('--report-json') + 1]).write_text(json.dumps({
        'version': 2, 'outcome': 'accepted', 'cache': {'verification_reused': False}}))
else:
    assert len(sys.argv) == 2
print('done')
''')
        checker.chmod(0o755)
        return checker

    def test_named_cases_select_the_target_limits_and_output_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("checker", "resolver"):
                suite = root / name
                suite.mkdir()
                (suite / "input.ref").write_text(r"\module Main {}")
                (suite / "cases.toml").write_text(
                    f'[{name}]\ninput = "input.ref"\ndescription = "small {name} workload"\nseconds = 5\n')
            checker = self.make_checker(root / "target/debug/resolve-bench")
            with patch.object(bench, "BENCHMARKS", root), patch.dict(os.environ, {"CARGO_TARGET_DIR": str(root / "target")}), contextlib.redirect_stdout(io.StringIO()):
                for name in ["checker", "resolver"]:
                    args = ["case", name]
                    if name == "checker":
                        args += ["--binary", str(checker), "--cache-mode", "shared", "--seconds", "4"]
                    self.assertEqual(bench.main(args), 0)
                    report = json.loads((root / "runs" / name / "report.json").read_text())
                    self.assertTrue(report["complete"])
                    self.assertEqual(report["seconds_per_run"], 4 if name == "checker" else 5)
                    self.assertEqual(report["case_definition"]["target"], name)
                    row = report["measurements"][0]
                    self.assertEqual(row["case"], name)
                    if name == "checker":
                        self.assertEqual(row["command"][row["command"].index("--cache-dir") + 1],
                                         str(root / "runs/checker/cache"))
                    else:
                        self.assertEqual(row["command"], [str(checker), str(root / "resolver/input.ref")])
                release = root / "target/release build/resolve bench"
                release.parent.mkdir()
                shutil.copy2(shutil.which("false"), release)
                self.assertEqual(bench.main(["case", "resolver", "--binary", str(release)]), 1)
                report = json.loads((root / "runs/resolver/report.json").read_text())
                self.assertFalse(report["complete"])
                self.assertEqual(report["measurements"][0]["command"],
                                 [str(release), str(root / "resolver/input.ref")])
                self.assertEqual(report["measurements"][0]["exit"], 1)
                self.assertEqual(bench.main(["case", "resolver", "--binary", str(root / "missing"),
                                             "--command", shutil.which("true")]), 0)

    def test_duplicate_case_names_across_suites_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for target in ("checker", "resolver"):
                suite = root / target
                suite.mkdir()
                (suite / "input.ref").write_text(r"\module Main {}")
                (suite / "cases.toml").write_text(
                    '[same]\ninput = "input.ref"\ndescription = "duplicate name"\nseconds = 5\n')
            with patch.object(bench, "BENCHMARKS", root):
                with self.assertRaisesRegex(ValueError, "duplicate benchmark case: same"):
                    bench.cases()

    def test_generated_suites_share_the_entry_point_and_measurement_options(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checker = self.make_checker(root / "checker")
            suites = [
                ("cache", ["--depth", "1"], 9),
                ("scaling", ["--sizes", "1", "2", "--width", "2", "--imports", "2", "--runs", "1"], 12),
            ]
            for action, options, count in suites:
                with self.subTest(action=action), contextlib.redirect_stdout(io.StringIO()):
                    output = root / action / "report.json"
                    work = root / action / "scratch"
                    self.assertEqual(bench.main([
                        action, *options, "--binary", str(checker), "--seconds", "5",
                        "--output-mib", "1", "--progress-seconds", "0", "--profile-phases",
                        "--output", str(output), "--work-dir", str(work),
                    ]), 0)
                    report = json.loads(output.read_text())
                    self.assertTrue(report["complete"])
                    self.assertEqual(report["action"], action)
                    self.assertEqual(report["seconds_per_run"], 5)
                    self.assertEqual(report["profile_environment"]["REF_TYPE_PROFILE_PHASES"], "1")
                    self.assertEqual(len(report["measurements"]), count)
                    self.assertEqual(list(work.iterdir()), [])
                    if action == "scaling":
                        self.assertEqual(report["axes"], ["chain", "consumers", "width", "imports", "locals", "resident"])
                        self.assertEqual(report["sizes"], [1, 2])
                        for row in report["measurements"]:
                            self.assertIn("--full-check", row["command"])

    def test_workload_rejects_missing_coverage_and_stale_report(self):
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            root = Path(directory)
            checker = self.make_checker(root / "checker")
            output = root / "report.json"
            args = ["workloads", "--families", "transport", "--sizes", "3", "--binary", str(checker),
                    "--work-dir", str(root / "work"), "--output", str(output)]
            self.assertEqual(bench.main(args), 1)
            row = json.loads(output.read_text())["measurements"][0]
            self.assertIn("verified_modules", row["coverage_error"])
            stale = root / "report-logs/000-transport-3-off.checker.json"
            stale.write_text(json.dumps({
                "version": 2, "outcome": "accepted", "verified_modules": [["sample"], ["sample", "Work"]],
                "checked_modules": [["sample", "Work"]], "execution": {"source_steps": 3},
            }))
            shutil.copy2(shutil.which("true"), checker)
            self.assertEqual(bench.main(args), 1)
            self.assertIsNone(json.loads(output.read_text())["measurements"][0]["checker"])

    def test_focused_coverage_distinguishes_checked_and_reused_targets(self):
        report = {"verified_modules": [["sample"], ["sample", "Focus"]], "checked_modules": [],
                  "cache": {"verification_reused": True}, "execution": {"source_steps": 0}}
        self.assertIsNone(coverage(report, "Focus", "warm"))
        self.assertIsNotNone(coverage(report, "Focus", "edit"))
        report["checked_modules"] = [["sample", "Focus"]]
        self.assertIsNotNone(coverage(report, "Focus", "warm"))
        self.assertIsNotNone(coverage(report, "Focus", "edit"))
        report["execution"]["source_steps"] = 1
        self.assertIsNone(coverage(report, "Focus", "edit"))

    def test_source_digest_tracks_external_modules_without_unrelated_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "original"
            (root / "Outer/Leaf").mkdir(parents=True)
            entry = root / "root.ref"
            entry.write_text(r'\module Outer(A: \Set) { \module Leaf; } \module Sibling;')
            (root / "Outer/Leaf.ref").write_text(r'\module Deeper;')
            nested = root / "Outer/Leaf/Deeper.ref"
            nested.write_text(r'\definition identity[A: \Set][x: A]: A := x;')
            (root / "Sibling.ref").write_text(r'\macro token ("\module Missing;") := \Prop;')
            before = sources.source_digest(entry)
            relocated = Path(directory) / "relocated"
            shutil.copytree(root, relocated)
            self.assertEqual(before, sources.source_digest(relocated / "root.ref"))
            (root / "unrelated.ref").write_text(r'\module Unrelated {}')
            (root / "Outer/unrelated.ref").write_text(r'\module Unrelated {}')
            (root / "ref.toml").write_text('[package]\nname = "unused"\n')
            self.assertEqual(before, sources.source_digest(entry))
            nested.write_text(nested.read_text() + "\n")
            self.assertNotEqual(before, sources.source_digest(entry))
            nested.unlink()
            with self.assertRaises(FileNotFoundError):
                sources.source_digest(entry)

    def test_workspace_axes_use_ordinary_checks_and_sample_the_cache(self):
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            root = Path(directory)
            checker = self.make_checker(root / "checker")
            output = root / "report.json"
            args = ["scaling", "--axes", "checkpoint-disk", "layered", "--sizes", "2", "--width", "1",
                    "--runs", "1", "--binary", str(checker), "--work-dir", str(root / "scratch"),
                    "--output", str(output)]
            self.assertEqual(bench.main(args), 0)
            rows = json.loads(output.read_text())["measurements"]
            self.assertEqual([row["case"] for row in rows], ["checkpoint-disk-2", "layered-2"])
            for row in rows:
                self.assertNotIn("--full-check", row["command"])
                self.assertIn("--cache-dir", row["command"])
                self.assertGreaterEqual(row["cache_peak_allocated_bytes"], row["cache_final_allocated_bytes"])

    def test_layered_workspace_registers_every_edge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = generators.layered(Path(directory), 10, 2)
            bs, cs = ([f"{prefix}{i}" for i in range(10)] for prefix in ("b", "c"))
            packages = sources.packages([root])
            self.assertEqual([path.name for path in packages], ["a", *bs, *cs, "d"])
            for path in packages:
                dependencies = tomllib.loads((path / "ref.toml").read_text())["dependencies"]
                expected = bs if path.name in cs else cs if path.name == "d" else ["a"] if path.name in bs else []
                self.assertEqual(set(dependencies), set(expected))

    def test_disk_sampling_observes_files_deleted_before_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            cache.mkdir()
            program = ("import sys,time; from pathlib import Path; "
                       "p=Path(sys.argv[1]); p.write_bytes(b'x' * 2**20); "
                       "p.with_name('linked').hardlink_to(p); time.sleep(1.2); "
                       "p.with_name('linked').unlink(); p.unlink()")
            result = measurements.measure([sys.executable, "-c", program, str(cache / "object")],
                                          Path(directory) / "run.log", seconds=5, sampled_cache=cache)
            self.assertEqual(result["exit"], 0)
            extra = result["cache_peak_allocated_bytes"] - result["cache_final_allocated_bytes"]
            self.assertLessEqual(2**20, extra)
            self.assertLess(extra, 2**21)

    def test_source_digest_tracks_packages_dependencies_and_workspace_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "original"
            entry = generators.consumers(root, 2, 2)
            before = sources.source_digest(entry)
            relocated = Path(directory) / "relocated"
            shutil.copytree(root, relocated)
            self.assertEqual(before, sources.source_digest(relocated))
            (root / "base/unused.ref").write_text(r'\module Unrelated {}')
            (root / "unused.ref").write_text(r'\module Unrelated {}')
            self.assertEqual(before, sources.source_digest(entry))
            dependency = root / "base/src/root.ref"
            original = dependency.read_text()
            dependency.write_text(original + "\n")
            self.assertNotEqual(before, sources.source_digest(entry))
            dependency.write_text(original)
            manifest = root / "ref.toml"
            manifest.write_text(manifest.read_text() + "\n")
            self.assertNotEqual(before, sources.source_digest(entry))
            consumer = root / "user0"
            before = sources.source_digest(consumer)
            self.assertEqual(before, sources.source_digest(relocated / "user0"))
            dependency.write_text(original + "\n")
            self.assertNotEqual(before, sources.source_digest(consumer))

    def test_package_order_and_cycles(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = sources.package(root, "base", [], r"\module Base {}")
            left = sources.package(root, "left", ["base"], r"\module Left {}")
            right = sources.package(root, "right", ["base"], r"\module Right {}")
            (root / "ref.toml").write_text('[workspace]\npackages=["right","left","right"]\n')
            self.assertEqual(sources.packages([root]), [base, right, left])
            sources.package(root, "base", ["left"], r"\module Base {}")
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                sources.packages([root])

    def test_repetitions_failures_and_duplicate_names_have_distinct_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = sources.package(root, "first", [], r"\module Main {}")
            second = sources.package(root, "second", [], r"\module Main {}")
            # Two independent inputs may intentionally have the same package name.
            (second / 'ref.toml').write_text((first / 'ref.toml').read_text())
            checker = root / "checker"
            checker.write_text('''#!/usr/bin/env python3
import json, sys
from pathlib import Path
args = sys.argv[1:]
failed = (Path(args[0]) / 'fail').exists()
report = Path(args[args.index('--report-json') + 1])
report.write_text(json.dumps({'version':2,'outcome':'rejected' if failed else 'accepted','cache':{'verification_reused':False}}))
print('rejected' if failed else 'accepted')
raise SystemExit(int(failed))
''')
            checker.chmod(0o755)
            output = root / 'report.json'
            arguments = ['libraries', str(first), str(second), '--binary', str(checker),
                         '--output', str(output), '--runs', '2', '--cache-dir', str(root / 'cache'),
                         '--work-dir', str(root / 'work'), '--seconds', '5']
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(bench.main(arguments), 0)
                report = json.loads(output.read_text())
                self.assertTrue(report['complete'])
                self.assertEqual(len(report['measurements']), 4)
                self.assertEqual(len({row['log'] for row in report['measurements']}), 4)
                self.assertEqual(report['summary'][str(first)]['runs'], 2)
                (first / 'fail').touch()
                self.assertEqual(bench.main(arguments), 1)
                report = json.loads(output.read_text())
                self.assertFalse(report['complete'])
                for row in report['measurements']:
                    self.assertEqual(row['completed'], row['path'] == str(second))
                    self.assertEqual(row['stopped_by'], None)

    def test_timeout_reaps_checker_and_keeps_resource_usage(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'run.log'
            result = measurements.measure([sys.executable, '-c', 'import os,time; print(os.getpid(),flush=True); time.sleep(60)'],
                                   log, seconds=.2)
            self.assertEqual(result['stopped_by'], 'time_limit')
            self.assertGreater(result['peak_rss_kib'], 0)
            with self.assertRaises(ProcessLookupError):
                os.kill(int(log.read_text()), 0)

    def test_descendants_are_reaped_after_the_parent_exits(self):
        descendant = ("import os,signal,time; "
                      "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                      "memory = bytearray(64 * 2**20); "
                      "print(os.getpid(),flush=True); time.sleep(60)")
        with tempfile.TemporaryDirectory() as directory:
            for separate_group, parent_exits in [(False, False), (True, False), (True, True)]:
                with self.subTest(separate_group=separate_group, parent_exits=parent_exits):
                    parent = ("import os,subprocess,sys,time; print(os.getpid(),flush=True); "
                              "child = subprocess.Popen([sys.executable,'-c',sys.argv[1]], "
                              f"stdout=subprocess.PIPE,text=True,process_group={0 if separate_group else None}); "
                              "print(child.stdout.readline(),end='',flush=True); "
                              f"time.sleep({0 if parent_exits else 60})")
                    log = Path(directory) / "run.log"
                    result = measurements.measure([sys.executable, "-c", parent, descendant],
                                                  log, seconds=.5)
                    self.assertEqual(result["stopped_by"],
                                     "unfinished_children" if parent_exits else "time_limit")
                    self.assertEqual(result["exit"], 0 if parent_exits else -signal.SIGTERM)
                    self.assertGreater(result["peak_rss_kib"], 50 * 1024)
                    pids = [int(line) for line in log.read_text().splitlines()]
                    self.assertEqual(len(pids), 2)
                    for pid in pids:
                        with self.assertRaises(ProcessLookupError):
                            os.kill(pid, 0)

    def test_process_cleanup_does_not_reap_unrelated_children(self):
        unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
        try:
            with tempfile.TemporaryDirectory() as directory:
                result = measurements.measure([sys.executable, "-c", "pass"],
                                              Path(directory) / "run.log", seconds=5)
                self.assertEqual(result["exit"], 0)
                self.assertIsNone(result["stopped_by"])
                self.assertIsNone(unrelated.poll())
        finally:
            unrelated.terminate()
            unrelated.wait()

    def test_output_limit_reaps_the_process(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "run.log"
            program = ("import os,time; print(os.getpid(),flush=True); "
                       "print('x' * (2 * 2**20),flush=True); time.sleep(60)")
            result = measurements.measure([sys.executable, "-c", program],
                                          log, seconds=5, output_mib=1)
            self.assertEqual(result["stopped_by"], "output_limit")
            with self.assertRaises(ProcessLookupError):
                os.kill(int(log.read_text().splitlines()[0]), 0)

    def test_interruption_saves_a_report_after_reaping_descendants(self):
        descendant = ("import os,signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                      "print(os.getpid(),flush=True); time.sleep(60)")
        parent = ("import os,subprocess,sys,time; print(os.getpid(),flush=True); "
                  "child = subprocess.Popen([sys.executable,'-c',sys.argv[1]], "
                  "stdout=subprocess.PIPE,text=True,process_group=0); "
                  "print(child.stdout.readline(),end='',flush=True); time.sleep(60)")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "root.ref"
            source.write_text(r"\module Main {}")
            output = root / "report.json"
            command = [sys.executable, str(Path(bench.__file__).resolve()), "run", str(source),
                       "--command", shlex.join([sys.executable, "-c", parent, descendant]),
                       "--seconds", "30", "--output", str(output), "--work-dir", str(root / "work")]
            runner = subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            try:
                deadline = time.monotonic() + 5
                pids = []
                while time.monotonic() < deadline:
                    logs = list((root / "report-logs").glob("*.log"))
                    if logs:
                        pids = [int(line) for line in logs[0].read_text().splitlines()]
                        if len(pids) == 2:
                            break
                    if runner.poll() is not None:
                        self.fail(f"runner exited before measurement: {runner.communicate()[1]}")
                    time.sleep(.02)
                self.assertEqual(len(pids), 2)
                runner.send_signal(signal.SIGTERM)
                _, errors = runner.communicate(timeout=8)
                self.assertEqual(runner.returncode, 130, errors)
                report = json.loads(output.read_text())
                self.assertFalse(report["complete"])
                self.assertEqual(report["measurements"][0]["stopped_by"], "interrupted")
                for pid in pids:
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
            finally:
                if runner.poll() is None:
                    runner.kill()
                runner.communicate()

    def test_multiple_profile_sessions_and_incomplete_log(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'run.log'
            log.write_text('''checking declaration child
2ms declaration child (excluding diagnostics)
checking declaration unfinished
cost=kernel.check calls=2 inclusive_us=20 exclusive_us=12 max_us=10
cost=kernel.check calls=3 inclusive_us=30 exclusive_us=18 max_us=20
cost_group=kernel exclusive_us=12
cost_group=kernel exclusive_us=18
cost_count=hits value=2
cost_count=hits value=3
cost_total elapsed_us=20 accounted_us=12 unaccounted_us=8
cost_total elapsed_us=30 accounted_us=18 unaccounted_us=12
''')
            profile = log_analysis.cost_profile(log)
            self.assertEqual(profile['scopes']['kernel.check'],
                             dict(calls=5, inclusive_us=50, exclusive_us=30, max_us=20))
            self.assertEqual(profile['exclusive_group_us'], {'kernel': 30})
            self.assertEqual(profile['counts'], {'hits': 5})
            self.assertEqual(len(profile['sessions']), 2)
            analysis = log_analysis.analyze(log, 10)
            self.assertEqual(analysis['completed_declarations'], 1)
            self.assertEqual(analysis['unfinished_declarations'][0]['label'], 'declaration unfinished')

    def test_raw_command_detects_sources_changed_during_measurement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'root.ref'
            source.write_text(r'\module Main {}')
            program = root / 'edit.py'
            program.write_text('import sys\nfrom pathlib import Path\nPath(sys.argv[1]).write_text("changed")\n')
            output = root / 'report.json'
            with contextlib.redirect_stdout(io.StringIO()):
                code = bench.main(['run', str(source), '--command', f'{sys.executable} {program}',
                                   '--output', str(output), '--work-dir', str(root / 'work')])
            report = json.loads(output.read_text())
            self.assertEqual(code, 1)
            self.assertFalse(report['complete'])
            self.assertFalse(report['measurements'][0]['sources_unchanged'])


if __name__ == '__main__':
    unittest.main()
