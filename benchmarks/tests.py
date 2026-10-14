"""Check measurement, cancellation, and analysis using small temporary workloads."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

import bench


class BenchmarkTests(unittest.TestCase):
    def test_package_order_and_cycles(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = bench.package(root, "base", [], r"\module Base {}")
            left = bench.package(root, "left", ["base"], r"\module Left {}")
            right = bench.package(root, "right", ["base"], r"\module Right {}")
            (root / "ref.toml").write_text('[workspace]\npackages=["right","left","right"]\n')
            self.assertEqual(bench.packages([root]), [base, right, left])
            bench.package(root, "base", ["left"], r"\module Base {}")
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                bench.packages([root])

    def test_repetitions_failures_and_duplicate_names_have_distinct_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = bench.package(root, "first", [], r"\module Main {}")
            second = bench.package(root, "second", [], r"\module Main {}")
            # Two independent inputs may intentionally have the same package name.
            (second / 'ref.toml').write_text((first / 'ref.toml').read_text())
            checker = root / "checker"
            checker.write_text('''#!/usr/bin/env python3
import json, sys
from pathlib import Path
args = sys.argv[1:]
failed = (Path(args[0]) / 'fail').exists()
report = Path(args[args.index('--report-json') + 1])
report.write_text(json.dumps({'version':1,'outcome':'rejected' if failed else 'accepted','cache':{'verification_reused':False}}))
print('rejected' if failed else 'accepted')
raise SystemExit(int(failed))
''')
            checker.chmod(0o755)
            output = root / 'report.json'
            arguments = ['libraries', str(first), str(second), '--binary', str(checker),
                         '--output', str(output), '--runs', '2', '--cache-dir', str(root / 'cache'),
                         '--work-dir', str(root / 'work'), '--memory-mib', '128', '--seconds', '5']
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
            result = bench.measure([sys.executable, '-c', 'import os,time; print(os.getpid(),flush=True); time.sleep(60)'],
                                   log, seconds=.2, memory_mib=128)
            self.assertEqual(result['stopped_by'], 'time_limit')
            self.assertGreater(result['peak_rss_kib'], 0)
            with self.assertRaises(ProcessLookupError):
                os.kill(int(log.read_text()), 0)

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
            profile = bench.cost_profile(log)
            self.assertEqual(profile['scopes']['kernel.check'],
                             dict(calls=5, inclusive_us=50, exclusive_us=30, max_us=20))
            self.assertEqual(profile['exclusive_group_us'], {'kernel': 30})
            self.assertEqual(profile['counts'], {'hits': 5})
            self.assertEqual(len(profile['sessions']), 2)
            analysis = bench.analyze(log, 10)
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
                                   '--output', str(output), '--work-dir', str(root / 'work'),
                                   '--memory-mib', '128'])
            report = json.loads(output.read_text())
            self.assertEqual(code, 1)
            self.assertFalse(report['complete'])
            self.assertFalse(report['measurements'][0]['sources_unchanged'])


if __name__ == '__main__':
    unittest.main()
