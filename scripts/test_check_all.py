"""Small end-to-end checks for the repository driver (Linux, built CLI required)."""
import json
import os
from pathlib import Path
import subprocess
import signal
import time
import sys
import tempfile
import unittest

BINARY = Path(os.environ.get('REF_TYPE_TEST_BINARY', 'target/release/cli')).resolve()
DRIVER = Path(__file__).with_name('check_all.py').resolve()


class RepositoryCheckTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='repository-check-')
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'ref.toml').write_text('[workspace]\npackages=["base","client"]\n')
        for name in ['base', 'client']:
            package = self.root / name
            (package / 'src').mkdir(parents=True)
            deps = '[dependencies]\nbase={path="../base"}\n' if name == 'client' else ''
            (package / 'ref.toml').write_text(f'[package]\nname="{name}"\n' + deps)
        (self.root / 'base/src/root.ref').write_text(r'\module Logic { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }')
        (self.root / 'client/src/root.ref').write_text(r'\module Main { \import base.Logic[] \as B; \definition P: \Prop := B.P; }')
        self.state = self.root / 'state'

    def run_check(self, *extra):
        result = subprocess.run([sys.executable, str(DRIVER), str(self.root), '--binary', str(BINARY),
                                 '--state-dir', str(self.state), *extra], capture_output=True, text=True, timeout=60)
        latest = json.loads((self.state / 'latest.json').read_text())
        report = json.loads(Path(latest['report']).read_text())
        return result, report

    def accepted(self, result, report):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(report['outcome'], 'accepted')
        self.assertEqual(set(report['targets']), set(report['verified']))
        self.assertEqual(report['save_failures'], 0)

    def test_cold_warm_and_dependency_change(self):
        result, cold = self.run_check()
        self.accepted(result, cold)
        self.assertTrue(cold['newly_checked'])
        result, warm = self.run_check()
        self.accepted(result, warm)
        self.assertFalse(warm['newly_checked'])
        self.assertEqual(set(warm['targets']), set(warm['reused']))
        (self.root / 'base/src/root.ref').write_text(r'\module Logic { \definition P: \Prop := \forall (P: \Prop) -> P; \definition bad: P := \fun (P: \Prop) => P; }')
        result, changed = self.run_check()
        self.assertNotEqual(result.returncode, 0)
        self.assertNotEqual(changed['source_sha256'], cold['source_sha256'])
        self.assertEqual(changed['attempts'][-1]['outcome'], 'rejected')

    def test_corrupt_cache_is_rechecked(self):
        result, first = self.run_check()
        self.accepted(result, first)
        objects = list((self.root / 'refcache/objects').rglob('*'))
        files = [p for p in objects if p.is_file()]
        self.assertTrue(files)
        for path in files:
            path.write_bytes(b'corrupt')
        result, repaired = self.run_check()
        self.accepted(result, repaired)
        self.assertTrue(repaired['newly_checked'])

    def test_storage_failure_is_nonzero_and_distinct(self):
        cache = self.root / 'refcache'
        cache.mkdir()
        (cache / 'checkpoints').write_text('not a directory')
        result, report = self.run_check()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(report['attempts'][-1]['outcome'], 'storage-failure')
        self.assertGreater(report['save_failures'], 0)
        (cache / 'checkpoints').unlink()
        result, repaired = self.run_check()
        self.accepted(result, repaired)

    def test_disk_reserve_stops_without_claiming_success(self):
        result, report = self.run_check('--min-free-mib', '1000000000')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('disk free space', report['error'])

    def start_check(self):
        child = subprocess.Popen([sys.executable, str(DRIVER), str(self.root), '--binary', str(BINARY),
                                  '--state-dir', str(self.state)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(lambda: child.poll() is None and child.kill())
        return child

    def wait_for(self, child, condition):
        deadline = time.monotonic() + 20
        while time.monotonic() < deadline:
            if condition():
                return
            if child.poll() is not None:
                self.fail(str(child.communicate()))
            time.sleep(.01)
        self.fail('check did not reach expected boundary')

    def test_source_change_is_not_mixed_with_snapshot_results(self):
        child = self.start_check()
        self.wait_for(child, lambda: bool(list(self.state.glob('*/source.json'))))
        source = self.root / 'base/src/root.ref'
        source.write_text(source.read_text() + r'\module Added {}')
        stdout, stderr = child.communicate(timeout=60)
        self.assertNotEqual(child.returncode, 0, stdout + stderr)
        report = json.loads(Path(json.loads((self.state / 'latest.json').read_text())['report']).read_text())
        self.assertIn('source or target list changed', report['error'])

    def test_external_kill_resumes_with_the_same_command(self):
        child = self.start_check()
        def made_progress():
            try:
                latest = json.loads((self.state / 'latest.json').read_text())
                report = json.loads(Path(latest['report']).read_text())
                return bool(report['verified']) and report['outcome'] == 'running'
            except (OSError, ValueError):
                return False
        self.wait_for(child, made_progress)
        child.send_signal(signal.SIGKILL)
        child.communicate(timeout=10)
        result, resumed = self.run_check()
        self.accepted(result, resumed)
        self.assertTrue(resumed['reused'])

    def test_impossible_memory_budget_terminates(self):
        result, report = self.run_check('--memory-mib', '32')
        self.assertNotEqual(result.returncode, 0)
        self.assertNotEqual(report['outcome'], 'accepted')
        self.assertLess(len(report['attempts']), 10)


if __name__ == '__main__':
    unittest.main()
