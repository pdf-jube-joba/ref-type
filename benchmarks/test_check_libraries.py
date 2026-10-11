"""Exercise native checker reporting without a large library."""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_libraries


class BoundedCheckingTests(unittest.TestCase):
    def test_reports_native_completion_failures_and_distinct_package_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project = root / 'libs/example'
            project.mkdir(parents=True)
            (project / 'ref.toml').write_text('[package]\nname = "example"\n')
            binary = root / 'checker'
            binary.write_text('''#!/usr/bin/env python3
import sys
from pathlib import Path
args = sys.argv[1:]
if '--list-modules' in args:
    print('example\\nexample.A\\nexample.B')
    raise SystemExit(0)
if (Path(args[0]) / 'fail-parent').exists():
    print('parent declaration is ill typed')
    raise SystemExit(1)
''')
            binary.chmod(0o755)
            report_path = root / 'report.json'
            argv = ['check_libraries.py', str(project), '--binary', str(binary),
                    '--output', str(report_path), '--cache-dir', str(root / 'cache'),
                    '--memory-mib', '128', '--seconds', '5']
            with patch.object(check_libraries, 'ROOT', root), patch.object(sys, 'argv', argv), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(check_libraries.main(), 0)
                report = json.loads(report_path.read_text())
                package = report['packages'][0]
                self.assertTrue(report['complete'])
                self.assertEqual(package['verified'], ['example', 'example.A', 'example.B'])
                self.assertEqual(len(package['batches']), 1)
                report_path.unlink()
                (project / 'fail-parent').touch()
                self.assertEqual(check_libraries.main(), 1)
                report = json.loads(report_path.read_text())
                package = report['packages'][0]
                self.assertFalse(report['complete'])
                self.assertEqual(package['verified'], [])
                self.assertEqual(package['failed'][0]['module'], 'example')
                self.assertFalse(any(b['resource_limit'] for b in package['batches']))
                # Different test projects may deliberately use the same package name.
                variant = root / 'libs/variant'
                variant.mkdir()
                (variant / 'ref.toml').write_text('[package]\nname = "example"\n')
                argv.insert(2, str(variant))
                self.assertEqual(check_libraries.main(), 1)
                report = json.loads(report_path.read_text())
                first, second = report['packages']
                self.assertFalse(first['complete'])
                self.assertTrue(second['complete'])
                failed_log = root / first['failed'][0]['log']
                self.assertIn('parent declaration is ill typed', failed_log.read_text())
                self.assertNotIn(first['failed'][0]['log'], [b['log'] for b in second['batches']])


if __name__ == '__main__':
    unittest.main()
