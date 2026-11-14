#!/usr/bin/env python3
"""Check, reload and reject generated declarations while paging the whole heap."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

from large_scale import independent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=Path('target/release/cli'))
    parser.add_argument('--memory-mib', type=int, default=32)
    parser.add_argument('--groups', type=int, default=64)
    parser.add_argument('--width', type=int, default=64)
    parser.add_argument('--output', type=Path, default=Path('benchmarks/runs/heap-spill.json'))
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with binary.open('rb') as stream:
        binary_sha256 = hashlib.file_digest(stream, 'sha256').hexdigest()
    result = dict(binary_sha256=binary_sha256,
                  memory_mib=args.memory_mib, groups=args.groups, width=args.width, runs=[])
    work = Path('benchmarks/runs')
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='heap-spill-', dir=work) as temporary:
        root = Path(temporary).resolve()
        entry = independent(root, args.groups, args.width)

        def run(label, path, *extra, outcome='accepted'):
            report_path = root / (label + '.json')
            command = [str(binary), str(path), '--memory-mib', str(args.memory_mib),
                       '--report-json', str(report_path), '--no-progress', *extra]
            started = time.monotonic()
            completed = subprocess.run(command, capture_output=True, text=True, timeout=180)
            report = json.loads(report_path.read_text())
            row = dict(label=label, command=command, elapsed_seconds=time.monotonic() - started,
                       exit_code=completed.returncode, report=report)
            result['runs'].append(row)
            args.output.write_text(json.dumps(result, indent=2) + '\n')
            assert report['outcome'] == outcome, completed.stderr
            assert completed.returncode == (0 if outcome == 'accepted' else 1), completed.stderr
            assert report['storage']['save_failures'] == 0, completed.stderr
            print(f"{label}: {report['outcome']}, {row['elapsed_seconds']:.3f}s, "
                  f"RSS {report['execution']['peak_rss_kib']} KiB, "
                  f"pageout requests {report['execution']['heap_pageout_requested_bytes']} bytes", flush=True)
            return report

        # Late alias conversions exercise old pages after thousands of fresh
        # declarations. Cache restoration then checks the same graph again.
        cold = run('cold', entry)
        assert cold['execution']['heap_pageout_requested_bytes'] > 0
        assert cold['execution']['recoveries'] == 0
        run('warm', entry)
        run('restore', entry, '--full-check-local')
        run('file', entry / 'src/root.ref', '--no-cache')
        # Nominally different types must still be rejected after paging/reload.
        source = entry / 'src/root.ref'
        source.write_text(source.read_text() + r'''
\module Invalid {
  \import \root.G0[] \as A;
  \import \root.G1[] \as B;
  \definition bad: A.T0 := B.value0;
}
''')
        run('rejected', entry, outcome='rejected')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
