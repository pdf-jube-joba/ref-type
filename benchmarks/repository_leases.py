#!/usr/bin/env python3
"""Build the lease decoder benchmark against an existing release build, then run it."""
import argparse
import itertools
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir', required=True, type=Path)
parser.add_argument('--fingerprints', type=int, default=8000)
args = parser.parse_args()
args.work_dir.mkdir(parents=True, exist_ok=False)
binary = args.work_dir / 'lease-benchmark'
deps = Path('target/release/deps')
command = ['rustc', '--edition=2024', '-O', str(Path(__file__).with_suffix('.rs')),
           '-L', f'dependency={deps}', '-o', str(binary)]
names = ['serde', 'serde_json', 'postcard']
# A workspace can retain several feature combinations. Let rustc choose a
# compatible set rather than accidentally mixing distinct serde_core instances.
libraries = [sorted(deps.glob(f'lib{name}-*.rlib'), key=lambda p: p.stat().st_mtime, reverse=True) for name in names]
if not all(libraries):
    parser.error('build the release CLI with this toolchain first')
for selected in itertools.product(*libraries):
    linking = list(command)
    for name, library in zip(names, selected):
        linking += ['--extern', f'{name}={library}']
    build = subprocess.run(linking, capture_output=True, text=True)
    if build.returncode == 0:
        break
else:
    raise RuntimeError(build.stderr)
with (args.work_dir / 'measurements.jsonl').open('w') as output:
    subprocess.run([str(binary), str(args.work_dir / 'data'), str(args.fingerprints)], stdout=output, check=True)
