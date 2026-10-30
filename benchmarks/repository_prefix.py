"""Compare prefix reuse with isolated, equivalently seeded normal caches."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import bench
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--before', required=True)
parser.add_argument('--after', default='target/release/cli')
parser.add_argument('--work-dir', required=True)
parser.add_argument('--runs', type=int, default=3)
args = parser.parse_args()
root = Path(args.work_dir).resolve()
root.mkdir(parents=True, exist_ok=False)
source = root / 'source'
consumer = source / 'consumer'
(consumer / 'src').mkdir(parents=True, exist_ok=True)
std = Path('libs/std').resolve()
(source / 'ref.toml').write_text('[workspace]\npackages=[' + json.dumps(os.path.relpath(std, source)) + ',"consumer"]\n')
(consumer / 'ref.toml').write_text('[package]\nname="consumer"\n[dependencies]\nstd={path=' + json.dumps(os.path.relpath(std, consumer)) + '}\n')
(consumer / 'src/root.ref').write_text(r'\module Proof { \import std.Logic[].Proposition[] \as L; \definition left[P, Q: \Prop][h: L.And[P,Q]]: P := h.left; }' + '\n')
report = {'source_sha256': bench.source_digest(source), 'std_source_sha256': bench.source_digest(std),
          'cache_condition': 'normal std seed, independent copies per run',
          'memory_mib': 3072, 'measurements': []}

def run(label, binary, entry, cache, module):
    result = root / (label + '.checker.json')
    command = [str(binary), str(entry), '--module', module, '--memory-mib', '3072', '--cache-dir', str(cache), '--report-json', str(result), '--no-progress']
    row = bench.measure(command, root / (label + '.log'), seconds=900, memory_mib=3072, environment=dict(os.environ), progress_seconds=30)
    row.update(label=label, binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), checker=json.loads(result.read_text()) if result.exists() else None)
    report['measurements'].append(row)
    (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(label, row['exit'], row['seconds'], row['peak_rss_kib'], flush=True)
    if row['exit'] != 0:
        raise SystemExit('benchmark failed; see ' + str(root / (label + '.log')))

for version, binary in [('before', Path(args.before).resolve()), ('after', Path(args.after).resolve())]:
    seed = root / (version + '-seed-cache')
    if seed.exists():
        raise SystemExit('benchmark already exists; use a fresh benchmark directory')
    run(version + '-seed', binary, source, seed, 'std')
    for index in range(args.runs):
        cache = root / (version + '-' + str(index) + '-cache')
        shutil.copytree(seed, cache)
        run(version + '-' + str(index), binary, consumer, cache, 'consumer.Proof')

if bench.source_digest(source) != report['source_sha256'] or bench.source_digest(std) != report['std_source_sha256']:
    raise SystemExit('source changed during comparison')
