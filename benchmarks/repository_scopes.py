"""Compare normal std checking via the workspace and a bounded package scope."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import bench

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--before', required=True)
parser.add_argument('--after', default='target/release/cli')
parser.add_argument('--work-dir', required=True)
parser.add_argument('--runs', type=int, default=3)
args = parser.parse_args()
root = Path(args.work_dir).resolve()
root.mkdir(parents=True, exist_ok=False)
source = Path('libs').resolve()
source_hash = bench.source_digest(source)
report = {'source_sha256': source_hash, 'selection': 'std', 'cache_condition': 'empty per run',
          'memory_mib': 3072, 'measurements': []}
for version, binary, entry in [('before', Path(args.before).resolve(), source),
                               ('after', Path(args.after).resolve(), source / 'std')]:
    for index in range(args.runs):
        label = f'{version}-{index}'
        result = root / (label + '.checker.json')
        command = [str(binary), str(entry), '--module', 'std', '--memory-mib', '3072',
                   '--cache-dir', str(root / (label + '-cache')), '--report-json', str(result), '--no-progress']
        row = bench.measure(command, root / (label + '.log'), seconds=900, memory_mib=3072,
                            environment=dict(os.environ), progress_seconds=30)
        checker = json.loads(result.read_text()) if result.exists() else None
        row.update(label=label, binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), checker=checker)
        report['measurements'].append(row)
        (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(label, row['exit'], row['seconds'], row['peak_rss_kib'], flush=True)
        if row['exit'] != 0 or checker['outcome'] != 'accepted':
            raise SystemExit('benchmark failed: ' + str(root / (label + '.log')))
if bench.source_digest(source) != source_hash:
    raise SystemExit('source changed during comparison')
