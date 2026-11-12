#!/usr/bin/env python3
"""Preserve actual driver reports and reconcile immutable source identities."""
import argparse
import collections
import gzip
import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel'], text=True).strip())


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def tree(commit):
    result = {}
    rows = subprocess.check_output(['git', 'ls-tree', '-rz', commit], cwd=ROOT)
    for row in rows.split(b'\0'):
        if row:
            info, name = row.split(b'\t', 1)
            result[name.decode()] = info.split()[2].decode()
    return result


def packed(path, value):
    raw = json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode()
    path.write_bytes(gzip.compress(raw, mtime=0))


def collect(state, output, partial):
    index = json.loads((state / 'latest.json').read_bytes())
    report = pathlib.Path(index['report'])
    raw = report.read_bytes()
    data = json.loads(raw)
    if not partial:
        assert data['outcome'] == 'accepted', data['outcome']
        assert set(data['verified']) == set(data['targets'])
        assert data['save_failures'] == data['corrupt_cache_reads'] == 0
    assert digest(pathlib.Path(data['binary']).read_bytes()) == data['binary_sha256']
    snapshot = report.parent / 'source.json'
    assert digest(snapshot.read_bytes()) == data['source_sha256']
    source = json.loads(snapshot.read_bytes())
    checked_tree, current_tree = tree(data['commit']), tree('HEAD')
    inventory = {}
    for name, text in source['files'].items():
        path, content = pathlib.Path(name), text.encode()
        relative = str(path.relative_to(ROOT))
        assert path.read_bytes() == content, ('checkout mismatch', relative)
        blob = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        assert checked_tree.get(relative) == blob, ('checked commit mismatch', relative)
        assert current_tree.get(relative) == blob, ('current head mismatch', relative)
        inventory[relative] = {'sha256': digest(content), 'git_blob': blob}
    output.mkdir(parents=True, exist_ok=True)
    (output / 'driver.json.gz').write_bytes(gzip.compress(raw, mtime=0))
    packed(output / 'source-files.json.gz', inventory)
    packed(output / 'aliases.json.gz', source.get('aliases', {}))
    workers = []
    for attempt in data['attempts']:
        path = pathlib.Path(attempt['report'])
        if path.exists():
            body = path.read_bytes()
            workers.append({'file': path.name, 'sha256': digest(body), 'raw_utf8': body.decode()})
        else:
            assert partial, ('missing accepted report', str(path))
            workers.append({'file': path.name, 'missing': True})
    packed(output / 'workers.raw.json.gz', workers)
    summary = {key: value for key, value in data.items()
               if key not in ('attempts', 'targets', 'verified', 'newly_checked', 'reused', 'package_entries')}
    summary.update(counts={key: len(data[key]) for key in ('targets', 'verified', 'newly_checked', 'reused')},
                   source_files=len(inventory), source_snapshot_sha256=digest(snapshot.read_bytes()),
                   checked_commit=data['commit'], current_head=subprocess.check_output(
                       ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                   checkout_and_both_git_trees_match=True, partial_checkpoint=partial,
                   attempts=len(data['attempts']), attempt_outcomes=dict(collections.Counter(
                       item['outcome'] for item in data['attempts'])), original_report_sha256=digest(raw))
    (summary_path := output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(summary_path, summary['outcome'], summary['counts'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--state', type=pathlib.Path, required=True)
    parser.add_argument('--out', type=pathlib.Path, required=True)
    parser.add_argument('--partial', action='store_true')
    args = parser.parse_args()
    collect(args.state, args.out, args.partial)
