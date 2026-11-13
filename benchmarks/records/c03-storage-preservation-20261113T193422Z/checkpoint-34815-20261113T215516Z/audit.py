#!/usr/bin/env python3
"""Read checkpoint references and preserve small recovery records only."""
import collections
import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path('/workspace/ref-type')
OUT = Path(__file__).resolve().parent
OLD_COMMIT = 'f04f960d9557454859cbf7d5c216152da54531a6'
OLD_BASE = 'benchmarks/records/c03-storage-preservation-20261113T193422Z'
RUN = 'work/c03/final-integrated/20261113T195317.054152Z'
CP = 'libs/refcache/checkpoints/66/66bc954efa8701e732db5792bf701a8af020ee5568e6f397659d8e80a95a26e1.checkpoint'

def digest_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def write_json(name, value):
    with (OUT / name).open('x') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')

class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0
    def raw(self, n):
        result = self.data[self.pos:self.pos+n]
        assert len(result) == n
        self.pos += n
        return result
    def uint(self):
        result = shift = 0
        while True:
            byte = self.raw(1)[0]
            result |= (byte & 127) << shift
            if byte < 128:
                return result
            shift += 7
            assert shift < 70
    def string(self):
        return self.raw(self.uint()).decode('utf-8')
    def vector(self, fn):
        return [fn() for _ in range(self.uint())]
    def module(self):
        return self.vector(self.string)
    def object(self):
        return dict(digest=self.raw(32).hex(), kind=self.uint(),
                    stored_bytes=self.uint(), decoded_bytes=self.uint())
    def optional_object(self):
        tag = self.uint()
        assert tag in (0, 1)
        return self.object() if tag else None

def manifest(data):
    assert data[:8] == b'REFMAN02'
    assert hashlib.sha256(data[40:]).digest() == data[8:40]
    r = Reader(data[40:])
    key, source = r.raw(32).hex(), r.raw(32).hex()
    coverage = r.vector(r.module)
    deps = r.vector(lambda: r.raw(32).hex())
    results = r.vector(lambda: (r.module(), r.object()))
    optionals = [r.optional_object() for _ in range(3)]
    graph = r.vector(r.object)
    assert r.pos == len(r.data)
    refs = [o for _, o in results] + [o for o in optionals if o] + graph
    unique = {}
    for obj in refs:
        if obj['digest'] in unique:
            assert unique[obj['digest']] == obj
        unique[obj['digest']] = obj
    return dict(key=key, input=source, coverage_count=len(coverage),
                dependencies=deps, graph_reference_count=len(graph), objects=unique)

def main():
    start = time.monotonic()
    cp_bytes = (ROOT / CP).read_bytes()
    m = manifest(cp_bytes)
    assert m['key'] == Path(CP).stem
    assert not m['dependencies'], 'Unexpected dependencies require an expanded audit'
    refs = m.pop('objects')
    errors = []
    totals = collections.Counter()
    inventory = OUT / 'checkpoint-object-inventory.jsonl.gz'
    with inventory.open('xb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as z:
        for index, (dg, obj) in enumerate(sorted(refs.items()), 1):
            rel = f'libs/refcache/objects/{dg[:2]}/{dg}'
            path = ROOT / rel
            entry = dict(path=rel, **obj)
            try:
                st = path.stat()
                h = hashlib.sha256()
                with path.open('rb') as f:
                    header = f.read(60)
                    h.update(header)
                    for chunk in iter(lambda: f.read(1024 * 1024), b''):
                        h.update(chunk)
                assert len(header) == 60 and header[:8] == b'REFOBJ02'
                assert header[8] == obj['kind'] + 1
                assert int.from_bytes(header[12:20], 'little') + 60 == obj['stored_bytes']
                assert int.from_bytes(header[20:28], 'little') == obj['decoded_bytes']
                assert st.st_size == obj['stored_bytes']
                assert h.hexdigest() == dg
                entry.update(status='present-size-header-sha256-match', allocated_bytes=st.st_blocks*512)
                totals['objects'] += 1
                totals['stored_bytes'] += st.st_size
                totals['allocated_bytes'] += st.st_blocks*512
                totals['decoded_bytes_declared'] += obj['decoded_bytes']
            except (OSError, AssertionError) as e:
                entry.update(status='error', error=type(e).__name__ + ': ' + str(e))
                errors.append(entry)
            z.write((json.dumps(entry, sort_keys=True) + '\n').encode())
            if index % 5000 == 0:
                print(json.dumps(dict(read_objects=index, total=len(refs), elapsed_seconds=round(time.monotonic()-start,1))), flush=True)
    assert (ROOT / CP).read_bytes() == cp_bytes, 'Checkpoint changed during read-only audit'
    report = json.loads((ROOT / RUN / 'report.json').read_text())
    interrupted = json.loads((ROOT / RUN / '00001-compact_support_k.json').read_text())
    assert interrupted['execution']['last_checkpoint'] == 34815
    old_manifest = json.loads(subprocess.check_output(['git','show', OLD_COMMIT+':'+OLD_BASE+'/manifest.json']))
    archived_sources = [x for x in old_manifest if x['path'].endswith('/source.json') and x['sha256'] == report['source_sha256']]
    assert archived_sources
    source = ROOT / RUN / 'source.json'
    checker = ROOT / 'target/release/cli'
    driver = ROOT / 'scripts/check_all.py'
    actual = dict(source_sha256=digest_file(source), checker_sha256=digest_file(checker), driver_sha256=digest_file(driver))
    assert actual == dict(source_sha256=report['source_sha256'],checker_sha256=report['binary_sha256'],driver_sha256=report['driver_sha256'])
    original_paths = {}
    for original, saved in [(CP,'checkpoint-34815.manifest'),
                            (RUN+'/report.json','aggregate-report.json'),
                            (RUN+'/00001-compact_support_k.json','interrupted-scope.json'),
                            (RUN+'/00001-compact_support_k.log','interrupted-scope.log'),
                            ('work/c03-preservation-20261113T193422Z/resumed-validation.log','run.log')]:
        destination = OUT / saved
        with (ROOT/original).open('rb') as src, destination.open('xb') as dst:
            shutil.copyfileobj(src,dst)
        original_paths[saved] = original
    verified = set(report['verified'])
    targets = set(report['targets'])
    remaining = sorted(targets - verified)
    write_json('targets.json',report['targets'])
    write_json('accepted-targets.json',sorted(verified))
    write_json('remaining-targets.json',remaining)
    write_json('fingerprints.json',dict(**actual,implementation_commit=report['commit'],
                                     source_bytes=source.stat().st_size,
                                     checker_bytes=checker.stat().st_size,
                                     source_snapshot_in_existing_archive=archived_sources,
                                     checkpoint_manifest_sha256=hashlib.sha256(cp_bytes).hexdigest()))
    audit = dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 checkpoint=34815, manifest=CP, manifest_sha256=hashlib.sha256(cp_bytes).hexdigest(),
                 manifest_structure=m, direct_reference_count=len(refs),
                 dependency_manifest_count=0, reference_totals=dict(totals),
                 reference_error_count=len(errors), errors=errors,
                 verification='read-only stat, object header, complete stored-file SHA256 matching manifest digest; no checker or cache mutation',
                 not_executed=['payload deserialization', 'checkpoint restore', 'mathematical checks'],
                 reference_inventory='checkpoint-object-inventory.jsonl.gz',
                 elapsed_seconds=round(time.monotonic()-start,3))
    write_json('checkpoint-reference-audit.json',audit)
    resume = dict(implementation_commit=report['commit'], evidence_parent=OLD_COMMIT,
                  old_archive_git_path=OLD_BASE+'/records.tar.gz',
                  old_archive_sha256='42b1dffa1cec0bc622397e25e7642a2be62bf266313c29b4d6c4f08e1c11d4c0',
                  checkpoint=34815, accepted_count=len(verified), target_count=len(targets),
                  c03_accepted_count=sum(x=='cohomology_thom' or x.startswith('cohomology_thom.') for x in verified),
                  remaining_count=len(remaining),
                  remaining_packages=dict(collections.Counter(x.split('.')[0] for x in remaining)),
                  original_paths=original_paths,
                  restore_source_snapshot_to=RUN+'/source.json',
                  source_snapshot_reuse='Use an archived source.json with the exact source SHA256; latest source snapshot bytes are unchanged.',
                  original_workspace=str(ROOT),
                  process_state='checker stopped by disk reserve protection; do not infer a mathematical rejection',
                  missing_for_full_restore=['checkpoint referenced cache objects listed in inventory', 'exact checked binary'],
                  cache_objects_uploaded=False, checker_uploaded=False,
                  checker_omission=dict(bytes=checker.stat().st_size,git_file_limit_bytes=100*1024**2,
                                        reason='278 MiB binary exceeds normal Git 100 MiB file limit; no large upload authorized'),
                  normal_command=['env','REF_TYPE_GRAPH_RESIDENT_MIB=512','python3','scripts/check_all.py','libs',
                                  '--binary','target/release/cli','--state-dir','work/c03/final-integrated',
                                  '--memory-mib','16384','--initial-memory-mib','16384',
                                  '--cache-budget-mib','26880','--min-free-mib','512',
                                  '--max-scope-targets','1','--split-package','cohomology_thom',
                                  '--resume-report',RUN+'/report.json'],
                  resume_prerequisites=['adequate additional disk capacity, with 512 MiB reserve unchanged',
                                        'no active checker', 'restore actual objects before claiming checkpoint continuity',
                                        'exact binary/source/target identity and accepted scope records available'],
                  execution_performed=False)
    write_json('resume-info.json',resume)
    readme = '''# C03 checkpoint 34815 recovery records

This additive directory preserves the latest checkpoint manifest and disk-stop records.
The earlier 418-file archive remains unchanged in the parent evidence commit.
It supplies accepted scope reports and the byte-identical fixed source snapshot.
Original path mappings, SHA256 identities, targets and the normal resume command are recorded here.
No checker was started to produce these records.

The manifest and the reference inventory are not a complete runnable checkpoint backup.
Referenced object payloads and the exact verified checker binary remain only in the original workspace.
The inventory audits stored bytes, headers and SHA256 values without restoring or deserializing the checkpoint.
No mathematical verification or environment-loss restore was performed.

For recovery, restore the earlier archive into a new empty directory, verify its manifest,
and place the new records at the original paths from resume-info.json only in an empty recovery workspace.
Place a source.json from the earlier archive, verified by fingerprints.json, beside the restored latest report.
All accepted scope report paths referenced by that report are present in the earlier archive.
Restore the exact referenced cache objects and exact checked binary before asserting checkpoint continuity.
Without the objects, compact_support_k must rebuild its checkpoint work.
Without an exact binary/source/target match, the normal driver rejects accepted-prefix resumption.

The command in resume-info.json is informational; capacity and identity prerequisites must be met first.
This commit does not complete the pending aggregate verification or change PR #76.
'''
    with (OUT/'README.md').open('x') as f:
        f.write(readme)
    records = []
    for path in sorted(OUT.iterdir()):
        if path.is_file() and path.name != 'manifest.json':
            records.append(dict(name=path.name,bytes=path.stat().st_size,sha256=digest_file(path)))
    write_json('manifest.json',records)
    print(json.dumps(dict(output=str(OUT),files=len(records)+1,bytes=sum(x['bytes'] for x in records),
                          audit=audit,free_bytes=os.statvfs(ROOT).f_bavail*os.statvfs(ROOT).f_frsize),ensure_ascii=False),flush=True)
    if errors:
        raise SystemExit('Reference incompleteness recorded; do not claim a complete checkpoint')

if __name__ == '__main__':
    main()
