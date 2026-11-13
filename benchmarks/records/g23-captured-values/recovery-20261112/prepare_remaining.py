#!/usr/bin/env python3
"""Warm only uncovered fixed-source targets before the standard full driver."""
import argparse
import ctypes
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
RECORD = Path(__file__).resolve().parent


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def verify_checkout(source, commit, build):
    trees = []
    for ref in [commit, 'HEAD']:
        rows = subprocess.check_output(['git', 'ls-tree', '-rz', ref], cwd=ROOT)
        trees.append({row.split(b'\t', 1)[1].decode(): row.split(b'\t', 1)[0].split()[2].decode()
                      for row in rows.split(b'\0') if row})
    for name, text in source['files'].items():
        path = Path(name)
        relative = str(path.relative_to(ROOT))
        raw = text.encode()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert path.read_bytes() == raw
        assert all(tree.get(relative) == blob for tree in trees), relative
    for name, expected in build['files'].items():
        assert digest(ROOT / name) == expected, name
    changes = subprocess.check_output(
        ['git', 'diff', '--name-only', build['commit'] + '..HEAD'], cwd=ROOT, text=True).splitlines()
    assert all(name.startswith('benchmarks/records/g23-captured-values/recovery-20261112/')
               for name in changes), changes


def seed(args):
    import gzip
    build = json.loads(gzip.decompress((RECORD / 'checker-source-sha256.json.gz').read_bytes()))
    assert digest(args.binary) == build['binary_sha256']
    index = json.loads((args.base / 'full/latest.json').read_text())
    path = Path(index['report'])
    driver = json.loads(path.read_text())
    snapshot = path.parent / 'source.json'
    source = json.loads(snapshot.read_text())
    assert driver['binary_sha256'] == build['binary_sha256']
    assert digest(snapshot) == driver['source_sha256']
    assert driver['save_failures'] == driver['corrupt_cache_reads'] == 0
    targets = set(driver['targets'])
    assert len(targets) == len(driver['targets'])
    verified, checked, evidence = set(), set(), []
    for attempt in driver['attempts']:
        if attempt['exit_code'] != 0 or attempt['outcome'] != 'accepted':
            continue
        report = Path(attempt['report'])
        result = json.loads(report.read_text())
        assert result['outcome'] == 'accepted'
        assert result['storage']['save_failures'] == result['storage']['corrupt'] == 0
        coverage = {'.'.join(parts) for parts in result['verified_modules']}
        module = attempt['module']
        wanted = targets if module is None else {
            name for name in targets if name == module or
            (not attempt['module_only'] and name.startswith(module + '.'))}
        assert wanted <= coverage, module
        verified.update(coverage & targets)
        checked.update('.'.join(parts) for parts in result['checked_modules'])
        evidence.append({'report': str(report), 'sha256': digest(report)})
    assert verified == set(driver['verified'])
    checked.update(driver['newly_checked'])
    critical = args.base / 'critical'
    scoped = json.loads((critical / 'source.json').read_text())
    scoped['entry'] = source['entry']
    assert scoped == source
    result = json.loads((critical / 'report.json').read_text())
    assert json.loads((critical / 'execution.json').read_text())['exit_code'] == 0
    assert result['outcome'] == 'accepted'
    assert result['storage']['save_failures'] == result['storage']['corrupt'] == 0
    summary = json.loads((RECORD / 'critical/summary.json').read_text())
    assert digest(critical / 'report.json') == summary['original_report_sha256']
    assert digest(critical / 'source.json') == summary['source_snapshot_sha256']
    assert summary['checker_sha256'] == build['binary_sha256']
    coverage = {'.'.join(parts) for parts in result['verified_modules']}
    assert 'k_theory_thom.Thom.Complexification.Compact.Isomorphism' in coverage
    verified.update(coverage & targets)
    checked.update('.'.join(parts) for parts in result['checked_modules'])
    evidence.append({'report': str(critical / 'report.json'), 'sha256': digest(critical / 'report.json')})
    # A scope changes only the entry; the complete immutable files and aliases agree.
    current = Path(json.loads((args.base / 'full-16g/latest.json').read_text())['report'])
    current_driver = json.loads(current.read_text())
    assert json.loads((current.parent / 'source.json').read_text()) == source
    assert current_driver['binary_sha256'] == build['binary_sha256']
    assert set(current_driver['targets']) == targets
    verify_checkout(source, driver['commit'], build)
    return source, targets, verified, checked, evidence, build, driver


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--cache-dir', type=Path, required=True)
    parser.add_argument('--state-dir', type=Path, required=True)
    parser.add_argument('--plan-only', action='store_true')
    parser.add_argument('--memory-mib', type=int, default=17408)
    parser.add_argument('--cache-budget-mib', type=int, default=20480)
    args = parser.parse_args()
    source, targets, verified, checked, evidence, build, driver = seed(args)
    args.state_dir.mkdir(parents=True, exist_ok=True)
    own_lock = (args.state_dir / 'lock').open('a')
    fcntl.flock(own_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    report = dict(outcome='prepared', commit=subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], text=True).strip(), binary=str(args.binary),
        binary_sha256=build['binary_sha256'], source_sha256=driver['source_sha256'],
        source_commit=driver['commit'], seeded_verified=sorted(verified),
        targets=sorted(targets), remaining=sorted(targets - verified), seed_reports=evidence,
        memory_mib=args.memory_mib, cache_budget_mib=args.cache_budget_mib, attempts=[])
    report_file = args.state_dir / 'report.json'
    save(args.state_dir / 'plan.json', report)
    print(f'fixed-source seed: {len(verified)}/{len(targets)}; remaining {len(targets - verified)}', flush=True)
    if args.plan_only:
        return 0
    active_lock = (args.base / 'full-16g/lock').open('a')
    fcntl.flock(active_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    child, interrupted = None, False
    parent_pid = os.getpid()
    libc = ctypes.CDLL(None, use_errno=True)

    def child_setup():
        if libc.prctl(1, signal.SIGTERM, 0, 0, 0) != 0 or os.getppid() != parent_pid:
            os._exit(130)

    def cancel(_signum, _frame):
        nonlocal interrupted
        interrupted = True
        if child is not None and child.poll() is None:
            child.send_signal(signal.SIGTERM)

    for signum in [signal.SIGINT, signal.SIGTERM, signal.SIGHUP]:
        signal.signal(signum, cancel)
    report['outcome'] = 'running'
    started = time.monotonic()
    try:
        for module in sorted(targets - verified):
            if module in verified:
                continue
            if interrupted:
                raise RuntimeError('interrupted')
            assert digest(args.binary) == build['binary_sha256']
            entry = driver['package_entries'][module.split('.')[0]]
            snapshot = args.state_dir / 'scope-source.json'
            save(snapshot, dict(source, entry=entry))
            snapshot_digest = digest(snapshot)
            label = f'{len(report["attempts"]) + 1:03d}-{module}'
            result_file = args.state_dir / (label + '.json')
            command = [str(args.binary), entry, '--source-snapshot', str(snapshot),
                       '--module', module, '--module-only', '--memory-mib', str(args.memory_mib),
                       '--checkpoint-seconds', '120', '--cache-dir', str(args.cache_dir),
                       '--cache-budget-mib', str(args.cache_budget_mib), '--report-json', str(result_file),
                       '--no-progress', '--diagnostics', 'compact']
            attempt = dict(module=module, command=command, source_sha256=snapshot_digest,
                           report=str(result_file), outcome='running')
            report['attempts'].append(attempt)
            save(report_file, report)
            print(f'checking {module}: {len(verified)}/{len(targets)}', flush=True)
            environment = dict(os.environ, REF_TYPE_GRAPH_SPILL_DIR='/tmp')
            with (args.state_dir / (label + '.stdout')).open('wb') as out, \
                    (args.state_dir / (label + '.log')).open('wb') as err:
                child = subprocess.Popen(command, stdout=out, stderr=err, env=environment,
                                         preexec_fn=child_setup)
                code = child.wait()
                child = None
            assert digest(args.binary) == build['binary_sha256'] and digest(snapshot) == snapshot_digest
            attempt['exit_code'] = code
            result = json.loads(result_file.read_text()) if result_file.exists() else {}
            attempt['outcome'] = result.get('outcome', 'missing-report')
            if interrupted:
                raise RuntimeError('interrupted')
            assert code == 0 and result.get('outcome') == 'accepted', attempt
            assert result['storage']['save_failures'] == result['storage']['corrupt'] == 0
            coverage = {'.'.join(parts) for parts in result['verified_modules']}
            assert module in coverage, module
            verified.update(coverage & targets)
            checked.update('.'.join(parts) for parts in result['checked_modules'])
            report.update(verified=sorted(verified), remaining=sorted(targets - verified),
                          newly_checked=sorted(verified & checked), reused=sorted(verified - checked),
                          elapsed_seconds=time.monotonic() - started)
            save(report_file, report)
        assert verified == targets
        verify_checkout(source, driver['commit'], build)
        report['outcome'] = 'prewarm-complete'
        print('all target paths have accepted source-matched reports; run the standard full driver next', flush=True)
        return 0
    except Exception as error:
        report.update(outcome='interrupted' if interrupted else 'failed', error=str(error))
        raise
    finally:
        if child is not None and child.poll() is None:
            child.terminate()
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        report['elapsed_seconds'] = time.monotonic() - started
        save(report_file, report)


if __name__ == '__main__':
    raise SystemExit(main())
