#!/usr/bin/env python3
"""Check every source module, with bounded workers and durable run evidence."""
import argparse
import datetime
import ctypes
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import tomllib


class Failure(Exception):
    pass


def digest(path):
    with open(path, 'rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', nargs='?', default='libs')
    parser.add_argument('--binary', default='target/release/cli')
    parser.add_argument('--state-dir', default='work/repository-check')
    parser.add_argument('--cache-dir')
    parser.add_argument('--memory-mib', type=int, default=3072)
    parser.add_argument('--cache-budget-mib', type=int, default=12288)
    parser.add_argument('--min-free-mib', type=int, default=256)
    parser.add_argument('--time-limit-seconds', type=int)
    args = parser.parse_args()
    for name in ['memory_mib', 'cache_budget_mib', 'min_free_mib']:
        if getattr(args, name) < 0:
            parser.error(name.replace('_', '-') + ' must be nonnegative')
    return args


def main():
    args = arguments()
    binary = Path(args.binary).resolve(strict=True)
    entry = Path(args.path).resolve(strict=True)
    state = Path(args.state_dir).resolve()
    state.mkdir(parents=True, exist_ok=True)
    lock = (state / 'lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise Failure(f'another check owns {state}')
    hint_file = state / 'verified-state.json'
    try:
        hint = json.loads(hint_file.read_text())
    except (OSError, ValueError):
        hint = {}
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    attempt = state / stamp
    attempt.mkdir()
    reserve = attempt / '.report-reserve'
    with reserve.open('wb') as stream:
        os.posix_fallocate(stream.fileno(), 0, 8 * 1024**2)
    snapshot = attempt / 'source.json'
    started = time.monotonic()
    binary_digest = digest(binary)
    commit = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True)
    report = dict(version=1, commit=commit.stdout.strip() if commit.returncode == 0 else None,
                  driver_sha256=digest(Path(__file__)), outcome='running', binary=str(binary), binary_sha256=binary_digest,
                  entry=str(entry), attempts=[], targets=[], verified=[], newly_checked=[], reused=[],
                  save_failures=0, corrupt_cache_reads=0, peak_rss_kib=0, peak_virtual_kib=0,
                  checkpoint_resumes=0, worker_recoveries=0, cache_retained_bytes_upper_bound=0)
    child = None
    interrupted = None
    snapshot_digest = None
    cache = None
    scope_snapshot = attempt / "scope-source.json"
    scope_digest = None
    parent_pid = os.getpid()
    libc = ctypes.CDLL(None, use_errno=True)

    def child_setup():
        # Kill the CLI supervisor too when this driver is externally killed.
        if libc.prctl(1, signal.SIGTERM, 0, 0, 0) != 0 or os.getppid() != parent_pid:
            os._exit(130)

    def cancel(signum, _frame):
        nonlocal interrupted
        interrupted = signum
        if child is not None and child.poll() is None:
            child.send_signal(signal.SIGTERM)

    for signum in [signal.SIGINT, signal.SIGTERM, signal.SIGHUP]:
        signal.signal(signum, cancel)

    def persist():
        report['elapsed_seconds'] = time.monotonic() - started
        save(attempt / 'report.json', report)
        save(state / 'latest.json', {'report': str(attempt / 'report.json'), 'outcome': report['outcome']})

    def invoke(command, label):
        nonlocal child
        if interrupted:
            raise Failure('interrupted; rerun the same command to resume validated caches')
        if snapshot_digest is not None and digest(snapshot) != snapshot_digest:
            raise Failure('saved source snapshot changed during the run')
        if scope_digest is not None and digest(scope_snapshot) != scope_digest:
            raise Failure('scope snapshot changed during the run')
        if digest(binary) != binary_digest:
            raise Failure('checker binary changed during the run')
        if any(shutil.disk_usage(path).free < args.min_free_mib * 1024**2 for path in [state, cache or state]):
            raise Failure(f'disk free space below {args.min_free_mib} MiB; resume after freeing space')
        log = attempt / (label + '.log')
        out = attempt / (label + '.stdout')
        with log.open('wb') as stderr, out.open('wb') as stdout:
            child = subprocess.Popen(command, stdout=stdout, stderr=stderr, preexec_fn=child_setup)
            last_message = time.monotonic()
            disk_failure = False
            stopping_since = None
            while child.poll() is None:
                try:
                    status = dict(line.split(':', 1) for line in Path(f'/proc/{child.pid}/status').read_text().splitlines() if ':' in line)
                    for metric, field in [('peak_rss_kib', 'VmHWM'), ('peak_virtual_kib', 'VmPeak')]:
                        report[metric] = max(report[metric], int(status.get(field, '0').split()[0]))
                except (OSError, ValueError):
                    pass
                if any(shutil.disk_usage(path).free < args.min_free_mib * 1024**2 for path in [state, cache or state]):
                    disk_failure = True
                    child.send_signal(signal.SIGTERM)
                if interrupted or disk_failure:
                    if stopping_since is None:
                        stopping_since = time.monotonic()
                    elif time.monotonic() - stopping_since >= 10:
                        child.kill()
                if time.monotonic() - last_message >= 30:
                    print(f'{label}: {time.monotonic() - started:.0f}s; log {log}', flush=True)
                    last_message = time.monotonic()
                time.sleep(.1)
            code = child.returncode
            child = None
        if disk_failure:
            raise Failure(f'disk free space fell below {args.min_free_mib} MiB; see {log}')
        if interrupted:
            raise Failure(f'interrupted; log {log}; rerun the same command')
        return code, out, log

    base = [str(binary), str(entry), '--memory-mib', str(args.memory_mib)]
    try:
        persist()
        code, output, log = invoke(base + ['--list-modules', '--save-source-snapshot', str(snapshot)], 'enumerate')
        if code:
            raise Failure(f'target enumeration failed ({code}); see {log}')
        targets = output.read_text().splitlines()
        if not targets or len(set(targets)) != len(targets):
            raise Failure('empty or duplicate target list')
        snapshot_digest = digest(snapshot)
        source = json.loads(snapshot.read_text())
        cache = Path(args.cache_dir).resolve() if args.cache_dir else Path(source.get('workspace_root') or entry) / 'refcache'
        cache.mkdir(parents=True, exist_ok=True)
        report.update(targets=targets, source_sha256=digest(snapshot), cache_dir=str(cache),
                      memory_mib=args.memory_mib, cache_budget_mib=args.cache_budget_mib)
        save(attempt / 'targets.json', targets)
        package_entries = {}
        for path, text in source['files'].items():
            if Path(path).name == 'ref.toml':
                package = tomllib.loads(text).get('package', {})
                if 'name' in package:
                    package_entries[package['name']] = str(Path(path).parent)
        report['package_entries'] = package_entries
        roots = [(root, False) for root in targets if '.' not in root]
        pending = list(roots)
        # This hint only chooses a faster execution plan. The CLI still validates
        # every cached object and normally rechecks any miss before success.
        if hint == {'binary_sha256': binary_digest, 'source_sha256': snapshot_digest}:
            pending = [(None, False)]
        if not roots:
            raise Failure('no root modules in enumeration')
        verified, checked = set(), set()
        sequence = 0
        while pending:
            module, only = pending.pop(0)
            wanted = set(targets) if module is None else {t for t in targets if t == module or (not only and t.startswith(module + '.'))}
            if wanted <= verified:
                continue
            sequence += 1
            label = f'{sequence:05d}-{module or "repository"}'
            result_file = attempt / (label + '.json')
            # Change only the entry point: every source byte and alias still comes
            # from the single immutable repository snapshot. Load this package's
            # dependency closure rather than parsing unrelated workspace members.
            scope_entry = package_entries.get(module.split('.')[0], str(entry)) if module else str(entry)
            save(scope_snapshot, dict(source, entry=scope_entry))
            scope_digest = digest(scope_snapshot)
            command = [str(binary), scope_entry, '--memory-mib', str(args.memory_mib),
                              '--source-snapshot', str(scope_snapshot), '--cache-dir', str(cache),
                              '--cache-budget-mib', str(args.cache_budget_mib),
                              '--report-json', str(result_file)]
            if module is not None:
                command += ['--module', module]
            if only:
                command.append('--module-only')
            if args.time_limit_seconds is not None:
                remaining = int(args.time_limit_seconds - (time.monotonic() - started))
                if remaining <= 0:
                    raise Failure('total time limit reached')
                command += ['--time-limit-seconds', str(remaining)]
            print(f'checking {module or "repository"}{" (own declarations)" if only else ""}: {len(verified)}/{len(targets)}', flush=True)
            persist()
            code, _, log = invoke(command, label)
            result = json.loads(result_file.read_text()) if result_file.exists() else {}
            execution = result.get('execution', {})
            storage = result.get('storage', {})
            report['checkpoint_resumes'] += result.get('checking', {}).get('checkpoint_hits', 0)
            report['worker_recoveries'] += execution.get('recoveries', 0)
            report['cache_retained_bytes_upper_bound'] = max(report['cache_retained_bytes_upper_bound'], storage.get('retained_bytes', 0))
            failures = result.get('storage', {}).get('save_failures', 0)
            report['save_failures'] += failures
            report['corrupt_cache_reads'] += result.get('storage', {}).get('corrupt', 0)
            for metric in ['peak_rss_kib', 'peak_virtual_kib']:
                report[metric] = max(report[metric], execution.get(metric, 0))
            report['attempts'].append(dict(module=module, module_only=only, exit_code=code,
                                           outcome=result.get('outcome', 'missing-report'), log=str(log),
                                           report=str(result_file)))
            checked.update('.'.join(p) for p in result.get('checked_modules', []))
            if code == 0 and result.get('outcome') == 'accepted' and not failures:
                coverage = {'.'.join(p) for p in result.get('verified_modules', [])}
                if not wanted <= coverage:
                    raise Failure(f'incomplete coverage for {module}: {sorted(wanted - coverage)[:10]}')
                verified.update(coverage & set(targets))
            elif result.get('outcome') == 'memory-limit' and module is None:
                pending = list(roots)
            elif result.get('outcome') == 'memory-limit' and not only and len(wanted) > 1:
                # Strictly smaller scopes, retaining all declarations and normal dependency checks.
                children = sorted({t[len(module) + 1:].split('.')[0] for t in wanted if t != module})
                pending[0:0] = [(module, True)] + [(module + '.' + c, False) for c in children]
            else:
                raise Failure(f'{module}: {result.get("outcome", "missing-report")} (exit {code}); see {log}')
            report.update(verified=sorted(verified), newly_checked=sorted(verified & checked),
                          reused=sorted(verified - checked))
            persist()
        # Re-read through the same loader to detect additions, removals and alias changes as well as edits.
        final_snapshot = attempt / 'source-final.json'
        code, final_targets, log = invoke(base + ['--list-modules', '--save-source-snapshot', str(final_snapshot)], 'validate-source')
        if code or json.loads(final_snapshot.read_text()) != source or final_targets.read_text().splitlines() != targets:
            raise Failure(f'source or target list changed; see {log}; rerun the same command')
        if digest(binary) != binary_digest or verified != set(targets):
            raise Failure('binary changed or target coverage is incomplete')
        save(hint_file, {'binary_sha256': binary_digest, 'source_sha256': snapshot_digest})
        report['outcome'] = 'accepted'
        print(f'accepted: {len(targets)} targets; {len(verified & checked)} newly checked, {len(verified - checked)} reused')
        return 0
    except (Failure, OSError, ValueError) as error:
        report['outcome'] = 'interrupted' if interrupted else 'failed'
        report['error'] = str(error)
        print(str(error), file=sys.stderr)
        return 130 if interrupted else 2
    finally:
        if child is not None and child.poll() is None:
            child.terminate()
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        reserve.unlink(missing_ok=True)
        if cache is not None:
            logical = allocated = 0
            for directory, _, files in os.walk(cache):
                for name in files:
                    try:
                        stat = (Path(directory) / name).stat()
                        logical += stat.st_size
                        allocated += stat.st_blocks * 512
                    except FileNotFoundError:
                        pass
            report.update(cache_bytes=logical, cache_allocated_bytes=allocated,
                          disk_free_bytes=shutil.disk_usage(cache).free)
        persist()
        print(f'report: {attempt / "report.json"}', flush=True)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (Failure, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(2)
