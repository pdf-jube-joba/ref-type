#!/usr/bin/env python3
"""Check every library in bounded processes, splitting oversized module trees.

The JSON report records complete coverage, errors and resource failures separately.
Successful checker results are reused through the ordinary source-keyed disk cache.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = ('library', 'category', 'homological-algebra', 'topological-k-theory',
            'manifolds-de-rham', 'product-compactness', 'module-expressions')


def inputs_digest():
    digest = hashlib.sha256()
    for base in ('libs', 'tests/projects'):
        for path in sorted((ROOT / base).rglob('*')):
            if path.suffix == '.ref' or path.name == 'ref.toml':
                digest.update(str(path.relative_to(ROOT)).encode())
                digest.update(path.read_bytes())
    return digest.hexdigest()


def packages():
    ordered = []
    seen = set()

    def visit(path):
        path = path.resolve()
        if path in seen:
            return
        seen.add(path)
        manifest = tomllib.loads((path / 'ref.toml').read_text())
        for dependency in manifest.get('dependencies', {}).values():
            visit(path / dependency['path'])
        ordered.append(path)

    for manifest in sorted((ROOT / 'libs').glob('*/ref.toml')):
        visit(manifest.parent)
    for name in PROJECTS:
        visit(ROOT / 'tests/projects' / name)
    for manifest in sorted((ROOT / 'tests/projects/pointwise-quotient').glob('*/ref.toml')):
        visit(manifest.parent)
    return ordered


def run(command, log, memory_mib, seconds):
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (memory_mib * 2**20,) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (seconds, seconds + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    started = time.monotonic()
    next_progress = started + 30
    timed_out = False
    with log.open('w') as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=output,
                                   start_new_session=True, preexec_fn=limits)
        try:
            while True:
                waited, status, usage = os.wait4(process.pid, os.WNOHANG)
                if waited:
                    break
                now = time.monotonic()
                if now - started >= seconds:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                if now >= next_progress:
                    print(f'  running {now - started:.0f}s: {log.name}', flush=True)
                    next_progress = now + 30
                time.sleep(.05)
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
    text = log.read_text(errors='replace')
    exhausted = timed_out or process.returncode in (-signal.SIGKILL, -signal.SIGXCPU)
    exhausted |= process.returncode == -signal.SIGABRT and 'memory allocation of' in text
    return dict(exit=process.returncode, seconds=round(time.monotonic() - started, 3),
                peak_rss_kib=usage.ru_maxrss, resource_limit=bool(exhausted),
                log=str(log.relative_to(ROOT)) if log.is_relative_to(ROOT) else str(log))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/debug/cli')
    parser.add_argument('--memory-mib', type=int, default=3072)
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--cache-dir', type=Path, default=ROOT / 'refcache/library-check')
    parser.add_argument('--output', type=Path, default=ROOT / 'benchmarks/library-check.json')
    args = parser.parse_args()
    if args.memory_mib < 1 or args.seconds < 1:
        parser.error('resource limits must be positive')
    args.output = args.output.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    logs = args.output.with_suffix('')
    logs.mkdir(exist_ok=True)
    binary = args.binary.resolve()
    previous = json.loads(args.output.read_text()) if args.output.exists() else {}
    old_packages = {p['path']: p for p in previous.get('packages', [])}
    binary_stat = binary.stat()
    report = dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  sources_sha256=inputs_digest(), memory_mib=args.memory_mib,
                  seconds_per_batch=args.seconds, packages=[], complete=False)

    def save():
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(args.output)

    save()
    for path in (args.paths or packages()):
        path = path.resolve()
        name = tomllib.loads((path / 'ref.toml').read_text())['package']['name']
        package = dict(path=str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
                       name=name, batches=[], verified=[], failed=[], complete=False)
        old = old_packages.get(package['path'], {})
        splits = set(old.get('splits', [])) | {b['module'] for b in old.get('batches', [])
                    if b['resource_limit'] and not b['exact']}
        layout_key = hashlib.sha256(str(path).encode()).hexdigest()
        layout_path = args.cache_dir.resolve() / (layout_key + '.batches.json')
        package_logs = logs / (path.relative_to(ROOT) if path.is_relative_to(ROOT)
                               else f'{name}-{layout_key[:12]}')
        package_logs.mkdir(parents=True, exist_ok=True)
        try:
            cached_layout = json.loads(layout_path.read_text())
            if isinstance(cached_layout, list) and all(isinstance(p, str) for p in cached_layout):
                splits.update(cached_layout)
        except (OSError, ValueError):
            pass

        def save_layout():
            package['splits'] = sorted(splits)
            try:
                layout_path.parent.mkdir(parents=True, exist_ok=True)
                temporary = layout_path.with_suffix(f'.{os.getpid()}.tmp')
                temporary.write_text(json.dumps(package['splits']) + '\n')
                temporary.replace(layout_path)
            except OSError:
                pass  # The report still retains the layout; checking is unaffected.

        save_layout()
        report['packages'].append(package)
        command = [str(binary), str(path), '--diagnostics', 'compact',
                   '--cache-dir', str(args.cache_dir.resolve()), '--no-progress',
                   '--memory-mib', str(args.memory_mib)]
        listing = package_logs / 'modules.log'
        result = run(command + ['--list-modules'], listing, args.memory_mib, args.seconds)
        if result['exit']:
            package['failed'].append(dict(module=name, **result))
            save()
            continue
        paths = [line for line in listing.read_text().splitlines()
                 if line == name or line.startswith(name + '.')]
        if name not in paths:
            raise RuntimeError(f'checker did not list the root module {name}')
        package['source_modules'] = len(paths)
        pending = [(name, False)]
        while pending:
            module, exact = pending.pop()
            if binary.stat().st_mtime_ns != binary_stat.st_mtime_ns:
                report['interrupted'] = 'checker binary changed during the run'
                save()
                return 1
            children = [p for p in paths if p.rpartition('.')[0] == module]
            if module in splits and not exact and children:
                pending.extend((child, False) for child in reversed(children))
                pending.append((module, True))
                continue
            label = module + ('-only' if exact else '')
            log = package_logs / f'{label}.log'
            print(f'check {label}', flush=True)
            result = run(command + ['--module', module] + (['--module-only'] if exact else []),
                         log, args.memory_mib, args.seconds)
            package['batches'].append(dict(module=module, exact=exact, **result))
            covered = [module] if exact else [p for p in paths if p == module or p.startswith(module + '.')]
            if result['exit'] == 0:
                package['verified'].extend(covered)
                print(f'  ok {result["seconds"]}s, {result["peak_rss_kib"] / 1024:.0f} MiB', flush=True)
            elif result['resource_limit'] and not exact and len(covered) > 1:
                splits.add(module)
                # Unary wrappers preserve almost the entire failed workload.
                nested = children
                while len(nested) == 1:
                    child = nested[0]
                    nested = [p for p in paths if p.rpartition('.')[0] == child]
                    if nested:
                        splits.add(child)
                save_layout()
                pending.extend((child, False) for child in reversed(children))
                pending.append((module, True))
                print(f'  split into {len(children)} children and parent declarations', flush=True)
            else:
                package['failed'].append(dict(module=module, exact=exact, **result))
                print(f'  FAILED: {result["log"]}', flush=True)
            save()
        package['verified'] = sorted(set(package['verified']))
        package['complete'] = not package['failed'] and set(package['verified']) == set(paths)
        save()
    report['binary_unchanged'] = hashlib.sha256(binary.read_bytes()).hexdigest() == report['binary_sha256']
    report['sources_unchanged'] = inputs_digest() == report['sources_sha256']
    report['complete'] = report['sources_unchanged'] and report['binary_unchanged'] and all(p['complete'] for p in report['packages'])
    save()
    print(f'complete={report["complete"]}; report: {args.output}', flush=True)
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
