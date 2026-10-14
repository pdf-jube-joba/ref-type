#!/usr/bin/env python3
"""CLI output, cache side effects and terminal integration checks on small fixtures."""
import errno
import os
from pathlib import Path
import pty
import resource
import select
import signal
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")) / "debug/cli"


def clean_environment(**extra):
    environment = {k: v for k, v in os.environ.items()
                   if not k.startswith("REF_TYPE_PROFILE_")
                   and k not in {"RUST_LOG", "REF_TYPE_COMPACT_DIAGNOSTICS"}}
    environment.update(extra)
    return environment


def run_check(path, *args, **environment):
    return subprocess.run([str(BINARY), str(path), *args],
                          env=clean_environment(**environment),
                          capture_output=True, text=True, timeout=20)


class CliOutputTests(unittest.TestCase):
    def test_no_cache_leaves_saved_files_unchanged_even_with_zero_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "ref.toml").write_text('[package]\nname = "small"\n')
            (root / "src").mkdir()
            (root / "src/root.ref").write_text(
                r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }")
            first = run_check(root)
            self.assertEqual(first.returncode, 0, first.stderr)
            cache = root / "refcache"

            def contents():
                return {p.relative_to(cache): p.read_bytes()
                        for p in cache.rglob("*") if p.is_file()}

            before = contents()
            self.assertTrue(before)
            uncached = run_check(root, "--no-cache", "--cache-budget-mib", "0", "--no-progress")
            self.assertEqual(uncached.returncode, 0, uncached.stderr)
            self.assertEqual(contents(), before)

    def test_piped_progress_profiles_and_timings_keep_module_order_and_totals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "root.ref"
            root.write_text(r"\module Parent { \module Child { \infer \Set; } }")
            for cached in [False, True]:
                with self.subTest(cached=cached):
                    output = run_check(root, REF_TYPE_PROFILE_PROGRESS="1")
                    self.assertEqual(output.returncode, 0, output.stderr)
                    log = output.stderr
                    self.assertIn("event=planned", log)
                    self.assertIn("event=finished success=true", log)
                    action = "Skip" if cached else "Check"
                    for module in ["Parent", "Parent.Child"]:
                        end = log.index(f"event=complete action={action} module={module} module_seconds=")
                        if not cached:
                            start = log.index(f"event=start module={module} package_completed=")
                            self.assertLess(start, end)
                    summary = "skip " if cached else "check "
                    self.assertLess(log.index("event=finished"), log.index(summary + "Parent ("))
                    self.assertNotIn("\r", log)
                    timings = {}
                    for line in log.splitlines():
                        if line.startswith((summary, "shared (", "total (")):
                            label, seconds = line.rsplit(" (", 1)
                            timings[label] = float(seconds.removesuffix("s)"))
                    self.assertEqual(set(timings), {summary + "Parent", summary + "Parent.Child", "shared", "total"})
                    self.assertTrue(all(seconds >= 0 for seconds in timings.values()))
                    self.assertGreater(timings["total"], 0)
                    self.assertAlmostEqual(sum(v for k, v in timings.items() if k != "total"),
                                           timings["total"], delta=timings["total"] * 0.01)

    def test_cost_profiles_finish_on_success_and_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "root.ref"
            for body, code in [(r"\definition identity(P: \Prop)(p: P): P := p;", 0),
                               (r"\definition invalid: \Prop := \Set;", 1)]:
                with self.subTest(code=code):
                    root.write_text("\\module Root { " + body + " }")
                    output = run_check(root, "--no-cache", "--no-progress", "--diagnostics", "compact",
                                       REF_TYPE_PROFILE_COSTS="resolve.total,kernel.")
                    self.assertEqual(output.returncode, code, output.stderr)
                    self.assertIn("cost=resolve.total calls=1", output.stderr)
                    self.assertIn("cost_group=kernel exclusive_us=", output.stderr)
                    self.assertEqual(output.stderr.count("cost_total elapsed_us="), 1)
                    self.assertNotIn("cost=resolve.front-binding", output.stderr)
                    self.assertNotIn("cost=", output.stdout)

    def test_parent_and_external_imports_check_the_shared_declaration_once(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "root.ref"
            root.write_text(r"""
\module Parent {
  \module Child { \definition marker: \Prop := \forall (P: \Prop) -> P -> P; }
  \import \root.Parent[].Child[] \as Local;
  \infer Local.marker;
}
\module Other {
  \import \root.Parent[].Child[] \as External;
  \infer External.marker;
}
""")
            output = run_check(root, "--no-cache", REF_TYPE_PROFILE_DECLARATIONS="1")
            self.assertEqual(output.returncode, 0, output.stderr)
            self.assertEqual(output.stderr.count("definition marker (excluding diagnostics)"), 1)


def run_terminal(path, log, interrupt=False):
    child, terminal = pty.fork()
    if child == 0:
        try:
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            resource.setrlimit(resource.RLIMIT_AS, (1024 ** 3, 1024 ** 3))
            with log.open("wb", buffering=0) as output:
                os.dup2(output.fileno(), 1)
                os.dup2(output.fileno(), 2)
            environment = clean_environment(REF_TYPE_PROFILE_PROGRESS="1", REF_TYPE_PROFILE_DECLARATIONS="1")
            os.execve(BINARY,
                      ["cli", str(path), "--no-cache", "--progress-tty"], environment)
        finally:
            os._exit(127)
    captured = bytearray()
    sent_interrupt = False
    reaped = False
    deadline = time.monotonic() + 15
    try:
        while time.monotonic() < deadline:
            if select.select([terminal], [], [], 0.01)[0]:
                try:
                    captured.extend(os.read(terminal, 65536))
                except OSError as error:
                    if error.errno != errno.EIO:
                        raise
            if interrupt and not sent_interrupt and b"\x1b[2K" in captured:
                if log.exists() and "checking " in log.read_text():
                    # The terminal driver delivers SIGINT to its foreground process group.
                    os.write(terminal, b"\x03")
                    sent_interrupt = True
            waited, status = os.waitpid(child, os.WNOHANG)
            if waited:
                reaped = True
                while select.select([terminal], [], [], 0)[0]:
                    try:
                        remaining = os.read(terminal, 65536)
                    except OSError as error:
                        if error.errno == errno.EIO:
                            break
                        raise
                    if not remaining:
                        break
                    captured.extend(remaining)
                return os.waitstatus_to_exitcode(status), captured, sent_interrupt
        raise AssertionError("CLI did not exit within 15 seconds")
    finally:
        if not reaped:
            try:
                os.killpg(child, signal.SIGKILL)
            except ProcessLookupError:
                pass
            os.waitpid(child, 0)
        os.close(terminal)


class ProgressTerminalTests(unittest.TestCase):
    def test_bar_and_summary_go_to_terminal_while_profiles_and_timings_go_to_log(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "details.log"
            source = Path(directory) / "root.ref"
            source.write_text(r"\module Test(A: \Set) { \definition B: \Set := A; }")
            status, terminal, _ = run_terminal(source, log)
            details = log.read_text()
            self.assertEqual(status, 0, details)
            self.assertIn(b"\x1b[2K", terminal)
            self.assertIn(b"Finished", terminal)
            self.assertNotIn(b"checking ", terminal)
            self.assertNotIn(b"progress elapsed_seconds=", terminal)
            self.assertIn("checking ", details)
            self.assertIn("event=finished success=true", details)
            self.assertIn("\ncheck ", details)
            self.assertIn("\ntotal (", details)
            self.assertNotIn("\x1b[2K", details)

    def test_ctrl_c_stops_checking_and_preserves_live_log(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "details.log"
            source = Path(directory) / "root.ref"
            declarations = "".join(
                f"\\definition value{index}: \\Prop := \\forall (P: \\Prop) -> P -> P;\n"
                for index in range(2_000)
            )
            source.write_text("\\module Slow {\n" + declarations + "}\n")
            status, terminal, interrupted = run_terminal(source, log, interrupt=True)
            self.assertTrue(interrupted)
            self.assertEqual(status, -signal.SIGINT)
            self.assertIn(b"\x1b[2K", terminal)
            details = log.read_text()
            self.assertIn("event=start module=", details)
            self.assertIn("checking ", details)
            self.assertNotIn("event=finished success=true", details)
            self.assertNotIn("\x1b[2K", details)


if __name__ == "__main__":
    unittest.main()
