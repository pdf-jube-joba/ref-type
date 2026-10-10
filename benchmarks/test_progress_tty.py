#!/usr/bin/env python3
"""PTY integration checks: build cli, then run python3 benchmarks/test_progress_tty.py."""
import errno
import os
from pathlib import Path
import pty
import resource
import select
import signal
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]


def run_terminal(path, log, interrupt=False):
    child, terminal = pty.fork()
    if child == 0:
        try:
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            resource.setrlimit(resource.RLIMIT_AS, (1024 ** 3, 1024 ** 3))
            with log.open("wb", buffering=0) as output:
                os.dup2(output.fileno(), 1)
                os.dup2(output.fileno(), 2)
            environment = {k: v for k, v in os.environ.items()
                           if not k.startswith("REF_TYPE_PROFILE_") and k != "RUST_LOG"}
            environment.update(REF_TYPE_PROFILE_PROGRESS="1", REF_TYPE_PROFILE_DECLARATIONS="1")
            os.execve(ROOT / "target/debug/cli",
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
            status, terminal, _ = run_terminal(ROOT / "tests/ok/definition.ref", log)
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
            status, terminal, interrupted = run_terminal(ROOT / "libs/std", log, interrupt=True)
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
