#!/usr/bin/env python3
"""Exercise the documented cargo-run entry point and the real HTTP server."""
from contextlib import contextmanager
from html.parser import HTMLParser
from pathlib import Path
from queue import Queue, Empty
from threading import Thread
from urllib.error import HTTPError
from urllib.parse import urlsplit, unquote
from urllib.request import urlopen
import os
import re
import signal
import socket
import subprocess
import tempfile

EXTENSION = Path(__file__).resolve().parents[1]
REPO = EXTENSION.parents[1]


@contextmanager
def server(*args):
    process = subprocess.Popen(
        ["cargo", "run", "--locked", "--offline", "--", *args],
        cwd=EXTENSION, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, start_new_session=True,
    )
    output = Queue()
    def collect():
        for line in process.stdout:
            output.put(line)
        output.put(None)
    Thread(target=collect, daemon=True).start()
    log = []
    try:
        while True:
            try:
                line = output.get(timeout=180)
            except Empty:
                raise AssertionError("Startup timed out: " + "".join(log))
            assert line is not None, "Server exited: " + "".join(log)
            log.append(line)
            match = re.search(r"Ref Type docs: (http://127\.0\.0\.1:\d+/)", line)
            if match:
                print("".join(log).strip())
                yield match[1]
                break
    finally:
        os.killpg(process.pid, signal.SIGINT) if process.poll() is None else None
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        process.stdout.close()


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.links, self.ids = [], set()
        self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])


def get(base, path=""):
    with urlopen(base.rstrip("/") + "/" + path.lstrip("/"), timeout=20) as response:
        assert response.status == 200
        assert response.headers["X-Content-Type-Options"] == "nosniff"
        assert "default-src 'none'" in response.headers["Content-Security-Policy"]
        return response.read().decode()


def crawl(base):
    pending, pages, anchors = ["/"], {}, []
    while pending:
        path = pending.pop()
        if path in pages:
            continue
        html = get(base, path)
        page = pages[path] = Page(html)
        for link in page.links:
            parsed = urlsplit(link)
            if parsed.scheme or parsed.netloc:
                continue
            target = parsed.path or path
            assert target.startswith("/"), (path, link)
            pending.append(target)
            if parsed.fragment:
                anchors.append((path, target, unquote(parsed.fragment)))
    for source, target, anchor in anchors:
        assert anchor in pages[target].ids, (source, target, anchor)
    print(f"HTTP crawl: {len(pages)} pages and {len(anchors)} fragment links passed")
    return pages


def failures(base):
    for path in ["file/999999", "source/999999", "dir/999999", "../Cargo.toml", "%2e%2e/etc/passwd", "source/%2e%2e%2fetc%2fpasswd", "file/-1", "file/999999999999999999999999999"]:
        try:
            get(base, path)
            raise AssertionError("Unexpected accessible path: " + path)
        except HTTPError as error:
            assert error.code in (400, 404), (path, error.code)
    port = urlsplit(base).port
    result = subprocess.run([str(REPO / "target/debug/ref-docs"), "--port", str(port)], capture_output=True, text=True, timeout=10)
    assert result.returncode != 0 and "--port 0" in result.stderr


with server("--port", "0") as base:
    pages = crawl(base)
    count = len([path for path in pages if path.startswith("/file/")])
    expected = len(list((REPO / "libs").rglob("*.ref")))
    assert count == expected, (count, expected)
    assert "Nat" in get(base, "search")
    failures(base)

with tempfile.TemporaryDirectory(prefix="ref-docs-http-") as directory:
    fixture = Path(directory)
    (fixture / "README.md").write_text('# Fixture\n\n<script>alert(1)</script>\n\n[bad](javascript:alert%281%29)\n')
    (fixture / "root.ref").write_text('/* **Docs** & <img src=x onerror=alert(1)> 日本語 */\n\\definition id (A: \\Set): A -> A := \\fun (x: A) => x;\n')
    (fixture / "empty.ref").write_text("")
    (fixture / "bad.ref").write_text("\\definition broken: ;")
    (fixture / "empty").mkdir()
    (fixture / "secret.txt").write_text("SECRET_CONTENT")
    (fixture / "outside.ref").symlink_to("/etc/passwd")
    (fixture / "loop").symlink_to(fixture, target_is_directory=True)
    with server("--libs", directory, "--port", "0") as base:
        pages = crawl(base)
        all_html = "\n".join(get(base, path) for path in pages)
        assert "<strong>Docs</strong>" in all_html
        assert "&lt;img src=x onerror=alert(1)&gt;" in all_html
        assert 'href="javascript:' not in all_html
        assert "<script>alert(1)</script>" not in all_html
        assert "SECRET_CONTENT" not in all_html
        assert "No named declarations" in all_html
        assert "Could not parse" in all_html
        failures(base)
    for path in [fixture / "missing", fixture / "secret.txt"]:
        result = subprocess.run([str(REPO / "target/debug/ref-docs"), "--libs", str(path), "--port", "0"], capture_output=True, text=True, timeout=10)
        assert result.returncode != 0 and "ref-docs:" in result.stderr

# Verify the documented fixed default independently of the ephemeral-port checks.
try:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 3030))
except OSError:
    print("Default port 3030 already occupied; fixed-port launch skipped")
else:
    with server() as base:
        assert base == "http://127.0.0.1:3030/"
        assert "Library explorer" in get(base)
print("Startup, enumeration, links, escaping, traversal and failure checks passed")
