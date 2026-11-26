import json
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile

from common.sources import package


def fixture(root, imports, width):
    package(root, "base", [], r"\module Generic(A: \Set) { \definition id[x: A]: A := x; }")
    views = []
    for i in range(imports):
        views.extend([rf"\inductive T{i}: \Set := | unit: T{i};",
                      rf"\import base.Generic[A := T{i}] \as S{i};"])
        if i % 8 == 0:
            views.append(rf"\definition use{i}: T{i} := S{i}.id T{i}::unit;")
    tail = [r"\import \root.Views[] \as V;", r"\definition resumed: V.T0 := V.use0;",
            r"\infer resumed;"]
    tail.extend(rf"\definition p{i}: \Prop := \forall (P: \Prop) -> P -> P;" for i in range(width))
    return package(
        root, "app", ["base"], "\\module Views {\n" + "\n".join(views)
        + "\n}\n\\module Tail {\n" + "\n".join(tail) + "\n}\n")


def interrupt(measurements, entry, seed, directory):
    report = directory / "interrupted.json"
    command = [*measurements.command, str(entry), "--cache-dir", str(seed), "--checkpoint-seconds", "0",
               "--report-json", str(report), "--no-progress", "--time-limit-seconds",
               str(max(1, int(measurements.options.seconds)))]
    environment = dict(measurements.environment, REF_TYPE_PROFILE_PROGRESS="1")
    with subprocess.Popen(command, env=environment, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                          text=True) as child:
        try:
            for line in child.stderr:
                if "event=start module=app.Tail " in line:
                    child.send_signal(signal.SIGINT)
                    child.communicate(timeout=10)
                    break
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
    result = json.loads(report.read_text())
    if child.returncode != 130 or result["outcome"] != "interrupted":
        raise ValueError("fixture finished before interruption; increase --width to extend the tail")
    return result["execution"]["last_checkpoint"]


def run(measurements, directory, imports, width, runs):
    entry = fixture(directory, imports, width)
    seed = directory / "seed"
    seed_position = interrupt(measurements, entry, seed, directory)
    expected = {("base",), ("base", "Generic"), ("app",), ("app", "Views"), ("app", "Tail")}
    digest = None
    for case in ("cold", "resume", "damaged"):
        for iteration in range(runs + 1):
            profile = iteration == 0
            label = f"recovery-{imports}-{case}" + ("-profile" if profile else "")
            with tempfile.TemporaryDirectory(dir=directory) as destination:
                cache = Path(destination)
                if case != "cold":
                    shutil.copytree(seed, cache, dirs_exist_ok=True)
                if case == "damaged":
                    object_path = cache / "objects" / digest[:2] / digest
                    if not object_path.is_file():
                        raise ValueError("profile did not identify the interrupted checkpoint object")
                    object_path.write_bytes(b"damaged checkpoint")
                old = measurements.environment
                if profile:
                    measurements.environment = dict(old, REF_TYPE_PROFILE_PROGRESS="1",
                                                    REF_TYPE_PROFILE_COSTS="namespace.",
                                                    REF_TYPE_PROFILE_ENVIRONMENTS="1")
                try:
                    row = measurements.run(label, entry, cache)
                finally:
                    measurements.environment = old
                if not row["completed"]:
                    raise ValueError(f"check failed; see {row['log']}")
                checker = row["checker"]
                stats = checker["checking"]
                if set(map(tuple, checker["verified_modules"])) != expected:
                    raise ValueError("incomplete fixture coverage")
                if case == "cold" and stats["session"]["retained_tables"]["namespace views"] < imports:
                    raise ValueError("fixture did not create the requested namespace views")
                log = Path(row["log"]).read_text()
                if log.splitlines().count(r"\root.app.Views.T0") != 1:
                    raise ValueError("unexpected projected query result")
                row["seed_position"] = seed_position
                if profile:
                    attempts = re.findall(r"^restore route=(\w+) object=([0-9a-f]{64})$", log, re.M)
                    first = re.search(r"progress elapsed_seconds=([\d.]+).* event=start ", log)
                    if not first:
                        raise ValueError("no source declaration started")
                    row.update(first_observed_declaration_seconds=float(first[1]), candidates=attempts)
                    if case == "resume":
                        if not attempts or attempts[0][0] != "request":
                            raise ValueError("interrupted checkpoint was not a recovery candidate")
                        digest = attempts[0][1]
                    if case == "damaged" and [route for route, _ in attempts][:2] != ["request", "prefix"]:
                        raise ValueError("damaged checkpoint did not reach the fallback candidate")
                measurements.save()
