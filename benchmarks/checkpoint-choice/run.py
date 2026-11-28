import argparse
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common.measurements import file_digest, save_json
from common.sources import package, source_digest
from scaling.generators import workspace


def fixture(root):
    template = " ".join(["$x"] * 180)
    package(root, "base", [], (
        r"\module Core { \inductive T: \Set := | unit: T; \macro wide($x) := ("
        + template + "); }"
    ))
    lines = [r"\module Heavy { \import base.Core[] \as B;"]
    lines.extend(rf"\use B.wide \as alias{i};" for i in range(1800))
    lines.extend(rf"\definition id{i}[x: B.T]: B.T := x;" for i in range(64))
    lines.append(r"} \module Tail { \import base.Core[] \as B;")
    lines.extend(
        rf"\definition p{i}[x: B.T]: B.T := (\fun (y: B.T) => y) x;"
        for i in range(1500)
    )
    lines.extend([
        r"} \module Witness { \import base.Core[] \as B;",
        r"\import \root.Heavy[] \as H;",
        r"\definition newValue: B.T := H.id63 B.T::unit;",
        r"\infer newValue; }",
    ])
    package(root, "app", ["base"], "\n".join(lines))
    return workspace(root, ["app"])


def run(binary, entry, cache, output, cap=None, seed=False):
    report = output.with_suffix(".json")
    command = [binary, str(entry), "--cache-dir", str(cache), "--report-json", str(report),
               "--no-progress", "--checkpoint-seconds", "0", "--time-limit-seconds", "60"]
    env = dict(os.environ, REF_TYPE_PROFILE_PROGRESS="1", REF_TYPE_PROFILE_ENVIRONMENTS="1")
    limit = cap * 1024**2 if cap is not None else None
    started = time.monotonic()
    with output.with_suffix(".log").open("w") as log, subprocess.Popen(
        command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        preexec_fn=None if limit is None else lambda: resource.setrlimit(resource.RLIMIT_AS, (limit, limit)),
    ) as child:
        sent = False
        for line in child.stdout:
            log.write(line)
            if seed and not sent and "event=start module=app.Tail " in line:
                child.send_signal(signal.SIGINT)
                sent = True
        status = child.wait()
    elapsed = time.monotonic() - started
    data = json.loads(report.read_text())
    text = output.with_suffix(".log").read_text()
    execution = data["execution"]
    checking = data["checking"]
    attempts = [
        dict(route=route, object=digest, decoded_bytes=int(size))
        for route, digest, size in re.findall(
            r"^restore route=(\w+) object=([0-9a-f]{64}) decoded_bytes=(\d+)$", text, re.M)
    ]
    if seed:
        if (status != 130 or data["outcome"] != "interrupted" or not sent
                or "event=start module=app.Witness " in text or execution["last_checkpoint"] != 70):
            raise ValueError(f"missed the interrupted Heavy boundary; see {output}.log")
    elif data["outcome"] == "accepted":
        expected = {"base", "base.Core", "app", "app.Heavy", "app.Tail", "app.Witness"}
        if (status != 0 or {".".join(p) for p in data["verified_modules"]} != expected
                or ["app", "Witness"] not in data["checked_modules"]
                or text.splitlines().count(r"\root.base.Core.T") != 1):
            raise ValueError(f"incomplete coverage or unexpected witness; see {report}")
        if cap is None and (checking["checkpoint_hits"] != 1 or execution["workers"] != 1):
            raise ValueError(f"ample-memory run did not use the interrupted checkpoint; see {report}")
        if cap is not None and not (
            checking["environment_hits"] and attempts and attempts[-1]["route"] == "prefix"
            and attempts[-1]["decoded_bytes"] < attempts[0]["decoded_bytes"]
        ):
            raise ValueError(f"cap did not exercise a smaller prefix; see {report}")
    elif cap is None or status != 2 or data["outcome"] != "memory-limit":
        raise ValueError(f"unexpected outcome {data['outcome']}; see {report}")
    if not seed and (not attempts or attempts[0]["route"] != "request"):
        raise ValueError(f"missing interrupted request candidate; see {report}")
    return dict(outcome=data["outcome"], wall_seconds=elapsed, as_limit_mib=cap,
                execution=execution, attempts=attempts, checkpoint_hits=checking["checkpoint_hits"],
                prefix_hits=checking["environment_hits"], checked_modules=data["checked_modules"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True, type=Path, action="append")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--as-mib", type=int, default=80)
    args = parser.parse_args()
    if args.runs < 1 or args.as_mib < 1:
        parser.error("--runs and --as-mib must be positive")
    args.output.mkdir(parents=True, exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        entry = fixture(root / "workspace")
        for index, binary in enumerate(args.binary):
            binary = binary.resolve(strict=True)
            logs = args.output / f"binary-{index}"
            logs.mkdir()
            seed = root / f"seed-{index}"
            interrupted = run(binary, entry, seed, logs / "seed", seed=True)
            result = dict(binary=str(binary), sha256=file_digest(binary), source=source_digest(entry),
                          seed=interrupted, runs=[])
            rows.append(result)
            for iteration in range(args.runs):
                cases = [("ample", None), ("pressure", args.as_mib)]
                for label, cap in (cases if iteration % 2 == 0 else reversed(cases)):
                    with tempfile.TemporaryDirectory(dir=root) as cache:
                        shutil.copytree(seed, cache, dirs_exist_ok=True)
                        row = run(binary, entry, cache, logs / f"{label}-{iteration}", cap)
                    row.update(case=label, iteration=iteration)
                    result["runs"].append(row)
                    save_json(args.output / "summary.json", rows)


if __name__ == "__main__":
    main()
