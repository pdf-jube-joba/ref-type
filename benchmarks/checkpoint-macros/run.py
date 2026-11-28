import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def workspace(root):
    template = " -> ".join(["$p"] * 32)
    lines = [r"\module Templates {"]
    lines.extend(rf"\macro repeat{i}($p) := {template};" for i in range(32))
    lines.extend(["}", r"\module Shared {"])
    for i in range(72):
        lines.append(rf"\import \root.Templates[] \as T{i};")
        lines.append(rf"\use T{i}.repeat0 \as alias{i};")
    lines.append("}")
    files = {
        "ref.toml": '[workspace]\npackages = ["macros", "consumer"]\n',
        "macros/ref.toml": '[package]\nname = "macros"\n',
        "macros/src/root.ref": "\n".join(lines) + "\n",
        "consumer/ref.toml": '[package]\nname = "consumer"\n[dependencies]\nmacros = {path = "../macros"}\n',
        "consumer/src/root.ref": r"""\module First {
    \definition accepted[P: \Prop][p: P]: P := p;
}
\module Next {
    \import macros.Shared[] \as S;
    \use S.alias0;
    \definition expanded[P: \Prop]: \Prop := alias0!{P};
}
""",
    }
    digest = hashlib.sha256()
    for name, content in sorted(files.items()):
        path = root / name
        if path.exists() and path.read_bytes() != content.encode():
            raise ValueError(f"unexpected contents in {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content.encode())
        digest.update(name.encode() + b"\0" + content.encode() + b"\0")
    return digest.hexdigest()


def run(cli, root, out, stage, *options):
    report = out / f"{stage}.json"
    cmd = [cli, root, "--cache-dir", out / "cache", "--no-progress",
           "--time-limit-seconds", "240", "--report-json", report, *options]
    env = dict(os.environ, REF_TYPE_PROFILE_PROGRESS="1", REF_TYPE_PROFILE_PHASES="1")
    with (out / f"{stage}.log").open("w") as log:
        subprocess.run(cmd, env=env, stdout=log, stderr=log, check=True)
    return json.loads(report.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("result_dir", type=Path)
    args = parser.parse_args()
    root = args.workspace.resolve()
    out = args.result_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    digest = workspace(root)
    cli = args.binary.resolve(strict=True)
    seed = run(cli, root, out, "seed", "--module", "macros")
    if seed["outcome"] != "accepted" or seed["execution"]["last_checkpoint"] == 0:
        raise RuntimeError(f"expected a published dependency checkpoint, see {out}")
    result = run(cli, root, out, "resume")
    log = (out / "resume.log").read_text()
    scope = re.findall(r"phase=resolve.reconnect-scope-macros elapsed_us=(\d+) "
                       r"rss_kib=Some\((\d+)\) rss_delta_kib=Some\((-?\d+)\)", log)
    first = re.search(r"progress elapsed_seconds=([\d.]+).*event=complete action=Check module=consumer.First ", log)
    checked = {tuple(path) for path in result["checked_modules"]}
    execution = result["execution"]
    if (result["outcome"] != "accepted" or result["checking"]["environment_hits"] != 1
            or len(scope) != 1 or not first or checked != {("consumer",), ("consumer", "First"), ("consumer", "Next")}
            or execution["duplicate_source_steps"] or execution["replayed_source_steps"]):
        raise RuntimeError(f"expected one dependency restore and fresh consumer checks, see {out}")
    warm = run(cli, root, out, "warm")
    if not warm["cache"]["verification_reused"] or warm["execution"]["source_steps"]:
        raise RuntimeError(f"expected warm result reuse, see {out}")
    row = dict(input_sha256=digest, checkpoint_steps=seed["execution"]["last_checkpoint"],
               first_new_declaration="consumer.First.accepted", first_new_accepted_seconds=float(first[1]),
               scope_elapsed_us=int(scope[0][0]), scope_rss_kib=int(scope[0][1]),
               scope_rss_delta_kib=int(scope[0][2]), peak_worker_rss_kib=execution["peak_rss_kib"],
               source_steps=execution["source_steps"])
    print(json.dumps(row, indent=2))


if __name__ == "__main__":
    main()
