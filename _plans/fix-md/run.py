#!/usr/bin/env python3
"""Check every standalone case in a fresh directory and record both diagnostic streams."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def validate_catalog():
    """Compare the source headings, report, catalog and files before executing anything."""
    catalog = json.loads((HERE / "catalog.json").read_text())
    items = catalog["items"]
    report = (HERE / "README.md").read_text()
    gaps = (HERE.parent / "gaps.md").read_text()
    headings = re.findall(r"^## (G\d{2}): (.+)$", gaps, re.MULTILINE)
    raw_headings = re.findall(r"^## .+$", gaps, re.MULTILINE)

    def require(condition, message):
        if not condition:
            raise ValueError(message)

    require(headings and len(headings) == len(raw_headings), "gaps.md: unnumbered heading")
    require([ident for ident, _ in headings] == [f"G{i:02}" for i in range(1, len(headings) + 1)],
            "gaps.md: numbering does not follow heading order")
    require(headings == [(item["id"], item["title"]) for item in items[:len(headings)]],
            "catalog: parent IDs/titles differ from gaps.md order")
    require(re.findall(r"^\| \[(G\d{2})\]\(#g\d{2}\) \|", report, re.MULTILINE)
            == [item["id"] for item in items], "README: parent table order differs from catalog")
    detail_headings = list(re.finditer(r"^## (G\d{2}(?:・G\d{2})*):", report, re.MULTILINE))
    require([ident for heading in detail_headings for ident in heading[1].split("・")]
            == [item["id"] for item in items], "README: explanation headings differ from catalog")
    documented = re.findall(r"\*\*(G\d{2}\.\d{2})\*\* \[`([^`]+)`\]\(cases/([^\)]+)\)", report)
    for index, heading in enumerate(detail_headings):
        end = detail_headings[index + 1].start() if index + 1 < len(detail_headings) else len(report)
        section_ids = re.findall(r"\*\*(G\d{2})\.\d{2}\*\*", report[heading.end():end])
        require(all(ident in heading[1].split("・") for ident in section_ids),
                f"README: case under wrong parent heading {heading[1]}")
    cases = []
    for number, item in enumerate(items, 1):
        ident = item["id"]
        require(ident == f"G{number:02}", f"catalog: expected parent G{number:02}")
        source = (HERE / item["source"]).read_text()
        source_headings = re.findall(r"^(?:>\s*)?## (G\d{2}): (.+)$", source, re.MULTILINE)
        require((ident, item["title"]) in source_headings, f"{ident}: source heading differs")
        require((item["source"] == "../gaps.md") == (number <= len(headings)),
                f"{ident}: wrong main/split source")
        if number > len(headings):
            require(source_headings == [(ident, item["title"])], f"{ident}: extra split-source IDs")
        require(item["anchor"] == ident.lower(), f"{ident}: wrong source anchor")
        require(f'<a id="{item["anchor"]}"></a>' in source, f"{ident}: missing source anchor")
        require(f'<a id="{ident.lower()}"></a>' in report, f"{ident}: missing report anchor")
        require(f"(fix-md/README.md#{ident.lower()})" in source, f"{ident}: missing backlink")
        require(f'[{item["title"]}]({item["source"]}#{item["anchor"]})' in report,
                f"{ident}: wrong report source link")
        require(item["cases"], f"{ident}: no cases")
        for branch, case in enumerate(item["cases"], 1):
            case_id, filename = case["id"], case["file"]
            require(case_id == f"{ident}.{branch:02}", f"{ident}: nonsequential branch ID")
            require(re.fullmatch(rf"{number:02}-{branch:02}-[a-z0-9-]+\.ref", filename),
                    f"{case_id}: filename prefix differs")
            require(documented.count((case_id, filename, filename)) == 1,
                    f"{case_id}: missing, duplicate or mismatched README explanation")
            data = (HERE / "cases" / filename).read_bytes()
            lines = len(data.splitlines())
            require(0 < lines <= 30, f"{case_id}: {lines} physical lines (maximum 30)")
            cases.append({"id": case_id, "case": filename, "lines": lines,
                          "sha256": hashlib.sha256(data).hexdigest()})
    names = [case["case"] for case in cases]
    require(len(names) == len(set(names)), "catalog: duplicate file")
    require(set(names) == {p.relative_to(HERE / "cases").as_posix()
                           for p in (HERE / "cases").rglob("*.ref")},
            "catalog: missing or unregistered .ref file")
    require(len(documented) == len(cases), "README: extra case explanations")
    require([entry[0] for entry in documented] == [case["id"] for case in cases],
            "README: explanation branch order differs from catalog")
    print(f"Catalog: {len(items)} parents, {len(cases)} cases, maximum {max(c['lines'] for c in cases)} lines")
    return catalog, cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/cli")
    parser.add_argument("--output", type=Path, help="write all measured results as JSON")
    parser.add_argument("--validate-only", action="store_true", help="check numbering and physical line counts")
    args = parser.parse_args()
    try:
        catalog, cases = validate_catalog()
    except (ValueError, KeyError, OSError) as error:
        print(f"Catalog validation failed: {error}")
        return 1
    if args.validate_only:
        if args.output:
            parser.error("--output requires execution; omit --validate-only")
        return 0
    executable = args.cli.resolve()
    if not executable.is_file():
        parser.error(f"CLI not found: {executable}; run cargo build --locked -p cli")
    env = {k: v for k, v in os.environ.items()
           if k != "RUST_LOG" and not k.startswith(("REF_TYPE_", "REF_INVESTIGATION_"))}
    results = []
    for case in cases:
        source = HERE / "cases" / case["case"]
        expected = re.findall(r"^/\* expect-error: (.+) \*/$", source.read_text(), re.MULTILINE)
        expected_exit = 1 if expected else 0
        result = {**case, "expected_exit": expected_exit, "expected_errors": expected}
        with tempfile.TemporaryDirectory(prefix="ref-standalone-") as temporary:
            isolated = Path(temporary) / source.name
            isolated.write_bytes(source.read_bytes())
            for mode, flags in [("parse", ["--parse-only"]), ("check", [])]:
                command = [str(executable), str(isolated), "--no-cache", "--diagnostics", "compact", *flags]
                try:
                    process = subprocess.run(command, cwd=temporary, env=env, capture_output=True,
                                             text=True, timeout=30)
                    measured = {"exit": process.returncode, "stdout": process.stdout,
                                "stderr": process.stderr}
                except subprocess.TimeoutExpired as error:
                    measured = {"exit": "timeout", "stdout": str(error.stdout or ""),
                                "stderr": str(error.stderr or "")}
                for stream in ["stdout", "stderr"]:
                    measured[stream] = measured[stream].replace(temporary, "<isolated>")
                result[mode] = measured
        check = result["check"]
        result["matched"] = (
            result["parse"]["exit"] == 0
            and not result["parse"]["stdout"]
            and not result["parse"]["stderr"]
            and check["exit"] == expected_exit
            and not check["stdout"]
            and all(message in check["stderr"] for message in expected)
            and (expected_exit != 0 or not check["stderr"])
            and "panicked at" not in check["stderr"]
        )
        results.append(result)
        print(f"{'PASS' if result['matched'] else 'FAIL'} {case['id']} {source.name}: "
              f"{case['lines']} lines parse={result['parse']['exit']} check={check['exit']}")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"base": catalog["base_sha"],
                                          "cli_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                                          "parent_ids": [item["id"] for item in catalog["items"]],
                                          "max_lines": max(case["lines"] for case in cases),
                                          "results": results}, ensure_ascii=False, indent=2) + "\n")
    print(f"{sum(r['matched'] for r in results)}/{len(results)} cases matched")
    return 0 if results and all(r["matched"] for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
