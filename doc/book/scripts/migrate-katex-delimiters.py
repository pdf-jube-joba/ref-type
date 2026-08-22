#!/usr/bin/env python3
"""Migrate mdbook-katex delimiters in Markdown files.

The script is a dry run unless --write is passed. Fenced code blocks and inline
code spans are left untouched.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from dataclasses import dataclass
from pathlib import Path


FENCE_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")


class MigrationError(ValueError):
    """Raised when a Markdown file contains an unmatched math delimiter."""


@dataclass
class Migration:
    text: str
    inline_count: int = 0
    block_count: int = 0


def is_escaped(text: str, index: int) -> bool:
    backslashes = 0
    index -= 1
    while index >= 0 and text[index] == "\\":
        backslashes += 1
        index -= 1
    return backslashes % 2 == 1


def migrate_text(text: str, source: Path) -> Migration:
    output: list[str] = []
    math: str | None = None
    math_line = 0
    code_ticks: int | None = None
    fence_char: str | None = None
    fence_length = 0
    inline_count = 0
    block_count = 0

    for line_number, line in enumerate(text.splitlines(keepends=True), 1):
        if math is None and code_ticks is None:
            fence = FENCE_RE.match(line)
            if fence:
                marker = fence.group(2)
                if fence_char is None:
                    fence_char = marker[0]
                    fence_length = len(marker)
                elif marker[0] == fence_char and len(marker) >= fence_length:
                    # A closing fence may only be followed by spaces/tabs.
                    if not fence.group(3).strip():
                        fence_char = None
                        fence_length = 0
                output.append(line)
                continue

        if fence_char is not None:
            output.append(line)
            continue

        index = 0
        while index < len(line):
            if math in {"new-inline", "new-block"}:
                closing = r"\)" if math == "new-inline" else r"\]"
                if line.startswith(closing, index) and not is_escaped(line, index):
                    output.append(closing)
                    math = None
                    index += len(closing)
                else:
                    output.append(line[index])
                    index += 1
                continue

            if math is None and line[index] == "`":
                end = index + 1
                while end < len(line) and line[end] == "`":
                    end += 1
                run_length = end - index
                if code_ticks is None:
                    code_ticks = run_length
                elif code_ticks == run_length:
                    code_ticks = None
                output.append(line[index:end])
                index = end
                continue

            if code_ticks is not None:
                output.append(line[index])
                index += 1
                continue

            if (
                math is None
                and line[index] == "\\"
                and not is_escaped(line, index)
                and line[index : index + 2] in {r"\(", r"\["}
            ):
                delimiter = line[index : index + 2]
                math = "new-inline" if delimiter == r"\(" else "new-block"
                math_line = line_number
                output.append(delimiter)
                index += 2
                continue

            if line[index] == "$" and not is_escaped(line, index):
                is_double = line.startswith("$$", index)
                if math is None:
                    math = "old-block" if is_double else "old-inline"
                    math_line = line_number
                    output.append(r"\[" if is_double else r"\(")
                    index += 2 if is_double else 1
                    continue
                if math == "old-block" and is_double:
                    output.append(r"\]")
                    block_count += 1
                    math = None
                    index += 2
                    continue
                if math == "old-inline":
                    output.append(r"\)")
                    inline_count += 1
                    math = None
                    index += 1
                    continue

            output.append(line[index])
            index += 1

    if math is not None:
        delimiter = {
            "old-block": "$$",
            "old-inline": "$",
            "new-block": r"\[",
            "new-inline": r"\(",
        }[math]
        raise MigrationError(
            f"{source}:{math_line}: unmatched {delimiter} math delimiter"
        )
    if code_ticks is not None:
        raise MigrationError(f"{source}: unmatched inline code delimiter")
    if fence_char is not None:
        raise MigrationError(f"{source}: unmatched fenced code block")

    return Migration("".join(output), inline_count, block_count)


def markdown_files(paths: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for path in paths:
        if path.is_dir():
            files.update(
                candidate for candidate in path.rglob("*.md") if candidate.is_file()
            )
        elif path.is_file():
            files.add(path)
        else:
            raise MigrationError(f"path does not exist: {path}")
    return sorted(files)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write", action="store_true", help="replace files in place"
    )
    mode.add_argument(
        "--diff", action="store_true", help="print the proposed unified diff"
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="Markdown files or directories (default: the book's src directory)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    book_dir = Path(__file__).resolve().parent.parent
    paths = args.paths or [book_dir / "src"]

    try:
        files = markdown_files(paths)
        migrations: list[tuple[Path, str, Migration]] = []
        for path in files:
            original = path.read_text(encoding="utf-8")
            migration = migrate_text(original, path)
            if migration.text != original:
                migrations.append((path, original, migration))
    except (MigrationError, OSError, UnicodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if args.diff:
        for path, original, migration in migrations:
            sys.stdout.writelines(
                difflib.unified_diff(
                    original.splitlines(keepends=True),
                    migration.text.splitlines(keepends=True),
                    fromfile=str(path),
                    tofile=str(path),
                )
            )
    elif args.write:
        for path, _original, migration in migrations:
            path.write_text(migration.text, encoding="utf-8")

    inline_count = sum(item.inline_count for _, _, item in migrations)
    block_count = sum(item.block_count for _, _, item in migrations)
    action = "Updated" if args.write else "Would update"
    print(
        f"{action} {len(migrations)} file(s): "
        f"{inline_count} inline and {block_count} block expression(s).",
        file=sys.stderr if args.diff else sys.stdout,
    )
    if not args.write and migrations:
        print(
            "No files were changed; pass --write to apply the migration.",
            file=sys.stderr if args.diff else sys.stdout,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
