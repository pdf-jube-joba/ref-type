#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$SCRIPT_DIR/../.."

cd "$PROJECT_DIR"
cargo run --quiet -- file tests/reals/dedekind.ref >/dev/null
cargo run --quiet -- file tests/reals/cauchy.ref >/dev/null
