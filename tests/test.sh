#!/usr/bin/env bash
set -euo pipefail

# このスクリプト自身が置かれているディレクトリを絶対パスで取得
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# プロジェクトのルート (cargo run を実行したい場所)
# もしこの test.sh と Cargo.toml が同じリポジトリ内のどこかにあって、
# "cargo run" をどこでやるべきかが明確なら、そこに合わせてください。
# ここではとりあえず SCRIPT_DIR の親に Cargo.toml がある想定にする:
PROJECT_DIR="$SCRIPT_DIR/.."

echo "=== OK cases ==="
for f in "$SCRIPT_DIR/ok"/*.txt; do
    echo "--- running OK: $f"
    (cd "$PROJECT_DIR" && cargo run -- "$f") || {
        echo "ERROR: OK case failed: $f"
        exit 1
    }
done

echo "=== NG cases ==="
for f in "$SCRIPT_DIR/ng"/*.txt; do
    echo "--- running NG: $f"
    if (cd "$PROJECT_DIR" && cargo run -- "$f"); then
        echo "ERROR: NG case unexpectedly succeeded: $f"
        exit 1
    else
        echo "NG case correctly failed: $f"
    fi
done

echo "All tests passed 🎉"
