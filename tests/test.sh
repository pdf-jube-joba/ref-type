#!/usr/bin/env bash
set -euo pipefail

# このスクリプト自身が置かれているディレクトリを絶対パスで取得
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# プロジェクトのルート (cargo run を実行したい場所)
PROJECT_DIR="$SCRIPT_DIR/.."

run_cases() {
    local label="$1"
    local dir="$2"
    local expect_fail="$3"

    echo "=== $label cases ==="

    # dir 配下の .ref ファイルを全部再帰的に収集
    mapfile -t files < <(find "$dir" -type f -name '*.ref' | sort)

    if [ ${#files[@]} -eq 0 ]; then
        echo "No .ref files found in $dir"
        return
    fi

    for f in "${files[@]}"; do
        echo "--- running $label: $f"
        if (cd "$PROJECT_DIR" && cargo run -- file "$f"); then
            if [ "$expect_fail" = "true" ]; then
                echo "ERROR: $label case unexpectedly succeeded: $f"
                exit 1
            fi
        else
            if [ "$expect_fail" = "false" ]; then
                echo "ERROR: $label case failed: $f"
                exit 1
            else
                echo "$label case correctly failed: $f"
            fi
        fi
    done
}

run_cases "OK" "$SCRIPT_DIR/ok" "false"
run_cases "NG" "$SCRIPT_DIR/ng" "true"

echo "=== MULTI-FILE cases ==="
(cd "$PROJECT_DIR" && cargo run -- file "$SCRIPT_DIR/projects/multifile/root.ref")

echo "=== LIBRARY case ==="
(cd "$PROJECT_DIR" && cargo run -- file lib/root.ref)

echo "All tests passed 🎉"
