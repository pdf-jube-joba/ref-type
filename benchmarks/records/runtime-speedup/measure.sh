#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.."
before=${1:-benchmarks/runs/speedup/before-cli}
after=${2:-target/release/cli}
output=benchmarks/records/runtime-speedup
mkdir -p benchmarks/runs/speedup
scratch=$(mktemp -d benchmarks/runs/speedup/comparison-XXXXXX)
inputs=(libs/std libs/category libs/algebra/integer_matrices libs/algebra/linear_algebra)

for version in before after; do
    binary=${!version}
    python3 benchmarks/bench.py run "${inputs[@]}" \
        --binary "$binary" --cache-mode off --runs 3 \
        --output "$scratch/$version-off.json"
    python3 benchmarks/bench.py run "${inputs[@]}" \
        --binary "$binary" --cache-mode shared --runs 4 \
        --cache-dir "$scratch/$version-cache" \
        --output "$scratch/$version-shared.json"
    python3 benchmarks/bench.py run libs/std libs/algebra/integer_matrices \
        --binary "$binary" --cache-mode cold --runs 1 \
        --output "$scratch/$version-cold.json"
    cp "$scratch/$version-off.json" "$scratch/$version-shared.json" \
        "$scratch/$version-cold.json" "$output/"
done
