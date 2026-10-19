#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../../.."
before_binary=$(realpath -- "${1:?before CLI}")
after_binary=$(realpath -- "${2:?after CLI}")
mkdir -p benchmarks/runs/singular-full-check
comparison_dir=$(mktemp -d benchmarks/runs/singular-full-check/comparison-XXXXXX)

export REF_TYPE_PROFILE_PHASES=1
for variant in before after; do
    if [[ "$variant" == before ]]; then
        checker_binary=$before_binary
    else
        checker_binary=$after_binary
    fi
    for layout in cold learned; do
        python3 benchmarks/bench.py run libs/topology/singular_cohomology \
            --binary "$checker_binary" --cache-mode shared \
            --cache-dir "$comparison_dir/$variant-cache" \
            --runs 1 --seconds 1500 --memory-mib 3072 --output-mib 32 \
            --output "$comparison_dir/$variant-$layout.json" \
            --extra --full-check --cache-stats
    done
done

printf '%s\n' "$comparison_dir"
