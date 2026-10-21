#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../../.."
binary=$(realpath "${1:-target/debug/cli}")
mkdir -p benchmarks/runs/cohomology-examples-full-check
results=$(mktemp -d benchmarks/runs/cohomology-examples-full-check/reproduce-XXXXXX)
input=libs/topology/examples/finite_models

for memory in 3072 8192; do
    REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_PHASES=1 \
        python3 benchmarks/bench.py run "$input" --binary "$binary" \
        --runs 1 --cache-mode shared --cache-dir "$results/cache-$memory" \
        --seconds "${FULL_SECONDS:-600}" --memory-mib "$memory" --batch-seconds 180 \
        --output-mib 32 --output "$results/full-$memory.json" \
        --extra --full-check --cache-stats || test "$?" -eq 1
    python3 benchmarks/records/cohomology-examples-full-check/summarize.py \
        "$results/full-$memory.json" > "$results/full-$memory-progress.json"
done

python3 benchmarks/bench.py run "$input" --binary "$binary" \
    --runs 3 --cache-mode off --seconds 180 --memory-mib 8192 \
    --module cohomology_examples.Graph.On.With --output "$results/graph.json" \
    --extra --module-only

python3 benchmarks/bench.py run "$input" --binary "$binary" \
    --runs 1 --cache-mode off --seconds 180 --memory-mib 8192 \
    --profile-costs --profile-phases --module cohomology_examples.Graph.On.With \
    --output "$results/graph-profile.json" --extra --module-only

for name in chains torus; do
    if [ "$name" = chains ]; then
        module=singular_excision.MayerVietoris.Over.On.Chains
    else
        module=cohomology_examples.Torus.Geometry.Ring.Primitive
    fi
    python3 benchmarks/bench.py run "$input" --binary "$binary" \
        --runs 1 --cache-mode off --seconds 180 --memory-mib 8192 \
        --module "$module" --output "$results/$name.json" --extra --module-only
    REF_TYPE_PROFILE_COSTS_PROGRESS_MS=15000 \
        python3 benchmarks/bench.py run "$input" --binary "$binary" \
        --runs 1 --cache-mode off --seconds 180 --memory-mib 8192 \
        --profile-costs --profile-phases --module "$module" \
        --output "$results/$name-profile.json" --extra --module-only
done

printf '%s\n' "$results"
