#!/usr/bin/env bash
set -eu
# Shared-cache measurements must start with an empty cache.
for version in before after; do
  cache="benchmarks/runs/halving/comparison-${version}-cache"
  if test -e "$cache"; then
    printf '%s\n' "Use a fresh comparison cache: $cache" >&2
    exit 1
  fi
done
destination=benchmarks/runs/halving/comparison
for scenario in off shared cold consumer; do
  for version in before after; do
    binary="benchmarks/runs/halving/${version}-cli"
    cache="benchmarks/runs/halving/comparison-${version}-cache"
    case "$scenario" in
      off) python3 benchmarks/bench.py run libs/std libs/category --binary "$binary" --cache-mode off --runs 3 --output "$destination/$version-$scenario.json" --extra --cache-stats ;;
      shared) python3 benchmarks/bench.py run libs/std --binary "$binary" --cache-mode shared --cache-dir "$cache" --runs 6 --output "$destination/$version-$scenario.json" --extra --cache-stats ;;
      cold) python3 benchmarks/bench.py run libs/std --binary "$binary" --cache-mode cold --runs 3 --output "$destination/$version-$scenario.json" --extra --cache-stats ;;
      consumer) python3 benchmarks/bench.py run libs/category --binary "$binary" --cache-mode shared --cache-dir "$cache" --runs 2 --output "$destination/$version-$scenario.json" --extra --cache-stats ;;
    esac
  done
done
