#!/bin/sh
# Build the project, then mirror the generated C for Programs/ into build/ as
# readable, formatted source.
#
# Only Programs/ is mirrored. Theorem-only modules compile to ~42 lines of module
# header and nothing else — proofs are erased — so there is nothing to read there.
#
#   scripts/build.sh            build everything, refresh build/
#   scripts/build.sh --no-build just refresh build/ from the current artifacts
#
# Lean emits unindented C into .lake/build/ir/, which it rewrites on every
# build. build/ is a formatted copy for reading; it is derived, and gitignored.

set -e
cd "$(dirname "$0")/.."

[ "$1" = "--no-build" ] || lake build

IR=".lake/build/ir/Programs"
OUT="build/Programs"

[ -d "$IR" ] || { echo "no generated C for Programs/ yet -- run 'lake build' first" >&2; exit 1; }

FMT=$(command -v clang-format || xcrun --find clang-format 2>/dev/null || true)
[ -n "$FMT" ] || echo "clang-format not found; copying unformatted" >&2

rm -rf "$OUT"

n=0
# every .c the project itself generates, across MathTheorems/ and Programs/,
# including the root aggregator modules
find "$IR" -name '*.c' | sort | while :; do read -r f || break
  rel=${f#"$IR"/}                      # e.g. ListMax/Main.c
  src="Programs/${rel%.c}.lean"
  # skip modules whose .lean source is gone (stale artifacts)
  [ -f "$src" ] || continue
  mkdir -p "$OUT/$(dirname "$rel")"
  if [ -n "$FMT" ]; then
    "$FMT" --style='{BasedOnStyle: LLVM, IndentWidth: 2, ColumnLimit: 92}' "$f" > "$OUT/$rel"
  else
    cp "$f" "$OUT/$rel"
  fi
  printf "  %-30s %5s lines\n" "$rel" "$(wc -l < "$OUT/$rel" | tr -d ' ')"
done

echo "-> $OUT/"
