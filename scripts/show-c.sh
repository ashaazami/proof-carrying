#!/bin/sh
# Show the C that Lean generated for a module, formatted and readable.
#
#   scripts/show-c.sh Programs.ListMax.ListMax
#
# The generated C lives in .lake/build/ir/ and is rewritten on every build,
# so this formats a copy rather than editing it in place.

set -e
MOD="${1:?usage: scripts/show-c.sh <Module.Name>   e.g. Programs.ListMax.ListMax}"
SRC=".lake/build/ir/$(printf '%s' "$MOD" | tr '.' '/').c"

[ -f "$SRC" ] || { echo "no C for $MOD -- run 'lake build' first ($SRC)" >&2; exit 1; }

FMT=$(command -v clang-format || xcrun --find clang-format 2>/dev/null || true)
if [ -n "$FMT" ]; then
  "$FMT" --style='{BasedOnStyle: LLVM, IndentWidth: 2, ColumnLimit: 92}' "$SRC"
else
  echo "// clang-format not found; showing unformatted" >&2
  cat "$SRC"
fi
