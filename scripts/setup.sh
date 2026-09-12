#!/bin/sh
# Check this machine can build the project, and offer to fix what is missing.
#
#   scripts/setup.sh          check, and prompt before installing anything
#   scripts/setup.sh --check  report only, change nothing (safe for CI)
#
# Safe to re-run any time. Run it after cloning, and after pulling changes that
# touch lean-toolchain or lake-manifest.json.

set -e
cd "$(dirname "$0")/.."

CHECK_ONLY=0
[ "$1" = "--check" ] && CHECK_ONLY=1
MISSING=0

say()  { printf "  %s\n" "$1"; }
ok()   { printf "  ok    %s\n" "$1"; }
bad()  { printf "  MISS  %s\n" "$1"; MISSING=$((MISSING + 1)); }

# Ask before doing anything that installs. Returns 1 if declined or in check mode.
confirm() {
  [ "$CHECK_ONLY" -eq 1 ] && return 1
  printf "        run: %s\n        [y/N] " "$1"
  read -r reply </dev/tty 2>/dev/null || return 1
  case "$reply" in [yY]*) return 0 ;; *) return 1 ;; esac
}

echo "Checking setup for $(basename "$(pwd)")"
echo

# 1. elan — everything else depends on it
if command -v elan >/dev/null 2>&1; then
  ok "elan $(elan --version 2>/dev/null | awk '{print $2}')"
else
  bad "elan not installed"
  say "      macOS: brew install elan-init"
  say "      Linux: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"
  echo; echo "elan is required for everything below. Install it, then re-run."
  exit 1
fi

# 2. the pinned toolchain
WANT=$(cat lean-toolchain)
if elan toolchain list 2>/dev/null | grep -q "^${WANT}$"; then
  ok "toolchain $WANT"
else
  bad "toolchain $WANT not installed"
  if confirm "elan toolchain install $WANT"; then elan toolchain install "$WANT"; fi
fi

# 3. dependencies resolved on disk
if [ -f lake-manifest.json ]; then
  ABSENT=$(python3 - <<'PY'
import json, os
names = [p["name"] for p in json.load(open("lake-manifest.json"))["packages"]]
print(" ".join(n for n in names if not os.path.isdir(f".lake/packages/{n}/.git")))
PY
)
  if [ -z "$ABSENT" ]; then ok "dependencies present"; else bad "not fetched:$ABSENT"; fi
else
  bad "no lake-manifest.json"
fi

# 4. Mathlib build cache — the step people skip
if [ -d .lake/packages/mathlib/.lake/build/lib ]; then
  ok "Mathlib cache present"
else
  bad "Mathlib not built (a source build takes hours; the cache takes minutes)"
  if confirm "lake exe cache get"; then lake exe cache get; fi
fi

# 5. the proofs themselves
if [ "$CHECK_ONLY" -eq 1 ]; then
  say "skip  lake build (--check makes no changes)"
else
  printf "  ....  lake build\n"
  if lake build >/tmp/setup-build.log 2>&1; then
    if grep -q "declaration uses \`sorry\`" /tmp/setup-build.log; then
      bad "build passes but contains 'sorry' — some theorems are unproved"
      grep "declaration uses \`sorry\`" /tmp/setup-build.log | sed 's/^/        /'
    else
      ok "all proofs check"
    fi
  else
    bad "lake build failed"; tail -5 /tmp/setup-build.log | sed 's/^/        /'
  fi
fi

# 6. editor (optional — the repo recommends it via .vscode/extensions.json)
if ls ~/.vscode/extensions 2>/dev/null | grep -qi '^leanprover.lean4'; then
  ok "VS Code lean4 extension"
elif command -v code >/dev/null 2>&1 || [ -d "/Applications/Visual Studio Code.app" ]; then
  bad "VS Code lean4 extension not installed (optional, but Lean is hard to use without it)"
  if confirm "code --install-extension leanprover.lean4"; then
    CODE=$(command -v code || echo "/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code")
    "$CODE" --install-extension leanprover.lean4
  fi
else
  say "n/a   VS Code not found — skipping extension check"
fi

echo
if [ "$MISSING" -eq 0 ]; then
  echo "Ready."
else
  echo "$MISSING item(s) need attention."
  [ "$CHECK_ONLY" -eq 1 ] && echo "Re-run without --check to fix them."
  exit 1
fi
