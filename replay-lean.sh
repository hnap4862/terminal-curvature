#!/usr/bin/env bash
set -euo pipefail

# Usage: ./replay-lean.sh /path/to/lean-4.19.0/bin/lean /path/to/mathlib4
# The mathlib checkout and its dependencies need compiled oleans.
lean_bin="$(realpath "$1")"
mathlib_dir="$(realpath "$2")"
cd "$(dirname "$0")"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build:$mathlib_dir/.lake/build/lib/lean"
for pkg in "$mathlib_dir"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$pkg" ]]; then LEAN_PATH="$LEAN_PATH:$pkg"; fi
done
"$lean_bin" --version
modules=(TerminalCurvature Word Counting Assembly Family Geometry Bounds Limits RealLimits ExplicitTree Audit)
if grep -nE '^[[:space:]]*(axiom|constant|opaque)[[:space:]]|(^|[^[:alnum:]_])(sorry|admit|native_decide|sorryAx)([^[:alnum:]_]|$)' "${modules[@]/%/.lean}"; then
  echo "Review proof-hole tokens above (including any comments)."
fi
for module in "${modules[@]}"; do
  echo "Compiling $module.lean"
  "$lean_bin" -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
echo "PASS: eleven modules, fresh local build"
