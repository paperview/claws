#!/bin/bash
# Differential test of one project: run every function in its code.hpp on
# the same generated inputs, once compiled as C++ and once evaluated from
# its Lean translation, and compare the results line by line. A line that
# differs is a bug in the translation, which every proof relies on.
#
#   scripts/diff.sh examples/Clamp [cases per function] [seed]
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
dir=$(cd "$1" && pwd)
name=$(basename "$dir")
cases=${2:-200}
seed=${3:-1}
out="$root/build/diff/$name"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$out"

ninja -C "$root/build" >/dev/null
"$root/build/tools/claws-lean/claws-lean" "$dir/code.hpp" --namespace "$name.Code" \
  --diff-cpp "$out/Diff.cpp" --diff-lean "$out/Diff.lean" \
  --diff-cases "$cases" --diff-seed "$seed" --
clang++ -std=c++20 -O1 -w -I "$root/include" "$out/Diff.cpp" -o "$out/diff"
"$out/diff" > "$out/cpp.txt"
lean --run "$out/Diff.lean" > "$out/lean.txt"

ran=$(grep -vc ' skip$' "$out/cpp.txt" || true)
skipped=$(grep -c ' skip$' "$out/cpp.txt" || true)
if diff "$out/cpp.txt" "$out/lean.txt" > "$out/diff.txt"; then
  echo "C++ and Lean agree on $ran cases ($skipped skipped by preconditions, seed $seed)"
else
  echo "C++ and Lean DISAGREE (seed $seed); first differences, C++ (<) then Lean (>):"
  head -20 "$out/diff.txt"
  echo "full outputs: $out/cpp.txt and $out/lean.txt"
  exit 1
fi
