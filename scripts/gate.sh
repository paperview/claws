#!/bin/bash
# The claws gate for one project: translate its C++ to Lean, check every
# law, compare the translation against the compiled C++ on generated
# inputs, then compile the C++ with stock clang. Exits nonzero on any
# failure.
#
#   scripts/gate.sh examples/Clamp
#
# A project directory holds code.hpp (the claws subset), main.cpp (the
# driver, outside the subset), LAWS.lean, PROOF.lean and Verdict.lean. Its
# name is its Lean namespace and must have a lean_lib in lakefile.toml.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
dir=$(cd "$1" && pwd)
name=$(basename "$dir")
export PATH="$HOME/.elan/bin:$PATH"

echo "== build claws-lean"
if [ ! -f "$root/build/build.ninja" ]; then
  # The LLVM whose Clang libraries the tools link: $LLVM_PREFIX if set,
  # else Homebrew's, else the one llvm-config reports.
  llvm=${LLVM_PREFIX:-}
  if [ -z "$llvm" ] && [ -d /opt/homebrew/opt/llvm ]; then
    llvm=/opt/homebrew/opt/llvm
  elif [ -z "$llvm" ] && command -v llvm-config >/dev/null; then
    llvm=$(llvm-config --prefix)
  fi
  cmake -S "$root" -B "$root/build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
    ${llvm:+-DCMAKE_PREFIX_PATH="$llvm"} >/dev/null
fi
ninja -C "$root/build" >/dev/null

echo "== translate $name/code.hpp"
"$root/build/tools/claws-lean/claws-lean" "$dir/code.hpp" \
  --namespace "$name.Code" -o "$dir/Code.lean" --

echo "== print $name/code.hpp as the semantics sees it"
"$root/build/tools/claws-ast/claws-ast" "$dir/code.hpp" --project "$name" -o "$dir/Ast.lean" --

echo "== check laws"
status=0
out=$(cd "$root" && lake build "$name.Verdict" 2>&1) || status=$?
printf '%s\n' "$out" | grep -v -e '^trace:' -e '^✔' || true
if [ "$status" -ne 0 ]; then
  echo "== the laws do not hold (see above): not compiling"
  exit 1
fi

echo "== differential test"
# The proofs are about the Lean translation; this checks the translation
# against the compiled C++ on generated inputs.
"$root/scripts/diff.sh" "$dir" 100

echo "== compile with stock clang"
mkdir -p "$root/build/bin"
clang++ -std=c++20 -Wall -Wextra -Werror -O2 -I "$root/include" "$dir/main.cpp" -o "$root/build/bin/$name"
"$root/build/bin/$name"
