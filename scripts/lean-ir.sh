#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/lean-ir.sh <Module.Name> [symbol]

Examples:
  scripts/lean-ir.sh SciLean.Data.DataArray.Random l_SciLean_DataArrayN_rand
  scripts/lean-ir.sh examples.RandBenchmark

What it does:
  1) Builds the module with `lake build`
  2) Prints the path to the generated C backend output under `.lake/build/ir/`
  3) Optionally `rg`s for a symbol in that `.c` file
  4) Prints handy commands for dumping Lean compiler traces (LCNF, specialize, inlining)
EOF
}

if [[ $# -lt 1 ]]; then
  usage
  exit 2
fi

mod="$1"
sym="${2:-}"

mod_path="${mod//.//}"
src_file="${mod_path}.lean"
ir_c=".lake/build/ir/${mod_path}.c"

echo "[lean-ir] Building ${mod} …"
lake build "${mod}"

echo "[lean-ir] Source: ${src_file}"
if [[ -f "${ir_c}" ]]; then
  echo "[lean-ir] C backend output: ${ir_c}"
else
  echo "[lean-ir] WARNING: expected C file not found at ${ir_c}"
  echo "[lean-ir]          try looking under: .lake/build/ir/"
fi

if [[ -n "${sym}" && -f "${ir_c}" ]]; then
  echo "[lean-ir] Searching for symbol: ${sym}"
  rg -n --fixed-strings "${sym}" "${ir_c}" || true
fi

echo ""
echo "[lean-ir] Compiler tracing (prints to stderr, can be huge):"
echo "  lake env lean --root . -Dtrace.Compiler.result=true ${src_file} 2> /tmp/lean-trace.log"
echo "  lake env lean --root . -Dtrace.Compiler.specialize=true ${src_file} 2> /tmp/lean-trace.log"
echo "  lake env lean --root . -Dtrace.Compiler.simp.inline=true ${src_file} 2> /tmp/lean-trace.log"
echo ""
echo "[lean-ir] Notes:"
echo '  - `@[inline]` / `@[always_inline]` / `@[macro_inline]` live in ~/lean4/src/Lean/Compiler/InlineAttrs.lean'
echo '  - trace classes are in ~/lean4/src/Lean/Compiler/LCNF/* (e.g. Main.lean, Specialize.lean, Simp.lean)'
