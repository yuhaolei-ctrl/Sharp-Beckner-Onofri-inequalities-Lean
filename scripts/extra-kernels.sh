#!/usr/bin/env bash
set -euo pipefail

# Replay the 28 theorems of comparator.json in two further independent kernels bundled with the
# toolchain, con-leche and Lean4Lean (Comparator itself runs Lean's kernel, NanoDa and con-ron).
# All declarations the theorems depend on are exported once with leanexport and checked by both.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

prefix=$(lean --print-prefix)
work=$(mktemp -d "${TMPDIR:-/tmp}/extra-kernels.XXXXXX")
module=BecknerOnofri/ExtraKernelsExport.lean
trap 'rm -rf "$work" "$module"' EXIT

# leanexport takes one root name, so collect the theorems in one auxiliary declaration.
{
  echo "module"
  echo "public import Solution"
  echo "@[expose] public section"
  echo "theorem extraKernelsRoot : True := by"
  python3 -c 'import json; [print(f"  have := @{n}") for n in json.load(open("comparator.json"))["theorem_names"]]'
  echo "  trivial"
} > "$module"

lake build BecknerOnofri.ExtraKernelsExport
lake env leanexport BecknerOnofri.ExtraKernelsExport -- extraKernelsRoot > "$work/export.ndjson"

echo "== con-leche"
"$prefix/bin/con-leche" --jobs="${JOBS:-4}" "$work/export.ndjson"
echo "== Lean4Lean"
"$prefix/bin/lean4lean" --import "$work/export.ndjson" | tail -1
