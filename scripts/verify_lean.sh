#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$ROOT_DIR/lean"

if ! command -v lake >/dev/null 2>&1; then
  echo "Error: 'lake' (Lean 4) is not installed. Install via elan: https://lean-lang.org/lean4/doc/setup.html" >&2
  exit 1
fi

echo "[lean] Building workspace in $LEAN_DIR ..."
(cd "$LEAN_DIR" && lake build)

echo "[lean] Auditing axioms of every ConjectureLab declaration ..."
(cd "$LEAN_DIR" && lake env lean AxiomAudit.lean)

echo "[lean] Verification succeeded."
