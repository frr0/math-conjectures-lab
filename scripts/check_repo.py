#!/usr/bin/env python3
"""Repository-wide integrity and verifier runner for math-conjectures-lab."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = ROOT / "results"
LEAN_DIR = ROOT / "lean"


def check_results() -> list[str]:
    errors: list[str] = []
    if not RESULTS_DIR.exists():
        return ["Missing results/ directory"]

    for entry in sorted(RESULTS_DIR.iterdir()):
        if not entry.is_dir() or entry.name.startswith(".") or entry.name == "TEMPLATE":
            continue

        readme = entry / "README.md"
        if not readme.exists():
            errors.append(f"{entry.relative_to(ROOT)}: missing README.md")

        verifier = entry / "verify.py"
        if verifier.exists():
            print(f"[verify] Running {verifier.relative_to(ROOT)} ...")
            proc = subprocess.run(
                [sys.executable, str(verifier)],
                cwd=entry,
                capture_output=True,
                text=True,
            )
            if proc.returncode != 0:
                errors.append(
                    f"{verifier.relative_to(ROOT)} failed (exit {proc.returncode}):\n"
                    f"{proc.stdout}\n{proc.stderr}"
                )
            else:
                print(f"[ok] {verifier.relative_to(ROOT)}")

    return errors


def check_lean_sources() -> list[str]:
    errors: list[str] = []
    if not LEAN_DIR.exists():
        return errors

    root_lean = LEAN_DIR / "ConjectureLab.lean"
    root_imports = root_lean.read_text(encoding="utf-8") if root_lean.exists() else ""

    for lean_file in sorted(LEAN_DIR.rglob("*.lean")):
        if ".lake" in lean_file.parts:
            continue
        if lean_file.parent.name == "ConjectureLab":
            mod_name = f"ConjectureLab.{lean_file.stem}"
            if f"import {mod_name}" not in root_imports:
                errors.append(
                    f"{lean_file.relative_to(ROOT)}: not imported in lean/ConjectureLab.lean"
                )
        text = lean_file.read_text(encoding="utf-8")
        for lineno, line in enumerate(text.splitlines(), start=1):
            stripped = line.split("--", 1)[0]
            if "sorry" in stripped.split():
                errors.append(f"{lean_file.relative_to(ROOT)}:{lineno}: contains 'sorry'")
            if stripped.lstrip().startswith("axiom "):
                errors.append(f"{lean_file.relative_to(ROOT)}:{lineno}: declares custom 'axiom'")
    return errors


def main() -> int:
    errors = []
    errors.extend(check_results())
    errors.extend(check_lean_sources())

    if errors:
        print("\nRepository verification FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print("All repository checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
