# math-conjectures-lab

Personal research lab for automated & AI-assisted mathematical conjecture exploration, computational verification (Python), and formal proofs (**Lean 4**).

## Catalogue

| # | Conjecture | Outcome | Verification | Directory |
| :--- | :--- | :--- | :---: | :--- |
| 1 | Euler's sum of powers ($k=5$, calibration) | Disproved (1966 counterexample) | ✅ | [euler-fifth-powers](results/euler-fifth-powers/) |

### Verification Legend
- ✅ **Lean-verified**: Complete Lean 4 proof checked with zero `sorry` and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- 🟢 **Computer-assisted / Counterexample verified**: Exact computational proof or counterexample verified by reproducible script (and/or partial Lean).
- 🟡 **Partial Lean**: Partial formalization or intermediate lemmas verified in Lean 4.
- ⬜ **Written only**: Reviewed written proof with no Lean formalization yet.

## Repository Layout

- `infra/` — OpenTofu (Terraform-compatible) Infrastructure as Code managing the GitHub repo, branches, labels, and rulesets.
- `results/<slug>/` — Individual conjecture packages (statement, literature check, `explore.py` / `verify.py`, proof notes).
- `lean/` — Shared Lean 4 formalization workspace (`lake build`).
- `scripts/` — Repository-wide validation and axiom audit scripts run in CI.
- `AGENTS.md` — Operational rules for human/AI research workflows.

## Quick Start

```bash
# Run repository & Python verification checks
python3 scripts/check_repo.py

# Build Lean 4 workspace and audit axioms (requires elan/lake)
bash scripts/verify_lean.sh
```
