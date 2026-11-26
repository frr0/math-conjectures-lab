# math-conjectures-lab

Personal research lab for automated & AI-assisted mathematical conjecture exploration, computational verification (Python), and formal proofs (**Lean 4**).

## Catalogue

| # | Conjecture | Outcome | Verification | Directory |
| :--- | :--- | :--- | :---: | :--- |
| 1 | Euler's sum of powers ($k=5$, calibration) | Disproved (1966 counterexample) | ✅ | [euler-fifth-powers](results/euler-fifth-powers/) |
| 2 | Erdős–Straus conjecture (1948) | Partial ($n \not\equiv 1 \pmod 8$ proved; $n \le 10^5$ checked) | 🟡 | [erdos-straus](results/erdos-straus/) |
| 3 | Brocard's problem (1876) | Partial (last-digit obstruction proved; $n \le 10^3$ checked) | 🟡 | [brocard-problem](results/brocard-problem/) |
| 4 | OEIS A100475 (loop question) | Disproved (no positive start ever loops) | 🟢 | [oeis-a100475](results/oeis-a100475/) |
| 5 | OEIS A189409 (`conjecture_1`: $\mathrm{primorial}(n)^2 + 1$ squarefree) | Disproved ($a(9) \equiv 0 \pmod{29^2}$) | ✅ | [oeis-a189409](results/oeis-a189409/) |
| 6 | OEIS A092243 (`conjecture1`: prime-gap tug-of-war $> 0$ for $n > 250{,}000$) | Proved ($a(261{,}150) = 1 > 0$) | 🟢 | [oeis-a092243](results/oeis-a092243/) |
| 7 | OEIS A108864 (last odd term with perfect deficiency $\le 10$) | Disproved ($m = 815{,}634{,}435$, $\mathrm{pd}(m) = 6$) | ✅ | [oeis-a108864](results/oeis-a108864/) |
| 8 | OEIS A046969 (`conjecture1`: $a(p)/12$ prime for $p > 3$, $2p-1$ prime) | Proved ($a(p) = 12(2p - 1)$) | 🟢 | [oeis-a046969](results/oeis-a046969/) |
| 9 | OEIS A189286 (`conjecture_3`: $a(n)/8$ odd $\iff n = 2^k$) | Proved ($v_2(a(n)) = 3$ iff $n = 2^k$, else $\ge 4$) | ✅ | [oeis-a189286](results/oeis-a189286/) |
| 10 | OEIS A238281 (`conjecture_2`: equal prime counts in adjacent intervals) | Disproved (counterexample at $n = 14, 286$) | 🟢 | [oeis-a238281](results/oeis-a238281/) |

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
