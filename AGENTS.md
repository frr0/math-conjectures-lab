# Research & Verification Protocol (`AGENTS.md`)

## 1. Branch Policy
- **`main`** is the publication branch: only reviewed, verified results (proofs, counterexamples, or clearly labeled partial results) may be merged here via focused PRs.
- **`research`** is the working branch for open investigations, scripts, drafts, and failed attempts.
- Use short-lived branches (`exp/<slug>`) for new targets and open PRs targeting `research` (for work in progress) or `main` (once verified). Never blanket-merge `research` into `main`.

## 2. Mandatory Discovery Workflow
Before claiming a conjecture is resolved, complete every gate in order:

1. **Exact Statement & Literature Check**
   - Record the exact mathematical statement, quantifiers, domain, and primary source (arXiv ID, OEIS ID, paper/book citation).
   - Check that the exact statement is still open (no prior proof or counterexample under another name).
2. **Computational Exploration (Python)**
   - Write `results/<slug>/explore.py` to test small/medium cases and search for counterexamples or structural patterns.
   - If a counterexample is found, write a fast, deterministic `results/<slug>/verify.py` that independently verifies the counterexample without heuristics.
3. **Proof & Independent Audit**
   - Write a complete, self-contained proof in `results/<slug>/README.md` (or `PROOF.md`).
   - Run an adversarial review pass checking edge cases, quantifiers, and hidden assumptions.
4. **Formal Verification (Lean 4)**
   - Formalize the exact theorem statement (never silently weaken hypotheses — *no spec gaming*) under `lean/ConjectureLab/`.
   - No `sorry`, no custom `axiom`, and no untrusted native computation axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
   - Run `bash scripts/verify_lean.sh` and `python3 scripts/check_repo.py` before opening the publication PR.

## 3. Honest Scope Labeling
- Distinguish clearly between: **full resolution**, **counterexample**, **partial theorem**, and **finite computational screen**.
- Never mark a result `✅` in `README.md` unless `scripts/verify_lean.sh` passes cleanly on the exact target theorem.
