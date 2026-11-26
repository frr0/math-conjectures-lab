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
   - Every conjecture published to `main` **must** have a Lean 4 module under `lean/ConjectureLab/` imported in `lean/ConjectureLab.lean` (full theorem formalization for `✅`, or core structural lemmas / exact witness checks for `🟢` / `🟡`).
   - Never silently weaken hypotheses (*no spec gaming*) when claiming a full formalization (`✅`).
   - No `sorry`, no custom `axiom`, and no untrusted native computation axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
   - Run `python3 scripts/check_repo.py` locally and `bash scripts/verify_lean.sh` (locally if `elan`/`lake` is installed, and always via the `lean-checks` GitHub Actions job before merging).

## 3. Honest Scope Labeling
- Distinguish clearly between: **full resolution**, **counterexample**, **partial theorem**, and **finite computational screen**.
- Never mark a result `✅` in `README.md` unless `scripts/verify_lean.sh` passes cleanly on the exact target theorem.

## 4. Automated GitHub Pipeline
1. Create a short-lived branch `exp/<slug>` from `main`.
2. Open a tracking GitHub Issue for the conjecture or pipeline change.
3. Open a focused PR from `exp/<slug>` targeting `main` and wait for both `python-checks` and `lean-checks` CI jobs to pass.
4. Squash-merge the PR (`gh pr merge --squash --delete-branch`), close the Issue, pull `main`, and keep `research` synced with `main` (`0 ahead / 0 behind`).
