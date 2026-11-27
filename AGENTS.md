# Research & Verification Protocol (`AGENTS.md`)

## 1. Branch Policy
- **`main`** is the publication branch and is protected by a ruleset: changes land only through PRs whose `python-checks` and `lean-checks` CI jobs pass. Only reviewed, verified results (proofs, counterexamples, or clearly labeled partial results) are merged.
- Every target gets a short-lived branch (`exp/<slug>` for conjectures, `chore/<slug>`/`fix/<slug>` for pipeline work). Open investigations, scripts, drafts and failed attempts live there, in a **draft PR** if they need to be pushed before they are ready.

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
   - No `sorry`, no custom `axiom`, and no untrusted native computation axioms (`native_decide`). Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. This is enforced in the kernel by `lean/AxiomAudit.lean`, which audits every declaration under `ConjectureLab.*` (so each module must use `namespace ConjectureLab.<Module>`).
   - Run `python3 scripts/check_repo.py` locally and `bash scripts/verify_lean.sh` (locally if `elan`/`lake` is installed, and always via the `lean-checks` GitHub Actions job before merging).

## 3. Honest Scope Labeling
- Distinguish clearly between: **full resolution**, **counterexample**, **partial theorem**, and **finite computational screen**.
- Never mark a result `✅` in `README.md` unless `scripts/verify_lean.sh` passes cleanly on the exact target theorem.

## 4. Automated GitHub Pipeline
1. Create a short-lived branch `exp/<slug>` from an up-to-date `main`.
2. Open a tracking GitHub Issue for the conjecture or pipeline change (check for duplicates first) and label it:
   - conjectures: `open-target` + `claimed` when work starts (`needs-audit` while a proof/axiom audit is pending);
   - pipeline/docs work: `enhancement` or `documentation`.
3. Implement, run `python3 scripts/check_repo.py` (and `bash scripts/verify_lean.sh` if `lake` is installed), commit with Conventional Commits, push.
4. Open a focused PR targeting `main` with `Closes #<issue>` in the body, then enable auto-merge right away: `gh pr merge --auto --squash --delete-branch`. GitHub merges it once both CI jobs pass and closes the Issue; there is no need to poll CI.
5. Before the merge, set the outcome labels on the Issue and the PR (`gh issue edit <n> --add-label ... --remove-label claimed,needs-audit`): exactly one of `proved` / `counterexample` / `partial-result`, plus `lean-verified` only for a full `✅` Lean formalization.
6. If a check fails, inspect it with `gh run view --log-failed`, fix and push to the same branch (auto-merge stays armed). Afterwards `git checkout main && git pull --prune`.
