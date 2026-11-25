import ConjectureLab.EulerFifthPowers
import ConjectureLab.ErdosStraus
import ConjectureLab.BrocardProblem

-- Root module for formally verified conjectures in math-conjectures-lab.
-- Import verified theorem modules here so `lake build` checks them automatically.

namespace ConjectureLab

/-- Sanity check theorem verifying that the Lean 4 toolchain builds cleanly. -/
theorem sanity_check (n : Nat) : n + 0 = n := Nat.add_zero n

end ConjectureLab
