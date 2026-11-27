import Mathlib.Tactic.Ring
import ConjectureLab.OeisA100475
import ConjectureLab.OeisA189409
import ConjectureLab.OeisA092243
import ConjectureLab.OeisA108864
import ConjectureLab.OeisA046969
import ConjectureLab.OeisA189286
import ConjectureLab.OeisA238281
import ConjectureLab.OeisA001481
import ConjectureLab.OeisA004215

-- Root module for formally verified conjectures in math-conjectures-lab.
-- Import verified theorem modules here so `lake build` checks them automatically.

namespace ConjectureLab

/-- Sanity check theorem verifying that the Lean 4 toolchain builds cleanly. -/
theorem sanity_check (n : Nat) : n + 0 = n := Nat.add_zero n

/-- Sanity check theorem verifying that Mathlib tactics are available. -/
theorem sanity_ring (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

end ConjectureLab
