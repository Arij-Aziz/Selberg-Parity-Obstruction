/-
# ParityBudget.Examples

Worked finite example: P = 6, m = 1, N = 6.

Sanity check that the parity witness and sieve machinery produce
the expected values for a small concrete case.

Status: [NEW-MOEBIUS]
-/
import Mathlib
import RequestProject.Core.ParityBudget.Setup

open Finset BigOperators Nat

noncomputable section

/-- The parity witness on Fin 6 sums to zero. -/
lemma parityWitness_sum_six :
    ∑ x : Fin 6, parityWitness 6 6 x = 0 := by
  unfold parityWitness
  simp only [Fin.sum_univ_succ]
  norm_num
  norm_cast
  native_decide

/-- At coprime elements {1, 5}, parityWitness = 1.
    Target parity correlation = 2 = φ(6) * 1. -/
lemma parityWitness_target_six :
    ∑ x : Fin 6,
      (if Nat.Coprime x.val 6 then (1 : ℝ) else 0) * parityWitness 6 6 x = 2 := by
  unfold parityWitness
  simp only [Fin.sum_univ_succ]
  norm_num

end
