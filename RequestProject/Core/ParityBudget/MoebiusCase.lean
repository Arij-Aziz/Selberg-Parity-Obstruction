/-
# ParityBudget.MoebiusCase

Result A: The sorry-free parity budget theorem for Möbius weights.

Status: [NEW-MOEBIUS]
-/
import Mathlib
import RequestProject.Core.ParityBudget.AbstractBudget
import RequestProject.Core.ParityBudget.FiniteParityProxy
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.L2Identity

open Finset BigOperators Nat

noncomputable section

/-
**Theorem 5.1 — parity_budget_moebius**

If the majorant suppresses the parity witness to at most zero
while the coprime target has parity correlation φ(P) * m > 0, then
  (Nat.totient P) * m ≤ (P * m) * Q(λ).

Equivalently, Q(λ) ≥ φ(P)/P, which is exactly the Möbius baseline.
-/
theorem parity_budget_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0)
    (hparity_sep :
      ∑ x : Fin (P * m),
        selbergNu (P * m) P lambda x * parityWitness P (P * m) x ≤ 0) :
    (Nat.totient P : ℝ) * m ≤
      (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  have := @multiPrimeQuadForm_lower_bound' P hP hP_pos lambda hlam_one hsupp; rw [ div_le_iff₀ ] at this <;> nlinarith [ ( by positivity : 0 < ( P : ℝ ) * m ) ] ;

/-
**Theorem 5.2 — parity_separating_weights_cost_more_than_moebius**

Parity-separating weights have a quadratic form at least as large as the
Möbius weights. This follows from `multiPrimeQuadForm_lower_bound'`.
-/
theorem parity_separating_weights_cost_more_than_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (moebiusWeights P) ≤
      multiPrimeQuadForm P lambda := by
  convert moebius_quadForm_eq P hP hP_pos ▸ multiPrimeQuadForm_lower_bound' P hP hP_pos lambda hlam_one hsupp using 1

end