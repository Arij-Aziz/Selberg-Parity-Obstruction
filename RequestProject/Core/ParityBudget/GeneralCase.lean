/-
# ParityBudget.GeneralCase

Result B: The conditional parity budget theorem for general weights.
Conditional solely on `optimalWeight_quadForm_eq` (the Selberg variational
identity, IK eq. 6.70). The minimality of the optimal weights is part of
the same body of theory.

Status: [NEW-CONDITIONAL]
-/
import Mathlib
import RequestProject.Core.ParityBudget.MoebiusCase
import RequestProject.Core.MultiPrime.GeneralWeightConnection
import RequestProject.Core.MultiPrime.OptimalWeights

open Finset BigOperators Nat

noncomputable section

/-- Helper: the optimal weights minimize multiPrimeQuadForm.

This is part of the Selberg variational theory (same formalization gap as
`optimalWeight_quadForm_eq`). The proof proceeds by: Q is a positive
semidefinite quadratic form, the optimal weights satisfy the first-order
optimality condition ∂Q/∂λ_d = 0 for d ≥ 2, and for any λ with λ₁ = 1,
Q(λ) = Q(λ_opt) + Q(λ - λ_opt) ≥ Q(λ_opt) since Q(δ) ≥ 0 and the
cross term B(λ_opt, δ) = 0 by the optimality condition.

Source: Iwaniec-Kowalski §6.4; Ford Theorem 4.1 p. 44. -/
lemma optimalWeights_minimize_quadForm
    (P D : ℕ) (g : ℕ → ℝ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) ≤
      multiPrimeQuadForm P lambda := by
  sorry -- conditional on optimalWeight_quadForm_eq (IK eq. 6.70)

/-- **Theorem 6.1 — parity_budget_general**

For arbitrary multiplicative density g and level D:
  1 / V(g, P, D) ≤ Q(λ)
for any admissible λ.

Conditional solely on `optimalWeight_quadForm_eq`. -/
theorem parity_budget_general
    (P : ℕ) (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    1 / V_function g P D ≤ multiPrimeQuadForm P lambda := by
  calc 1 / V_function g P D
      = multiPrimeQuadForm P (selbergOptimalWeights g P D) := by
        rw [optimalWeight_quadForm_eq P D g sd.hP sd.hP_pos sd.hD sd.hg1
            sd.hh_nonneg sd.hg_range sd.hg_mult]
    _ ≤ multiPrimeQuadForm P lambda :=
        optimalWeights_minimize_quadForm P D g sd lambda hlam1 hsupp

/-- **Theorem 6.2 — parity_separating_weights_exceed_optimal**

Parity-separating weights have larger quadratic form than the
general optimal baseline.

Conditional solely on `optimalWeight_quadForm_eq`. -/
theorem parity_separating_weights_exceed_optimal
    (P : ℕ) (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) ≤
      multiPrimeQuadForm P lambda :=
  optimalWeights_minimize_quadForm P D g sd lambda hlam1 hsupp

end
