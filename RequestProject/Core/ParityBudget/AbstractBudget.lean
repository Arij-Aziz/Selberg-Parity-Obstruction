/-
# ParityBudget.AbstractBudget

Abstract signed-witness framework for the parity budget theorem.
No Selberg specifics — only the abstract `Majorant` interface.

Status: [NEW-ABSTRACT]
-/
import Mathlib
import RequestProject.Core.Majorant
import RequestProject.Core.RestrictionLowerBound

open Finset BigOperators

noncomputable section

namespace Majorant

variable {N : ℕ} (M : Majorant N)

/-
**Lemma 3.1**: Target correlation ≤ majorant correlation + surplus.

If χ is a signed witness with |χ x| ≤ 1 for all x, then
  Σ target(x) · χ(x) ≤ Σ ν(x) · χ(x) + (mass - targetMass).

Proof: Σ T·χ = Σ ν·χ - Σ (ν-T)·χ ≤ Σ ν·χ + Σ |ν-T|.
Since ν ≥ T ≥ 0 and |χ| ≤ 1, Σ |ν-T| = Σ(ν-T) = mass - targetMass.
-/
lemma target_correlation_le_majorant_correlation_plus_surplus
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1) :
    ∑ x, M.target x * χ x ≤
      ∑ x, M.nu x * χ x + (M.mass - M.targetMass) := by
  -- By definition of mass and target mass, we can rewrite the inequality as follows:
  have h_rewrite : ∑ x, (M.nu x - M.target x) * χ x ≥ -∑ x, (M.nu x - M.target x) := by
    rw [ ← Finset.sum_neg_distrib ];
    exact Finset.sum_le_sum fun x _ => by nlinarith [ abs_le.mp ( hbound x ), M.domination x, M.nu_nonneg x, M.target_nonneg x ] ;
  simp_all +decide [ sub_mul ];
  linarith! [ M.mass, M.targetMass ]

/-
**Lemma 3.2**: Parity separation implies surplus.

If the target has parity correlation ≥ α but the majorant has
correlation ≤ β, then α - β ≤ mass - targetMass.
-/
lemma parity_separation_implies_surplus
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β) :
    α - β ≤ M.mass - M.targetMass := by
  linarith [ target_correlation_le_majorant_correlation_plus_surplus M χ hbound ]

/-
**Lemma 3.3**: Budget from parity separation.

Combine with mass_ge_targetMass to get a lower bound on mass:
  targetMass + (α - β) ≤ mass.
-/
lemma budget_from_parity_separation
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β)
    (hα : 0 < α - β) :
    M.targetMass + (α - β) ≤ M.mass := by
  linarith [ parity_separation_implies_surplus M χ hbound htarget hmajor ]

/-
**Lemma 3.4**: Energy budget from parity separation.

Combine with restriction_lower_bound:
  (targetMass + (α - β))² · l2NormSq ≥ targetMass⁴ / N.
-/
lemma energy_budget_from_parity_separation
    (hN : (0 : ℝ) < N) (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β)
    (hα : 0 < α - β) :
    (M.targetMass + (α - β)) ^ 2 * M.l2NormSq ≥ M.targetMass ^ 4 / N := by
  refine' le_trans ( le_of_eq _ ) _;
  exact M.targetMass ^ 4 / N;
  · rfl;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show M.l2NormSq ≥ M.targetMass ^ 2 / N from _ ) <| by positivity );
    · convert mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by linarith [ show 0 ≤ M.targetMass from Finset.sum_nonneg fun _ _ => M.target_nonneg _ ] ) ( show M.targetMass ≤ M.targetMass + ( α - β ) by linarith ) 2 ) ( show ( 0 : ℝ ) ≤ M.targetMass ^ 2 / N by positivity ) using 1 ; ring;
    · have := fin_cauchy_schwarz ( fun x => M.target x );
      rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast at *;
      exact this.trans ( by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( Finset.sum_le_sum fun _ _ => pow_le_pow_left₀ ( M.target_nonneg _ ) ( M.domination _ ) _ ) ( Nat.cast_nonneg _ ) )

end Majorant

end