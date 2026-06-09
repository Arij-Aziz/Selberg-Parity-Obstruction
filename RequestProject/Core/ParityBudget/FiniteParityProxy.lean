/-
# ParityBudget.FiniteParityProxy

Properties of the finite parity witness χ(x) = μ(gcd(x, P)).

Status: [NEW-ABSTRACT] / [NEW-MOEBIUS]
-/
import Mathlib
import RequestProject.Core.ParityBudget.Setup
import RequestProject.Core.MultiPrime.MoebiusWeights

open Finset BigOperators Nat

noncomputable section

/-
**Property 4.1**: The parity witness is bounded: |χ(x)| ≤ 1.
    Möbius function takes values in {-1, 0, 1}.
-/
lemma parityWitness_bounded (P N : ℕ) (x : Fin N) :
    |parityWitness P N x| ≤ 1 := by
  unfold parityWitness;
  norm_num [ ArithmeticFunction.moebius ];
  split_ifs <;> norm_num

/-
**Property 4.2**: At coprime elements, parityWitness = 1.
    When gcd(x, P) = 1, μ(1) = 1.
-/
lemma parityWitness_coprime_eq_one (P N : ℕ) (x : Fin N)
    (hcop : Nat.Coprime x.val P) :
    parityWitness P N x = 1 := by
  unfold parityWitness; simp_all +decide [ Nat.Coprime, Nat.gcd_eq_left_iff_dvd ] ;

/-
**Property 4.3**: Target parity correlation.
    Σ_{x coprime to P} parityWitness(x) = φ(P) * m.
-/
lemma parityWitness_target_correlation (P m : ℕ) (hP_pos : 0 < P) :
    ∑ x : Fin (P * m),
      (if Nat.Coprime x.val P then (1 : ℝ) else 0) * parityWitness P (P * m) x =
    (Nat.totient P : ℝ) * m := by
  have h_sum_coprime : ∑ x : Fin (P * m), (if Nat.Coprime x.val P then 1 else 0) = Nat.totient P * m := by
    have h_sum_coprime : ∑ x ∈ Finset.range (P * m), (if Nat.Coprime x P then 1 else 0) = Nat.totient P * m := by
      induction' m with m ih;
      · norm_num;
      · rw [ Nat.mul_succ, Finset.sum_range_add, ih ];
        simp +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, mul_add ];
        congr 1 with x ; simp +decide [ Nat.coprime_comm ];
    rw [ ← h_sum_coprime, Finset.sum_range ];
  convert congr_arg ( ( ↑ ) : ℕ → ℝ ) h_sum_coprime using 1;
  · norm_num [ parityWitness ];
    rw_mod_cast [ Finset.card_filter ];
    push_cast; congr; ext; aesop;
  · norm_cast

end