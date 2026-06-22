/-
  Challenge.lean
  ==============
  Auditable statement file for the Selberg Majorant: Parity Budget Extension.

  ── HOW TO USE ──────────────────────────────────────────────────────────────
  This file has ONE import: `import Mathlib`.
  No `RequestProject.*` imports appear anywhere.

  Every theorem is stated with its verbatim signature from the source file,
  with `sorry` as the proof body. All project-internal definitions are
  reproduced inline below using only Mathlib primitives, so a reviewer can
  verify every statement is well-typed without building the project.

  To check: `lake build Challenge`
  Expected: zero errors; only `declaration uses sorry` warnings (intended).

  ── CONTENTS ─────────────────────────────────────────────────────────────────
  §0.  Inline definitions (Mathlib-only reproductions)
  §1.  Möbius Weights                                     (5 theorems)
  §2.  Parity Budget — Abstract Framework                  (4 theorems)
  §3.  Parity Witness Properties                           (3 theorems)
  §4.  Parity Budget — Möbius Case (Result A)              (2 theorems)
  §5.  Parity Budget — Concrete Examples                   (2 theorems)
  §6.  Parity Budget — General Case (Result B)             (3 theorems)

  Total: 19 theorems (matching Audit.lean theorem list exactly).
  Axiom footprint for each when sorry-free: [propext, Classical.choice, Quot.sound].
  ─────────────────────────────────────────────────────────────────────────────
-/
import Mathlib

open Finset BigOperators Complex ArithmeticFunction

noncomputable section

-- ════════════════════════════════════════════════════════════════════════════
-- §0.  Inline definitions (Mathlib primitives only)
-- ════════════════════════════════════════════════════════════════════════════

-- ── Sieve infrastructure ───────────────────────────────────────────────────

/-- Squarefree divisors of a natural number n. -/
def squarefreeDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter Squarefree

/-- Squarefree divisors of P (abbreviated for convenience). -/
def sqfDivisors (P : ℕ) : Finset ℕ :=
  squarefreeDivisors P

/-- The multi-prime Selberg majorant:
    ν(x) = (Σ_{d ∈ sqfDivisors P, d | gcd(x,P)} λ_d)² -/
def selbergNu (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) : ℝ :=
  (∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P), lambda d) ^ 2

/-- The multi-prime quadratic form:
    Q(λ) = Σ_{d,e ∈ sqfDivisors P} λ_d · λ_e / lcm(d,e) -/
def multiPrimeQuadForm (P : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    lambda d * lambda e / (Nat.lcm d e : ℝ)

-- ── Majorant structure ────────────────────────────────────────────────────

/-- An abstract majorant for a target indicator function on a finite set. -/
structure Majorant (N : ℕ) where
  nu         : Fin N → ℝ
  target     : Fin N → ℝ
  nu_nonneg      : ∀ x, 0 ≤ nu x
  target_nonneg  : ∀ x, 0 ≤ target x
  target_indicator : ∀ x, target x = 0 ∨ target x = 1
  domination : ∀ x, target x ≤ nu x

namespace Majorant
variable {N : ℕ} (M : Majorant N)

/-- The mass (L¹ norm) of the majorant: Σ_x ν(x) -/
def mass : ℝ := ∑ x : Fin N, M.nu x

/-- The mass of the target: Σ_x target(x) -/
def targetMass : ℝ := ∑ x : Fin N, M.target x

/-- The L² norm squared of the majorant: Σ_x ν(x)² -/
def l2NormSq : ℝ := ∑ x : Fin N, M.nu x ^ 2

end Majorant

-- ── Parity witness ────────────────────────────────────────────────────────

/-- The parity witness on Fin N:
    χ(x) = μ(gcd(x, P)), the Möbius function of the gcd with P.
    For squarefree P, this takes values in {-1, +1, 0}, being +1 when
    gcd(x, P) has an even number of prime factors and -1 when odd. -/
def parityWitness (P : ℕ) (N : ℕ) (x : Fin N) : ℝ :=
  (ArithmeticFunction.moebius (Nat.gcd x.val P) : ℝ)

-- ── Möbius weights ────────────────────────────────────────────────────────

/-- The Möbius weights restricted to squarefree divisors of P:
    μ_P(d) = μ(d) if d is a squarefree divisor of P, else 0. -/
def moebiusWeights (P : ℕ) (d : ℕ) : ℝ :=
  if d ∈ sqfDivisors P then (ArithmeticFunction.moebius d : ℝ) else 0

-- ── Optimal weights infrastructure ─────────────────────────────────────────

/-- The multiplicative function h(d) = g(d) / ∏_{p ∈ primeFactors(d)} (1 − g(p)).
    For squarefree d with multiplicative g, this equals ∏_{p|d} g(p)/(1-g(p)). -/
def hFunction (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  g d / ∏ p ∈ d.primeFactors, (1 - g p)

/-- V(g, P, D) = Σ_{d ∈ sqfDivisors P, d ≤ D} h(d).
    This is the reciprocal sum that appears in the Selberg upper bound. -/
def V_function (g : ℕ → ℝ) (P D : ℕ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D), hFunction g d

/-- Optimal Selberg weights: λ_d = μ(d) · V(D/d) / V(D).
    These minimize the quadratic form Q(λ) subject to λ₁ = 1,
    when defined on the support {d ∈ sqfDivisors P : d ≤ D}. -/
def selbergOptimalWeights (g : ℕ → ℝ) (P D : ℕ) (d : ℕ) : ℝ :=
  if d ∈ (sqfDivisors P).filter (· ≤ D)
  then (ArithmeticFunction.moebius d : ℝ) * V_function g P (D / d) / V_function g P D
  else 0

-- ── Sieve density structure ───────────────────────────────────────────────

/-- Bundle of well-posedness assumptions for a multiplicative sieve density
    function g on squarefree divisors of P with sieve level D. -/
structure SieveDensity (g : ℕ → ℝ) (P D : ℕ) : Prop where
  hP        : Squarefree P
  hP_pos    : 0 < P
  hD        : 1 ≤ D
  hg1       : g 1 = 1
  hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d
  hg_range  : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1
  hg_mult   : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
                d ∣ P → e ∣ P → g (d * e) = g d * g e

-- ════════════════════════════════════════════════════════════════════════════
-- §1.  Möbius Weights (5 theorems)
--     The quadratic form Q(λ) at the Möbius weights equals φ(P)/P,
--     which is minimal among all admissible weights with λ₁ = 1.
-- ════════════════════════════════════════════════════════════════════════════

/-- **moebiusWeights_one**
    The Möbius weight at 1 equals 1. This is the normalization condition
    λ₁ = 1 for Selberg sieve weights, which holds for the Möbius function
    since μ(1) = 1 and 1 is a squarefree divisor of any nonzero P. -/
theorem moebiusWeights_one (P : ℕ) (hP_pos : 0 < P) :
    moebiusWeights P 1 = 1 := by
  sorry

/-- **moebius_quadForm_eq**
    At the Möbius weights, the multi-prime quadratic form evaluates to
    φ(P)/P. This is a fundamental identity: Q(μ_P) = ∏_{p|P} (1 − 1/p).
    The proof uses multiplicativity of both Q and μ, reducing to the
    prime case where Q(μ_p) = 1 − 1/p. -/
theorem moebius_quadForm_eq (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      (Nat.totient P : ℝ) / (P : ℝ) := by
  sorry

/-- **multiPrimeQuadForm_lower_bound'**
    For any admissible weights λ (λ₁ = 1, support inside sqfDivisors P),
    the quadratic form satisfies Q(λ) ≥ φ(P)/P. This is the key
    optimality result: the Möbius weights achieve the absolute minimum
    of Q among all admissible weight systems. -/
theorem multiPrimeQuadForm_lower_bound'
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    (Nat.totient P : ℝ) / (P : ℝ) ≤ multiPrimeQuadForm P lambda := by
  sorry

/-- **optimalWeight_quadForm_eq_moebius**
    Q(μ_P) = 1 / V(1/·, P, P). This connects the quadratic form at
    Möbius weights to the reciprocal sum V-function with g(d) = 1/d.
    The identity V(1/·, P, P) = P/φ(P) gives the bridge between the
    two formulations of the Selberg upper bound. -/
theorem optimalWeight_quadForm_eq_moebius
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      1 / V_function (fun n => (1 : ℝ) / n) P P := by
  sorry

/-- **multiPrimeQuadForm_lower_bound_inv**
    Equivalently, Q(λ) ≥ 1 / V(1/·, P, P) for any admissible λ.
    This dual formulation expresses the lower bound directly in terms
    of the V-sum, without explicit reference to φ(P). -/
theorem multiPrimeQuadForm_lower_bound_inv
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    1 / V_function (fun n => (1 : ℝ) / n) P P ≤
      multiPrimeQuadForm P lambda := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §2.  Parity Budget — Abstract Framework (4 theorems)
--     These lemmas establish the general inequality chain for any
--     majorant M and any signed witness χ bounded by 1.
-- ════════════════════════════════════════════════════════════════════════════

namespace Majorant
variable {N : ℕ} (M : Majorant N)

/-- **target_correlation_le_majorant_correlation_plus_surplus**
    Lemma 3.1: For any signed witness χ bounded by 1 in absolute value,
    the target's correlation with χ does not exceed the majorant's
    correlation with χ plus the mass surplus (mass − targetMass).
    Σ target(x)χ(x) ≤ Σ ν(x)χ(x) + (mass − targetMass).
    This is the fundamental inequality underlying the parity budget
    theorem: any gap between target and majorant correlations is
    bounded by the excess mass. -/
lemma target_correlation_le_majorant_correlation_plus_surplus
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1) :
    ∑ x, M.target x * χ x ≤
      ∑ x, M.nu x * χ x + (M.mass - M.targetMass) := by
  sorry

/-- **parity_separation_implies_surplus**
    Lemma 3.2: If the target has parity correlation at least α but
    the majorant has correlation at most β, then the difference
    α − β ≤ mass − targetMass. This quantifies the "cost" of parity
    separation in terms of forced excess mass. -/
lemma parity_separation_implies_surplus
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β) :
    α - β ≤ M.mass - M.targetMass := by
  sorry

/-- **budget_from_parity_separation**
    Lemma 3.3: When parity separation occurs (α > β), the majorant's mass
    must exceed the target mass by at least α − β. That is:
    targetMass + (α − β) ≤ mass. This is the core budget inequality
    showing that parity-separating weights force excess mass. -/
lemma budget_from_parity_separation
    (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β)
    (hα : 0 < α - β) :
    M.targetMass + (α - β) ≤ M.mass := by
  sorry

/-- **energy_budget_from_parity_separation**
    Lemma 3.4: Combining parity separation with the restriction lower bound
    yields an energy budget: (targetMass + (α − β))² · ‖ν‖₂² ≥ targetMass⁴ / N.
    This shows that parity separation forces not only excess mass but
    also a specific lower bound on the L² energy of the majorant. -/
lemma energy_budget_from_parity_separation
    (hN : (0 : ℝ) < N) (χ : Fin N → ℝ) (hbound : ∀ x, |χ x| ≤ 1)
    {α β : ℝ}
    (htarget : α ≤ ∑ x, M.target x * χ x)
    (hmajor : ∑ x, M.nu x * χ x ≤ β)
    (hα : 0 < α - β) :
    (M.targetMass + (α - β)) ^ 2 * M.l2NormSq ≥ M.targetMass ^ 4 / N := by
  sorry

end Majorant

-- ════════════════════════════════════════════════════════════════════════════
-- §3.  Parity Witness Properties (3 theorems)
--     The concrete parity witness χ(x) = μ(gcd(x, P)) satisfies the
--     boundedness and positivity conditions needed by §2.
-- ════════════════════════════════════════════════════════════════════════════

/-- **parityWitness_bounded**
    Property 4.1: The parity witness is bounded: |χ(x)| ≤ 1 for all x.
    This holds because the Möbius function takes values only in
    {−1, 0, +1}, so its absolute value is at most 1. This bound is
    essential for applying the abstract framework of §2. -/
lemma parityWitness_bounded (P N : ℕ) (x : Fin N) :
    |parityWitness P N x| ≤ 1 := by
  sorry

/-- **parityWitness_coprime_eq_one**
    Property 4.2: When x is coprime to P, the parity witness equals 1
    (since μ(1) = 1). On the sifted set of elements coprime to P,
    the witness agrees with the indicator, giving the maximal positive
    correlation needed for parity separation. -/
lemma parityWitness_coprime_eq_one (P N : ℕ) (x : Fin N)
    (hcop : Nat.Coprime x.val P) :
    parityWitness P N x = 1 := by
  sorry

/-- **parityWitness_target_correlation**
    Property 4.3: The target parity correlation over Fin(P·m), summing
    only over elements coprime to P, equals φ(P)·m. This is the fixed
    positive numerator that drives the parity budget theorem: the target
    always has parity correlation φ(P)·m irrespective of the weight
    choice. -/
lemma parityWitness_target_correlation (P m : ℕ) (hP_pos : 0 < P) :
    ∑ x : Fin (P * m),
      (if Nat.Coprime x.val P then (1 : ℝ) else 0) * parityWitness P (P * m) x =
    (Nat.totient P : ℝ) * m := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §4.  Parity Budget — Möbius Case (Result A, 2 theorems)
--     These are the sorry-free core theorems: at Möbius weights,
--     parity-separating weights cannot beat the Möbius baseline.
-- ════════════════════════════════════════════════════════════════════════════

/-- **parity_budget_moebius**
    Theorem 5.1 (Result A — sorry-free): If weights λ suppress the parity
    witness to at most zero (i.e., Σ ν(x)·χ(x) ≤ 0), then the resulting
    mass bound gives (Nat.totient P)·m ≤ (P·m)·Q(λ), equivalently
    Q(λ) ≥ φ(P)/P. This is the core no-go theorem: any attempt to
    suppress the parity witness forces the quadratic form (and hence
    sieve mass) to be at least the Möbius baseline. -/
theorem parity_budget_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0)
    (hparity_sep :
      ∑ x : Fin (P * m),
        selbergNu (P * m) P lambda x * parityWitness P (P * m) x ≤ 0) :
    (Nat.totient P : ℝ) * m ≤
      (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  sorry

/-- **parity_separating_weights_cost_more_than_moebius**
    Theorem 5.2 (Result A — sorry-free): Parity-separating weights have
    quadratic form at least as large as the Möbius weights. That is,
    Q(μ) ≤ Q(λ) for any admissible λ with λ₁ = 1 and support on
    sqfDivisors P. The Möbius weights are provably optimal — any
    attempt to achieve parity separation costs more in the quadratic form. -/
theorem parity_separating_weights_cost_more_than_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (moebiusWeights P) ≤
      multiPrimeQuadForm P lambda := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §5.  Parity Budget — Concrete Examples (2 theorems)
--     Worked example for P = 6, m = 1 to validate the formulas.
-- ════════════════════════════════════════════════════════════════════════════

/-- **parityWitness_sum_six**
    Worked example P = 6: The parity witness on Fin 6 sums to zero.
    For P = 6 = 2·3, the prime factor parities cancel: among the 6
    residue classes mod 6, exactly half have an even number of prime
    factors in their gcd and half have an odd number.
    Sanity check: the signed witness over a full residue ring sums to 0. -/
lemma parityWitness_sum_six :
    ∑ x : Fin 6, parityWitness 6 6 x = 0 := by
  sorry

/-- **parityWitness_target_six**
    Worked example P = 6: Among the 6 residue classes, exactly 2 are
    coprime to 6 (1 and 5). For those, μ(gcd(x, 6)) = μ(1) = 1, so
    the target parity correlation is 2 = φ(6)·1. This validates the
    formula parityWitness_target_correlation for a concrete case. -/
lemma parityWitness_target_six :
    ∑ x : Fin 6,
      (if Nat.Coprime x.val 6 then (1 : ℝ) else 0) * parityWitness 6 6 x = 2 := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §6.  Parity Budget — General Case (Result B, 3 theorems)
--     Generalization to arbitrary multiplicative density g with
--     optimal weights. These are CONDITIONAL on `optimalWeight_quadForm_eq`
--     (the Selberg variational identity, IK eq. 6.70).
-- ════════════════════════════════════════════════════════════════════════════

/-- **optimalWeights_minimize_quadForm**
    The optimal Selberg weights minimize the quadratic form Q(λ) among all
    admissible weights λ with λ₁ = 1 and support in sqfDivisors P. This
    lemma is conditional on the proof of `optimalWeight_quadForm_eq`
    (Iwaniec-Kowalski eq. 6.70), which establishes Q(λ_opt) = 1/V(g,P,D).
    Once that identity is proven, positive semidefiniteness of Q implies
    Q(λ_opt) ≤ Q(λ) for all admissible λ. -/
lemma optimalWeights_minimize_quadForm
    (P D : ℕ) (g : ℕ → ℝ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) ≤
      multiPrimeQuadForm P lambda := by
  sorry

/-- **parity_budget_general**
    Theorem 6.1 (Result B — conditional): For arbitrary multiplicative
    density function g and sieve level D satisfying the SieveDensity
    conditions, the bound 1/V(g, P, D) ≤ Q(λ) holds for any admissible
    weights λ with λ₁ = 1 and support in sqfDivisors P. This generalizes
    the Möbius case (g(p) = 1/p) to arbitrary multiplicative g. The
    proof is conditional on `optimalWeight_quadForm_eq`. -/
theorem parity_budget_general
    (P : ℕ) (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    1 / V_function g P D ≤ multiPrimeQuadForm P lambda := by
  sorry

/-- **parity_separating_weights_exceed_optimal**
    Theorem 6.2 (Result B — conditional): Parity-separating weights have
    quadratic form at least as large as the general optimal baseline.
    This extends Theorem 5.2 from the Möbius baseline to the general
    optimal weights, conditional on `optimalWeight_quadForm_eq`. The
    statement is: Q(λ_opt) ≤ Q(λ) for any admissible λ. -/
theorem parity_separating_weights_exceed_optimal
    (P : ℕ) (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) ≤
      multiPrimeQuadForm P lambda := by
  sorry

end
