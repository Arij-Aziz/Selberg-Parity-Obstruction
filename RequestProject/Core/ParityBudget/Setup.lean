/-
# ParityBudget.Setup

Definitions for the parity budget framework.

## Main definitions

* `parityWitness` — the finite parity witness χ(x) = μ(gcd(x, P))

Status: [NEW-ABSTRACT]
-/
import Mathlib
import RequestProject.Core.MultiPrime.Setup

open Finset BigOperators Nat

noncomputable section

/-- The parity witness on `Fin N`: χ(x) = μ(gcd(x, P)).
    For squarefree P, this takes values in {-1, +1}, being +1 when
    gcd(x, P) has an even number of prime factors and -1 when odd. -/
noncomputable def parityWitness (P : ℕ) (N : ℕ) (x : Fin N) : ℝ :=
  (ArithmeticFunction.moebius (Nat.gcd x.val P) : ℝ)

end
