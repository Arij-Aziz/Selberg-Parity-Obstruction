![Build](https://github.com/Arij-Aziz/Selberg-Parity-Obstruction/actions/workflows/build.yml/badge.svg)
# Selberg Majorant: Parity Budget Extension — A Lean 4 Formalization

Machine-verified proofs formalizing the **Parity Obstruction** for the multi-prime Selberg majorant. This project extends the multi-prime framework to prove that any sieve majorant attempting to separate numbers by their prime-factor parity must incur a strict, quantifiable penalty in its mass and $L^2$ energy. 

Formalized in Lean 4 using Mathlib. The abstract structural inequalities and the Möbius-weight case (Result A) are fully sorry-free.

## What This Project Is

This project formalizes the "parity budget" theorem. In sieve theory, the parity problem prevents classical sieves from distinguishing numbers with an even number of prime factors from those with an odd number. 

This repository makes that obstruction mathematically rigid for majorants. It defines a finite parity witness $\chi(x) = \mu(\gcd(x, P))$ and proves that if a majorant $\nu$ successfully suppresses this witness, its mass and $L^2$ norm must strictly inflate. 

The core abstract identity proved here is:
If target correlation $\ge \alpha$ and majorant correlation $\le \beta$, then:
    `mass(ν) ≥ targetMass + (α - β)`
    `‖ν‖₂² ≥ (targetMass + (α - β))² / N`

## What This Project Is Not

- **Not a resolution to the prime parity problem.** This proves the structural limitations of *sieve majorants* on finite sets, it does not evaluate asymptotic prime distributions (e.g., the Goldston-Pintz-Yıldırım or Zhang/Maynard frameworks).
- **Not a new sieve construction.** This project assesses the limitations of weights ($\lambda_d$) evaluated on the standard Selberg quadratic form $Q(\lambda)$.

## Sorry Status

The abstract parity budget framework, the witness properties, and the Möbius weight applications (Result A) are **100% `sorry`-free**.

There is exactly **one `sorry`** introduced in this extension:
optimalWeights_minimize_quadForm   (RequestProject/Core/ParityBudget/GeneralCase.lean)

This lemma asserts that the general optimal Selberg weights minimize the multi-prime quadratic form $Q(\lambda)$. This relies on the exact same variational calculus identity deferred in the underlying multi-prime project (Iwaniec–Kowalski eq. 6.70). Result B (the general case budget) is conditionally dependent on this single optimization fact.

## Main Results

**Theorem 1 — The Abstract Parity Budget**
(`Core/ParityBudget/AbstractBudget.lean`)
For *any* majorant $M$ and bounded witness $|\chi(x)| \le 1$:
If the target correlates with $\chi$ by at least $\alpha$, and the majorant suppresses $\chi$ to at most $\beta$, then:
    `M.targetMass + (α - β) ≤ M.mass`  (`budget_from_parity_separation`)

**Theorem 2 — Witness Boundedness & Target Correlation**
(`Core/ParityBudget/Setup.lean`, `Challenge.lean §3`)
For the specific parity witness $\chi(x) = \mu(\gcd(x, P))$:
    `|χ(x)| ≤ 1`
    `Σ_{gcd(x,P)=1} χ(x) = φ(P)·m`

**Result A — Parity Budget for Möbius Weights (Sorry-Free)**
(`Core/ParityBudget/MoebiusCase.lean`)
If any weight system $\lambda$ suppresses the parity witness to $\le 0$, the quadratic form must be bounded below by the Möbius baseline:
    `Q(λ) ≥ φ(P)/P` (`parity_budget_moebius`)
Consequently, parity-separating weights strictly cost more than Möbius weights.

**Result B — General Case (Conditional)**
(`Core/ParityBudget/GeneralCase.lean`)
For an arbitrary multiplicative density $g(d)$ and level $D$, any parity-separating weight system satisfies:
    `Q(λ) ≥ 1 / V(g, P, D)`

**Concrete Validation**
(`Core/ParityBudget/Examples.lean`)
The framework is instantiated and validated on a concrete finite ring ($P=6, m=1$) to guarantee absence of vacuous truths. 
    `Σ_{x \in Fin 6} χ(x) = 0` and `target_correlation = 2`.

## Auditable Statement File

`Challenge.lean` is a self-contained reviewer file. It has exactly one import (`import Mathlib`). Every theorem introduced in this extension is restated verbatim with `sorry` as its proof body, with all project-internal definitions reproduced inline using only Mathlib primitives.

To verify well-typedness:
```bash
lake build Challenge
```
## Axiom Audit
All sorry-free theorems verified with #print axioms. Expected footprint: [propext, Classical.choice, Quot.sound]. Classical logic only.

Bash
#print axioms target_correlation_le_majorant_correlation_plus_surplus
#print axioms parity_budget_moebius
