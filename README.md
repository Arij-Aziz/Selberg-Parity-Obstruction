![Build](https://github.com/Arij-Aziz/Selberg-Parity-Obstruction/actions/workflows/build.yml/badge.svg)
# Selberg Majorant: Parity Budget Extension — A Lean 4 Formalization

Machine-verified proofs formalizing the **Parity Obstruction** for the multi-prime Selberg majorant. This project extends the multi-prime framework to prove that any sieve majorant attempting to separate numbers by their prime-factor parity must incur a strict, quantifiable penalty in its mass and L² energy. 

Formalized in Lean 4 using Mathlib. The abstract structural inequalities and the Möbius-weight case are fully sorry-free; axiom footprint verified as `[propext, Classical.choice, Quot.sound]` for all theorems outside the one deferred optimal-weight step (see `RequestProject/Audit.lean` and **Sorry Status** below).
Challenge.lean (root) is a statement-only mirror for the comparator check; its sorry proofs are intentional placeholders and are not part of the verified proof chain.

## What This Project Is

This project formalizes the "parity budget" theorem. In sieve theory, the parity problem prevents classical sieves from distinguishing numbers with an even number of prime factors from those with an odd number. This repository makes that obstruction mathematically rigid for majorants on finite rings Fin(P·m).

The central object of this extension is the finite parity witness:

    χ(x) = μ(gcd(x, P))

The central identity of the project proves that if a majorant ν successfully suppresses this witness (majorant correlation ≤ β) while the target correlates positively (target correlation ≥ α), its mass must strictly inflate:

    mass(ν)  ≥  targetMass  +  (α − β)
    ‖ν‖₂²    ≥  (targetMass + (α − β))² / N

Every other parity result in the project follows from the structural inequalities governing this witness.

## What This Project Is Not

- **Not a resolution to the prime parity problem.** This proves the structural limitations of *sieve majorants* on finite sets; it does not evaluate asymptotic prime distributions (e.g., the Goldston-Pintz-Yıldırım or Zhang/Maynard frameworks).
- **Not a new sieve construction.** This project assesses the limitations of weights (λ_d) evaluated on the standard Selberg quadratic form Q(λ).
- **Not a proof of uniqueness.** It evaluates the bounds required for parity separation but does not claim the majorant is globally unique.

## Sorry Status

There is exactly **one `sorry`** in the project:


```

optimalWeights_minimize_quadForm   (RequestProject/Core/ParityBudget/GeneralCase.lean)

```

This states: the general optimal Selberg weights minimize the multi-prime quadratic form Q(λ). 

This relies on the exact same variational calculus identity deferred in the underlying multi-prime project (Iwaniec–Kowalski eq. 6.70). Result B (the general case budget) is conditionally dependent on this single optimization fact.

**Everything that can be proved without this step is proved.**
The abstract parity budget framework, the witness properties, and the Möbius weight applications (Result A) are **100% `sorry`-free**.

## Main Results

**Theorem A — The Abstract Parity Budget**
(`Core/ParityBudget/AbstractBudget.lean`)

For *any* majorant M and bounded witness |χ(x)| ≤ 1:
If the target correlates with χ by at least α, and the majorant suppresses χ to at most β, then:

    M.targetMass + (α − β)  ≤  M.mass
    (M.targetMass + (α − β))² / N  ≤  M.l2NormSq

This is `budget_from_parity_separation` and `energy_budget_from_parity_separation`. 

**Theorem B — Witness Boundedness & Target Correlation**
(`Core/ParityBudget/Setup.lean`)

For the specific parity witness χ(x) = μ(gcd(x, P)):

    |χ(x)|  ≤  1
    Σ_{gcd(x,P)=1} χ(x)  =  φ(P) · m

This is `parityWitness_bounded` and `parityWitness_target_correlation`.

**Result A — Parity Budget for Möbius Weights**
(`Core/ParityBudget/MoebiusCase.lean`)

If any weight system λ suppresses the parity witness to ≤ 0, the quadratic form must be bounded below by the Möbius baseline:

    Q(λ)  ≥  φ(P) / P

This is `parity_budget_moebius`. Consequently, `parity_separating_weights_cost_more_than_moebius` proves that parity-separating weights strictly cost more than Möbius weights. Both are fully sorry-free.

**Result B — General Case (Conditional)**
(`Core/ParityBudget/GeneralCase.lean`)

For an arbitrary multiplicative density g(d) and level D, any parity-separating weight system satisfies:

    Q(λ)  ≥  1 / V(g, P, D)

This is `parity_budget_general`, extending Result A to general optimal weights (conditional on the single sorry).

**Concrete Validation**
(`Core/ParityBudget/Examples.lean`)

The framework is instantiated and validated on a concrete finite ring (P = 6, m = 1) to guarantee the absence of vacuous truths:

    Σ_{x ∈ Fin 6} χ(x)  =  0
    target_correlation  =  2

## Auditable Statement File

`Challenge.lean` is a self-contained reviewer file. It has exactly one import (`import Mathlib`) and no `RequestProject.*` imports. Every theorem introduced in this extension is restated verbatim with `sorry` as its proof body, with all project-internal definitions reproduced inline using only Mathlib primitives. A reviewer can verify every statement is well-typed by running:

```bash
lake build Challenge

```

Expected output: zero errors; only `declaration uses sorry` warnings (intended). The file covers exactly 19 new theorems, matching the theorem list exactly.

## Scope of Novelty

We are not aware of the following appearing in the literature in this form:

1. A machine-verified abstract structural inequality explicitly linking majorant mass surplus to witness suppression (`targetMass + (α - β) ≤ mass`).
2. The rigorous instantiation of the parity witness χ(x) = μ(gcd(x, P)) evaluated exactly on finite rings Fin(P·m) inside a theorem prover.
3. A formal proof that parity-separating weights must strictly inflate the quadratic form over the baseline Möbius weights Q(μ_P).

## Axiom Audit

All sorry-free theorems verified with `#print axioms` (see `RequestProject/Audit.lean`). Expected footprint for each: `[propext, Classical.choice, Quot.sound]`.

```
── §2. Abstract Parity Budget ──────────────────────────────────────────────
target_correlation_le_majorant_correlation_plus_surplus → [propext, Classical.choice, Quot.sound]
parity_separation_implies_surplus                       → [propext, Classical.choice, Quot.sound]
budget_from_parity_separation                           → [propext, Classical.choice, Quot.sound]
energy_budget_from_parity_separation                    → [propext, Classical.choice, Quot.sound]

── §3. Witness Properties ──────────────────────────────────────────────────
parityWitness_bounded                                   → [propext, Classical.choice, Quot.sound]
parityWitness_coprime_eq_one                            → [propext, Classical.choice, Quot.sound]
parityWitness_target_correlation                        → [propext, Classical.choice, Quot.sound]

── §4. Möbius Case (Result A) ──────────────────────────────────────────────
parity_budget_moebius                                   → [propext, Classical.choice, Quot.sound]
parity_separating_weights_cost_more_than_moebius        → [propext, Classical.choice, Quot.sound]

── §5. Concrete Examples ───────────────────────────────────────────────────
parityWitness_sum_six                                   → [propext, Classical.choice, Quot.sound]
parityWitness_target_six                                → [propext, Classical.choice, Quot.sound]

-- conditional on optimalWeights_minimize_quadForm — sorryAx is EXPECTED
#print axioms parity_budget_general
#print axioms parity_separating_weights_exceed_optimal
-- Expected: [propext, Classical.choice, Quot.sound, sorryAx]

```

Classical logic only.

## AI Assistance

This project is a human–AI collaboration. Mathematical direction, abstract framework definitions, theorem statements, and scope decisions were made by the human author. AI assistance was used for executing tactics (e.g., `linarith` and Cauchy-Schwarz manipulations in `AbstractBudget.lean`), proof elaboration, and infrastructure lemmas. All mathematical claims were decided and verified by the human author.

## Build

```bash
lake exe cache get
lake build

```

Requires Lean toolchain `leanprover/lean4:v4.28.0` (see `lean-toolchain`).

## File Map

```
RequestProject/
├── Audit.lean                              ← #print axioms for all new theorems
├── AssumptionsRegistry.lean                ← Manually maintained proof-status log
├── Main.lean                               ← Top-level imports
└── Core/
    └── ParityBudget/
        ├── Setup.lean                      ← parityWitness definition and bounds
        ├── AbstractBudget.lean             ← Abstract framework: budget_from_parity_separation
        ├── MoebiusCase.lean                ← Result A: parity_budget_moebius (sorry-free)
        ├── GeneralCase.lean                ← Result B: parity_budget_general (conditional)
        ├── FiniteParityProxy.lean          ← Structural proxy lemmas
        └── Examples.lean                   ← Concrete validation on P=6

formalization.yml                           ← Machine-readable project metadata
Challenge.lean                              ← Pure-Mathlib auditable statement file (sorry proofs)
Solution.lean                               ← File that only imports Main.lean file

```

