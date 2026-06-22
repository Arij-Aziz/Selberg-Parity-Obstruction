-- Selberg Majorant Improvement: Machine-verified formalization
-- Paper: "Rigidity of the Selberg Majorant: Stability, Restriction,
--         and a Quadratic Form Identity with Machine-Verified Proofs"
--
-- Axiom audit: RequestProject/Audit.lean
-- All main theorems depend only on [propext, Classical.choice, Quot.sound].
-- Zero sorry.
--
-- Future/ contains scaffolding for future work.

-- ── Core sieve infrastructure ───────────────────────────────────────────────
import RequestProject.Core.Basic
import RequestProject.Core.Weights.Definition
import RequestProject.Core.Weights.Bounds
import RequestProject.Core.Weights.UpperBound
import RequestProject.Core.Weights.Optimization
import RequestProject.Core.Majorant
import RequestProject.Core.MajorantComparison
import RequestProject.Core.SelbergComparison
import RequestProject.Core.Fourier
import RequestProject.Core.FourierRatio
import RequestProject.Core.Transference
import RequestProject.Core.Weights.QuadFormStability
-- ── Theorem 1: Kinetic Propagation ────────────────────────────────────────────
import RequestProject.Core.KineticPropagation

-- ── Theorem 2: Restriction Lower Bound ────────────────────────────────────────
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.SelbergRestriction

-- ── Theorem 3: Fourier–Sieve Identity ─────────────────────────────────────────
import RequestProject.Core.Weights.FourierConnection

-- ── Multi-prime extension ─────────────────────────────────────────────────────
import RequestProject.Core.MultiPrime.Setup
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MultiPrime.FourierRatioSharp
import RequestProject.Core.MultiPrime.SelbergCorrelation
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.SelbergWeightCorrelation
import RequestProject.Core.MultiPrime.SelbergUpperBound
import RequestProject.Core.MultiPrime.SelbergCorrelationBoundDisproved
import RequestProject.Core.MultiPrime.GeneralWeightConnection

-- ── Parity Budget (no-go theorem) ─────────────────────────────────────────────
import RequestProject.Core.ParityBudget.Setup
import RequestProject.Core.ParityBudget.AbstractBudget
import RequestProject.Core.ParityBudget.FiniteParityProxy
import RequestProject.Core.ParityBudget.MoebiusCase
import RequestProject.Core.ParityBudget.Examples
import RequestProject.Core.ParityBudget.GeneralCase

-- ── Result 1: Sharp Mass–Energy Tradeoff ─────────────────────────────────────────
import RequestProject.Core.MassEnergyTradeoff.MassEnergySandwich

-- ── Result 2: Restriction Lower Bound for Selberg Majorants ──────────────────
import RequestProject.Core.RestrictionLowerBoundSelberg

-- ── Result 3: Kinetic Propagation Stability ─────────────────────────────────
import RequestProject.Core.KineticStability.VFunctionStability

-- ── Central registry ─────────────────────────────────────────────────────────
import RequestProject.AssumptionsRegistry

-- ── Audit ─────────────────────────────────────────
import RequestProject.Audit

