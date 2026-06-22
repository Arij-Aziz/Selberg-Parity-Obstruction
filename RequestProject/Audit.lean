-- Audit.lean: axiom footprint for all main theorems.
-- Expected for each: [propext, Classical.choice, Quot.sound]
-- Any 'sorry' invalidates the proof chain.

import RequestProject.Core.SelbergComparison
import RequestProject.Core.KineticPropagation
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.Weights.FourierConnection
import RequestProject.Core.SelbergRestriction
import RequestProject.Core.Weights.QuadFormStability
import RequestProject.Core.Weights.UpperBound
import RequestProject.Core.MultiPrime.Setup
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower
import RequestProject.Core.KineticStability.QuadFormPerturbation
import RequestProject.Core.MultiPrime.FourierRatioSharp
import RequestProject.Core.MultiPrime.SelbergCorrelation
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.SelbergWeightCorrelation
import RequestProject.Core.MultiPrime.SelbergUpperBound
import RequestProject.Core.MultiPrime.RemainderBound
import RequestProject.Core.MultiPrime.SelbergCorrelationBoundDisproved
import RequestProject.Core.MultiPrime.GeneralWeightConnection
import RequestProject.Core.ParityBudget.AbstractBudget
import RequestProject.Core.ParityBudget.FiniteParityProxy
import RequestProject.Core.ParityBudget.MoebiusCase
import RequestProject.Core.ParityBudget.Examples
import RequestProject.Core.ParityBudget.GeneralCase


-- ── MoebiusWeights ──────────────────────────────────────────────────────────
#print axioms moebiusWeights_one
#print axioms moebius_quadForm_eq
#print axioms multiPrimeQuadForm_lower_bound'
#print axioms optimalWeight_quadForm_eq_moebius
#print axioms multiPrimeQuadForm_lower_bound_inv

-- ── Parity Budget (Result A — sorry-free) ─────────────────────────────────────
#print axioms Majorant.target_correlation_le_majorant_correlation_plus_surplus
#print axioms Majorant.parity_separation_implies_surplus
#print axioms Majorant.budget_from_parity_separation
#print axioms Majorant.energy_budget_from_parity_separation
#print axioms parityWitness_bounded
#print axioms parityWitness_coprime_eq_one
#print axioms parityWitness_target_correlation
#print axioms parity_budget_moebius
#print axioms parity_separating_weights_cost_more_than_moebius
#print axioms parityWitness_sum_six
#print axioms parityWitness_target_six
-- Expected: [propext, Classical.choice, Quot.sound] (+ Lean.ofReduceBool for Examples)

-- ── Parity Budget (Result B — conditional on optimalWeight_quadForm_eq) ────────
#print axioms optimalWeights_minimize_quadForm
#print axioms parity_budget_general
#print axioms parity_separating_weights_exceed_optimal
-- Expected: [propext, Classical.choice, Quot.sound, sorryAx]
