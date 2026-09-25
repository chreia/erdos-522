/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseRadialLimits
import Erdos522.Probability.BlockSupremaAlmostSure
import Erdos522.Analysis.HarmonicRestriction

/-!
# Summable exceptions for sublevel components near the circle

Eight Jensen probes, one curvature event, and one annular derivative-count
event control all components meeting a prescribed nearby circle. The same
exception controls every target radius admitted by the deterministic geometry.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- Failure of the uniform second-derivative envelope on an enlarged annulus. -/
def radialCurvatureFailure (N : ℕ) (K : ℝ) : Set (SignVector N) :=
  {v | ∃ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N ∧
    DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(rademacherPolynomial N v).derivative.derivative.eval z‖}

/-- Failure of the quantitative annular small-derivative root bound. -/
def annularDerivativeCountFailure (N : ℕ) (K : ℝ) : Set (SignVector N) :=
  {v | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (rademacherPolynomial N v) N K
      ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}

/-- The four exceptional events used for nearby-circle sublevel counts. -/
def sublevelCrossingFailure (K N : ℕ) : Set (SignVector N) :=
  ((radialLogarithmicFailure N (radialSecantRadii ((K : ℝ) + 1) N) ∪
    radialLogarithmicFailure N (radialSecantRadii (reciprocalProbeWidth K) N)) ∪
    radialCurvatureFailure N ((K : ℝ) + 1)) ∪
    annularDerivativeCountFailure N ((K : ℝ) + 1)

/-- The curvature failures are summable even before passing to sparse degrees. -/
theorem summable_radialCurvatureFailure (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun N : ℕ => (signMeasure N).real (radialCurvatureFailure N K)) := by
  apply (summable_inverse_nat_power 10 (by norm_num)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact DerivativeSupremum.second_derivative_supremum N hN hK hKN

/-- At each fixed annular width, all nearby-circle exceptions have a finite
sum along the eighth-power degrees. -/
theorem summable_sublevelCrossingFailure (K : ℕ) :
    Summable (fun j : ℕ => (signMeasure (j ^ 8)).real (sublevelCrossingFailure K (j ^ 8))) := by
  have houter := summable_radialLogarithmicFailure one_le_harmonicRestrictionConstant
    harmonic_l2_restriction ((K : ℝ) + 1) (by positivity)
    (radialSecantRadii ((K : ℝ) + 1))
    (Eventually.of_forall fun N i => radialSecantRadii_mem_annulus (by positivity) N i) 8 (by norm_num)
  have hinner := summable_radialLogarithmicFailure one_le_harmonicRestrictionConstant
    harmonic_l2_restriction (reciprocalProbeWidth K) (reciprocalProbeWidth_pos K).le
    (radialSecantRadii (reciprocalProbeWidth K))
    (Eventually.of_forall fun N i => radialSecantRadii_mem_annulus
      (reciprocalProbeWidth_pos K).le N i) 8 (by norm_num)
  have hcurvature := (summable_radialCurvatureFailure ((K : ℝ) + 1) (by positivity)).comp_injective
    strictMono_eighth_power.injective
  have hderivative := summable_annular_small_derivative_failures ((K : ℝ) + 1) (by positivity)
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _
    (((houter.add hinner).add hcurvature).add hderivative)
  intro j
  unfold sublevelCrossingFailure
  exact (measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)) le_rfl)

end Erdos522
