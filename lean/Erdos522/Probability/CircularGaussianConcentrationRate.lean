/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianLogarithmicConcentration
import Erdos522.Probability.GaussianConcentrationRate

/-!
# Polynomial logarithmic concentration for Gaussian coefficients

The logarithmic moment order and clipping levels are chosen uniformly over a
fixed radial annulus. The random energy contributes its explicit exponential
failure probability in addition to the summable polynomial bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522

/-- A common coefficient for the mean and variance occupation errors. -/
def circularGaussianOccupationConstant (K : ℝ) : ℝ :=
  circularGaussianOccupationMeanConstant K + circularGaussianOccupationVarianceConstant K

theorem circularGaussianOccupationConstant_pos (K : ℝ) : 0 < circularGaussianOccupationConstant K := by
  unfold circularGaussianOccupationConstant circularGaussianOccupationMeanConstant
    circularGaussianOccupationVarianceConstant circularGaussianValuePairError
  positivity

/-- Uniform concentration in a fixed `K/N` annulus with explicit finite failure
coefficient and the random-energy exponential term. -/
theorem eventually_circularGaussian_logarithmic_concentration (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N+1) g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
          (2 * circularGaussianOccupationConstant K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  let H := circularGaussianOccupationConstant K
  have hH : 0 < H := circularGaussianOccupationConstant_pos K
  have hm : 0 ≤ circularGaussianOccupationMeanConstant K := by
    unfold circularGaussianOccupationMeanConstant; positivity
  have hv : 0 ≤ circularGaussianOccupationVarianceConstant K := by
    unfold circularGaussianOccupationVarianceConstant circularGaussianValuePairError; positivity
  have hmH : circularGaussianOccupationMeanConstant K ≤ H := by dsimp [H, circularGaussianOccupationConstant]; linarith
  have hvH : circularGaussianOccupationVarianceConstant K ≤ H := by dsimp [H, circularGaussianOccupationConstant]; linarith
  have he := (tendsto_logarithmicRelativeError 16 H).add
    (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (1 / 2 : ℝ))
  simp only [mul_zero, add_zero, Function.comp_def] at he
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1,
    he.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hN hNK hdegree hlog herror
  change 1 ≤ Real.log N at hlog
  intro r hrl hru
  have hn : 1 < N := by omega
  have hn0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn0
  have htol := logarithmicTolerance_pos hn
  have hD : 0 < logarithmicMomentCutoff 16 N := by
    unfold logarithmicMomentCutoff
    have hl : 0 < Real.log N := by linarith
    positivity
  have hd := div_le_div_of_nonneg_right hmH (Real.sqrt_nonneg (N : ℝ))
  have hvc := div_le_div_of_nonneg_right hvH (Real.sqrt_nonneg (N : ℝ))
  have hthreshold := (gaussian_logarithmic_threshold_le (A := 16) hlog hH.le).trans
    (show logarithmicTolerance N / 2 +
      (logarithmicRelativeError 16 H N + (1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) *
        logarithmicTolerance N ≤ logarithmicTolerance N by nlinarith)
  have hsmallThreshold :
      logarithmicTolerance N / 2 + 2 * (Real.log N / 32) *
          (circularGaussianOccupationMeanConstant K / Real.sqrt N) +
        logarithmicMomentCutoff 16 N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + circularGaussianOccupationMeanConstant K / Real.sqrt N +
            (N : ℝ) ^ (-1 / 16 : ℝ)) + 2 * Real.exp (-2 * (Real.log N / 32)) ≤
      logarithmicTolerance N := by
    apply le_trans _ hthreshold
    gcongr
  have h := circularGaussian_logarithmic_integral_concentration N hn0 K r hK hNK hrl hru hdegree
    (Real.log N) hlog (Real.log N / 32) (logarithmicTolerance N / 2)
    ((N : ℝ) ^ (-1 / 16 : ℝ)) (logarithmicMomentCutoff 16 N)
    (by linarith) (by positivity) (Real.rpow_pos_of_pos hNr _) hD
  have hmoment : (32 * Real.log N) ^ (2 * Real.log N) ≤
      (16 * (2 * Real.log N)) ^ (12 * Real.log N) := by
    rw [show 16 * (2 * Real.log N) = 32 * Real.log N by ring]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hbudget :
      (circularGaussianOccupationVarianceConstant K / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
        (32 * Real.log N) ^ (2 * Real.log N) / (logarithmicMomentCutoff 16 N ^ 2) ^ Real.log N +
        4 * (Real.log N / 32) ^ 2 * (circularGaussianOccupationVarianceConstant K / Real.sqrt N) /
          (logarithmicTolerance N / 2) ^ 2 ≤
      (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
    apply le_trans _ (logarithmic_failure_le (A := 16) hlog (by norm_num) hH.le)
    gcongr
  have hprob := (measure_mono (μ := Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian))
    (show {g | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N+1) g) r - Real.log (radialSigma N r) - circularLogMean|} ⊆ _
      from fun _ hg => lt_of_le_of_lt hsmallThreshold hg)).trans h
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal (show
    2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
        (circularGaussianOccupationVarianceConstant K / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
        (32 * Real.log N) ^ (2 * Real.log N) / (logarithmicMomentCutoff 16 N ^ 2) ^ Real.log N +
        4 * (Real.log N / 32) ^ 2 * (circularGaussianOccupationVarianceConstant K / Real.sqrt N) /
          (logarithmicTolerance N / 2) ^ 2 ≤
      2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
        (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) by linarith))
  have hnneg : 0 ≤ 2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
      (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

/-- A pure polynomial failure bound, uniform in each fixed radial annulus. -/
theorem eventually_circularGaussian_logarithmic_concentration_power (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N+1) g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        (2 * circularGaussianOccupationConstant K + 3) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  filter_upwards [eventually_circularGaussian_logarithmic_concentration K hK,
    eventually_gaussian_energy_le_logarithmic_power K] with N hN henergy
  intro r hrl hru
  have h := hN r hrl hru
  linarith

end Erdos522
