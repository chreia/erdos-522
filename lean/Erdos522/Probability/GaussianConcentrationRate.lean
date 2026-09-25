/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianLogarithmicConcentration
import Erdos522.Probability.LogarithmicConcentrationRate

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
def gaussianOccupationConstant (K : ℝ) : ℝ :=
  gaussianOccupationMeanConstant K + gaussianOccupationVarianceConstant K

theorem gaussianOccupationConstant_pos (K : ℝ) : 0 < gaussianOccupationConstant K := by
  unfold gaussianOccupationConstant gaussianOccupationMeanConstant
    gaussianOccupationVarianceConstant gaussianValuePairError
  positivity

/-- The extra half-unit of energy in the Gaussian clipping estimate is negligible
relative to the logarithmic tolerance. -/
theorem gaussian_logarithmic_threshold_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {A H : ℝ} (hH : 0 ≤ H) :
    logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
        logarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
        2 * Real.exp (-2 * (Real.log N / 32)) ≤
      logarithmicTolerance N / 2 +
        (logarithmicRelativeError A H N + (1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) *
          logarithmicTolerance N := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hp7 : 1 ≤ (Real.log N) ^ 7 := one_le_pow₀ hlog
  have hpow : (N : ℝ) ^ (-1 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ) =
      (N : ℝ) ^ (-1 / 16 : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  have htail : (1 / 2 : ℝ) * Real.exp (-2 * (Real.log N / 32)) ≤
      ((1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) * logarithmicTolerance N := by
    rw [logarithmic_clipping_exp hn]
    calc
      _ ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) * (Real.log N) ^ 7 := by
        convert mul_le_mul_of_nonneg_left hp7
          (show 0 ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) by positivity) using 1
        ring
      _ = _ := by
        unfold logarithmicTolerance
        rw [show (1 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ) *
            ((N : ℝ) ^ (-1 / 32 : ℝ) * Real.log N ^ 7) =
          (1 / 2 : ℝ) * ((N : ℝ) ^ (-1 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) *
            Real.log N ^ 7 by ring, hpow]
  have h := logarithmic_threshold_le (A := A) hlog hH
  nlinarith only [h, htail]

/-- Uniform concentration in a fixed `K/N` annulus with explicit finite failure
coefficient and the random-energy exponential term. -/
theorem eventually_gaussian_logarithmic_concentration (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
      (gaussianCoefficientMeasure (N + 1)).real {g | logarithmicTolerance N <
        |logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
          (2 * gaussianOccupationConstant K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  let H := gaussianOccupationConstant K
  have hH : 0 < H := gaussianOccupationConstant_pos K
  have hm : 0 ≤ gaussianOccupationMeanConstant K := by
    unfold gaussianOccupationMeanConstant; positivity
  have hv : 0 ≤ gaussianOccupationVarianceConstant K := by
    unfold gaussianOccupationVarianceConstant gaussianValuePairError; positivity
  have hmH : gaussianOccupationMeanConstant K ≤ H := by dsimp [H, gaussianOccupationConstant]; linarith
  have hvH : gaussianOccupationVarianceConstant K ≤ H := by dsimp [H, gaussianOccupationConstant]; linarith
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
          (gaussianOccupationMeanConstant K / Real.sqrt N) +
        logarithmicMomentCutoff 16 N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + gaussianOccupationMeanConstant K / Real.sqrt N +
            (N : ℝ) ^ (-1 / 16 : ℝ)) + 2 * Real.exp (-2 * (Real.log N / 32)) ≤
      logarithmicTolerance N := by
    apply le_trans _ hthreshold
    gcongr
  have h := gaussian_logarithmic_integral_concentration N hn0 K r hK hNK hrl hru hdegree
    (Real.log N) hlog (Real.log N / 32) (logarithmicTolerance N / 2)
    ((N : ℝ) ^ (-1 / 16 : ℝ)) (logarithmicMomentCutoff 16 N)
    (by linarith) (by positivity) (Real.rpow_pos_of_pos hNr _) hD
  have hmoment : (32 * Real.log N) ^ (2 * Real.log N) ≤
      (16 * (2 * Real.log N)) ^ (12 * Real.log N) := by
    rw [show 16 * (2 * Real.log N) = 32 * Real.log N by ring]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hbudget :
      (gaussianOccupationVarianceConstant K / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
        (32 * Real.log N) ^ (2 * Real.log N) / (logarithmicMomentCutoff 16 N ^ 2) ^ Real.log N +
        4 * (Real.log N / 32) ^ 2 * (gaussianOccupationVarianceConstant K / Real.sqrt N) /
          (logarithmicTolerance N / 2) ^ 2 ≤
      (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
    apply le_trans _ (logarithmic_failure_le (A := 16) hlog (by norm_num) hH.le)
    gcongr
  have hprob := (measure_mono (μ := gaussianCoefficientMeasure (N + 1))
    (show {g | logarithmicTolerance N <
        |logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) - circularLogMean|} ⊆ _
      from fun _ hg => lt_of_le_of_lt hsmallThreshold hg)).trans h
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal (show
    Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
        (gaussianOccupationVarianceConstant K / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
        (32 * Real.log N) ^ (2 * Real.log N) / (logarithmicMomentCutoff 16 N ^ 2) ^ Real.log N +
        4 * (Real.log N / 32) ^ 2 * (gaussianOccupationVarianceConstant K / Real.sqrt N) /
          (logarithmicTolerance N / 2) ^ 2 ≤
      Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
        (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) by linarith))
  have hnneg : 0 ≤ Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
      (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

/-- Every fixed Gaussian energy exponential is eventually smaller than the
polynomial occupation failure scale. -/
theorem eventually_gaussian_energy_le_logarithmic_power (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) ≤ (N : ℝ) ^ (-3 / 8 : ℝ) := by
  let c : ℝ := 3 / (32 * Real.exp (6 * K))
  have hc : 0 < c := by dsimp [c]; positivity
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 8) c hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN hsmall
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hn (3 / 8 : ℝ)
  have hh : Real.exp (-c * N) ≤ 1 / (N : ℝ) ^ (3 / 8 : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    simpa only [Function.comp_def, mul_comm] using hsmall.le
  convert hh using 1
  · congr 1
    dsimp [c]
    ring
  · rw [show (-3 / 8 : ℝ) = -(3 / 8 : ℝ) by ring, Real.rpow_neg hn.le, one_div]

/-- A pure polynomial failure bound, uniform in each fixed radial annulus. -/
theorem eventually_gaussian_logarithmic_concentration_power (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
      (gaussianCoefficientMeasure (N + 1)).real {g | logarithmicTolerance N <
        |logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        (2 * gaussianOccupationConstant K + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  filter_upwards [eventually_gaussian_logarithmic_concentration K hK,
    eventually_gaussian_energy_le_logarithmic_power K] with N hN henergy
  intro r hrl hru
  have h := hN r hrl hru
  linarith

end Erdos522
