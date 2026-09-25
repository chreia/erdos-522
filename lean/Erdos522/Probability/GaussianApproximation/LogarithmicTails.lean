/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.OccupationDeviation
import Erdos522.Probability.GaussianApproximation.ClippedLogarithms
import Erdos522.Probability.ExponentialTailIntegral
import Erdos522.Analysis.LogarithmicClipping

/-!
# Logarithmic clipping tails of the circular Gaussian

The disk law controls the negative tail, and unit quadratic energy controls
the positive tail. Each clipping tail has expectation at most `exp (-2T)/2`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set WithLp

namespace Erdos522

/-- The circular Gaussian has unit quadratic energy. -/
theorem integral_norm_sq_circularGaussian : (∫ x, ‖x‖ ^ 2 ∂circularGaussian) = 1 := by
  rw [← measurePreserving_circularGaussian_coordinates.symm.integral_comp
    valueCartesianCoordinates.symm.measurableEmbedding]
  have hnorm (p : ℝ × ℝ) : ‖valueCartesianCoordinates.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  simp_rw [hnorm]
  have hI : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (1 / 2)) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1 / 2) 2).integrable_sq
  have hsq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2)) = (1 / 2 : ℝ) := by
    have h := variance_eq_integral (μ := gaussianReal 0 (1 / 2)) (X := fun x : ℝ => x) measurable_id.aemeasurable
    simpa only [variance_fun_id_gaussianReal, integral_id_gaussianReal, sub_zero, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using h.symm
  rw [integral_add (hI.comp_fst _) (hI.comp_snd _), integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
  simp only [probReal_univ, one_smul]
  rw [hsq]
  norm_num

/-- Quadratic energy is integrable for the circular Gaussian. -/
theorem integrable_norm_sq_circularGaussian : Integrable (fun x => ‖x‖ ^ 2) circularGaussian := by
  unfold circularGaussian
  exact (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 (Matrix.diagonal fun _ : Fin 2 => (1 / 2 : ℝ)))).norm.integrable_sq

/-- The positive amount beyond a logarithmic clipping level. -/
def positiveGaussianLogTail (T : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  max (Real.log ‖x‖ - T) 0

/-- The negative amount beyond a logarithmic clipping level. -/
def negativeGaussianLogTail (T : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  max (-Real.log ‖x‖ - T) 0

/-- The Gaussian disk law gives an exponential bound for every negative logarithmic tail. -/
theorem measure_negativeGaussianLogTail_le (T : ℝ) (s : ℝ) (hs : 0 < s) :
    circularGaussian {x | s ≤ negativeGaussianLogTail T x} ≤
      ENNReal.ofReal (Real.exp (-2 * T) * Real.exp (-2 * s)) := by
  have hsubset : {x | s ≤ negativeGaussianLogTail T x} ⊆ closedBall 0 (Real.exp (-(T + s))) := by
    intro x hx
    change s ≤ max (-Real.log ‖x‖ - T) 0 at hx
    have hlog : s ≤ -Real.log ‖x‖ - T := by
      rcases le_max_iff.mp hx with h | h
      · exact h
      · linarith
    rw [mem_closedBall, dist_zero_right]
    by_cases hx0 : x = 0
    · simpa only [hx0, norm_zero] using (Real.exp_pos (-(T + s))).le
    · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hx0)).mp (by linarith)
  have hreal := circularGaussian_real_closedBall_le_sq (Real.exp (-(T + s))) (Real.exp_pos _).le
  have heq : Real.exp (-(T + s)) ^ 2 = Real.exp (-2 * T) * Real.exp (-2 * s) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hreal
  exact (measure_mono hsubset).trans
    (by
      rw [← ofReal_measureReal (μ := circularGaussian)]
      exact ENNReal.ofReal_le_ofReal hreal)

/-- Markov's inequality at unit quadratic energy gives the same positive-tail bound. -/
theorem measure_positiveGaussianLogTail_le (T : ℝ) (hT : 0 ≤ T) (s : ℝ) (hs : 0 < s) :
    circularGaussian {x | s ≤ positiveGaussianLogTail T x} ≤
      ENNReal.ofReal (Real.exp (-2 * T) * Real.exp (-2 * s)) := by
  have hsubset : {x | s ≤ positiveGaussianLogTail T x} ⊆
      {x | Real.exp (2 * (T + s)) ≤ ‖x‖ ^ 2} := by
    intro x hx
    change s ≤ max (Real.log ‖x‖ - T) 0 at hx
    have hlog : s ≤ Real.log ‖x‖ - T := by
      rcases le_max_iff.mp hx with h | h
      · exact h
      · linarith
    have hx0 : x ≠ 0 := by intro h; simp [h] at hlog; linarith
    have hnorm : Real.exp (T + s) ≤ ‖x‖ :=
      (Real.le_log_iff_exp_le (norm_pos_iff.mpr hx0)).mp (by linarith)
    have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hnorm 2
    have heq : Real.exp (T + s) ^ 2 = Real.exp (2 * (T + s)) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    rwa [heq] at hpow
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := circularGaussian)
    (f := fun x => ‖x‖ ^ 2) (ae_of_all _ fun x => sq_nonneg _)
    integrable_norm_sq_circularGaussian (Real.exp (2 * (T + s)))
  rw [integral_norm_sq_circularGaussian] at hmarkov
  have hreal : circularGaussian.real {x | Real.exp (2 * (T + s)) ≤ ‖x‖ ^ 2} ≤
      Real.exp (-2 * T) * Real.exp (-2 * s) := by
    have h : circularGaussian.real {x | Real.exp (2 * (T + s)) ≤ ‖x‖ ^ 2} ≤
        1 / Real.exp (2 * (T + s)) :=
      (le_div_iff₀ (Real.exp_pos (2 * (T + s)))).mpr (by nlinarith [hmarkov])
    refine h.trans_eq ?_
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  exact (measure_mono hsubset).trans
    (by
      rw [← ofReal_measureReal (μ := circularGaussian)]
      exact ENNReal.ofReal_le_ofReal hreal)

/-- Both Gaussian clipping tails are integrable and have the exact half-exponential budget. -/
theorem gaussian_log_clipping_tail_bounds (T : ℝ) (hT : 0 ≤ T) :
    Integrable (positiveGaussianLogTail T) circularGaussian ∧
    Integrable (negativeGaussianLogTail T) circularGaussian ∧
    (∫ x, positiveGaussianLogTail T x ∂circularGaussian) ≤ Real.exp (-2 * T) / 2 ∧
    (∫ x, negativeGaussianLogTail T x ∂circularGaussian) ≤ Real.exp (-2 * T) / 2 := by
  have hp := integrable_and_integral_le_of_exponential_tail circularGaussian (positiveGaussianLogTail T)
    (by unfold positiveGaussianLogTail; fun_prop) (fun _ => le_max_right _ _)
    (Real.exp (-2 * T)) 2 (Real.exp_pos _).le (by norm_num)
    (fun s hs => measure_positiveGaussianLogTail_le T hT s hs)
  have hn := integrable_and_integral_le_of_exponential_tail circularGaussian (negativeGaussianLogTail T)
    (by unfold negativeGaussianLogTail; fun_prop) (fun _ => le_max_right _ _)
    (Real.exp (-2 * T)) 2 (Real.exp_pos _).le (by norm_num)
    (fun s hs => measure_negativeGaussianLogTail_le T s hs)
  exact ⟨hp.1, hn.1, hp.2, hn.2⟩

/-- The circular Gaussian assigns zero probability to the origin. -/
theorem circularGaussian_ae_ne_zero : ∀ᵐ x ∂circularGaussian, x ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  change circularGaussian {0} = 0
  apply (measureReal_eq_zero_iff).mp
  simpa only [closedBall_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero, Real.exp_zero, sub_self]
    using circularGaussian_real_closedBall 0 (by norm_num)

/-- The circular Gaussian logarithm is integrable. -/
theorem integrable_log_norm_circularGaussian :
    Integrable (fun x => Real.log ‖x‖) circularGaussian := by
  obtain ⟨hp, hn, _, _⟩ := gaussian_log_clipping_tail_bounds 0 (by norm_num)
  convert hp.sub hn using 1
  ext x
  simp only [positiveGaussianLogTail, negativeGaussianLogTail, sub_zero, Pi.sub_apply]
  exact (max_zero_sub_max_neg_zero_eq_self _).symm

/-- The circular Gaussian logarithmic mean. -/
def circularLogMean : ℝ := ∫ x, Real.log ‖x‖ ∂circularGaussian

/-- The two tails exactly describe the absolute Gaussian clipping error away from the origin. -/
theorem abs_log_norm_sub_clip_eq_tails (T : ℝ) (hT : 0 ≤ T)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    |Real.log ‖x‖ - clippedLogarithm T ‖x‖| =
      positiveGaussianLogTail T x + negativeGaussianLogTail T x := by
  rw [clippedLogarithm, ite_eq_right (not_le.mpr (norm_pos_iff.mpr hx))]
  unfold positiveGaussianLogTail negativeGaussianLogTail
  by_cases hlo : Real.log ‖x‖ ≤ -T
  · rw [min_eq_right (by linarith : Real.log ‖x‖ ≤ T), max_eq_left hlo,
      abs_of_nonpos (by linarith : Real.log ‖x‖ - -T ≤ 0),
      max_eq_right (by linarith : Real.log ‖x‖ - T ≤ 0),
      max_eq_left (by linarith : 0 ≤ -Real.log ‖x‖ - T)]
    ring
  · have hlo' : -T ≤ Real.log ‖x‖ := le_of_lt (lt_of_not_ge hlo)
    by_cases hhi : Real.log ‖x‖ ≤ T
    · rw [min_eq_right hhi, max_eq_right hlo', sub_self, abs_zero,
        max_eq_right (by linarith : Real.log ‖x‖ - T ≤ 0),
        max_eq_right (by linarith : -Real.log ‖x‖ - T ≤ 0), add_zero]
    · have hhi' : T ≤ Real.log ‖x‖ := le_of_lt (lt_of_not_ge hhi)
      rw [min_eq_left hhi', max_eq_right (by linarith : -T ≤ T),
        abs_of_nonneg (sub_nonneg.mpr hhi'), max_eq_left (sub_nonneg.mpr hhi'),
        max_eq_right (by linarith : -Real.log ‖x‖ - T ≤ 0), add_zero]

/-- The clipped circular Gaussian mean has error at most `exp (-2T)`. -/
theorem abs_circularLogMean_sub_clipped_le (T : ℝ) (hT : 0 ≤ T) :
    |circularLogMean - circularClippedLogMean T| ≤ Real.exp (-2 * T) := by
  obtain ⟨hp, hn, hpbound, hnbound⟩ := gaussian_log_clipping_tail_bounds T hT
  have hc : Integrable (fun x => clippedLogarithm T ‖x‖) circularGaussian := by
    apply (MemLp.of_bound ((measurable_clippedLogarithm T).comp measurable_norm).aestronglyMeasurable T ?_ : MemLp _ 1 _).integrable (by norm_num)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact clippedLogarithm_mem_Icc T ‖x‖ hT
  calc
    _ = |∫ x, Real.log ‖x‖ - clippedLogarithm T ‖x‖ ∂circularGaussian| := by
      rw [integral_sub integrable_log_norm_circularGaussian hc]
      rfl
    _ ≤ ∫ x, |Real.log ‖x‖ - clippedLogarithm T ‖x‖| ∂circularGaussian := abs_integral_le_integral_abs
    _ = ∫ x, positiveGaussianLogTail T x + negativeGaussianLogTail T x ∂circularGaussian := by
      apply integral_congr_ae
      filter_upwards [circularGaussian_ae_ne_zero] with x hx
      exact abs_log_norm_sub_clip_eq_tails T hT x hx
    _ = (∫ x, positiveGaussianLogTail T x ∂circularGaussian) +
        ∫ x, negativeGaussianLogTail T x ∂circularGaussian := integral_add hp hn
    _ ≤ Real.exp (-2 * T) := by linarith

end Erdos522
