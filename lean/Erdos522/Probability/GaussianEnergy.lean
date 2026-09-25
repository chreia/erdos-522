/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianQuadraticExponential
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Concentration of weighted Gaussian energy

Independence multiplies the exponential moments of Gaussian squares.
For nonnegative weights of total mass one and maximum at most `W`, the
energy exceeds two with probability at most `exp (-3/(32W))`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Erdos522

/-- The quadratic energy of a Gaussian coefficient vector with deterministic weights. -/
def gaussianWeightedEnergy {n : ℕ} (w : Fin n → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ k, w k * g k ^ 2

private theorem exp_gaussianWeightedEnergy_eq_prod {n : ℕ} (w : Fin n → ℝ) (t : ℝ)
    (g : Fin n → ℝ) :
    Real.exp (t * gaussianWeightedEnergy w g) = ∏ k, Real.exp ((t * w k) * g k ^ 2) := by
  rw [gaussianWeightedEnergy, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  ring

/-- The exponential of the weighted energy is integrable in the subcritical range. -/
theorem integrable_exp_gaussianWeightedEnergy {n : ℕ} (w : Fin n → ℝ) (t : ℝ)
    (ht : ∀ k, t * w k < 1 / 2) :
    Integrable (fun g => Real.exp (t * gaussianWeightedEnergy w g)) (gaussianCoefficientMeasure n) := by
  simp_rw [exp_gaussianWeightedEnergy_eq_prod]
  exact Integrable.fintype_prod_dep (fun k => integrable_exp_mul_sq_gaussianReal (ht k))

/-- Exact independent factorization bounds the exponential moment by its first two cumulants. -/
theorem integral_exp_gaussianWeightedEnergy_le {n : ℕ} (w : Fin n → ℝ) (t : ℝ)
    (ht : ∀ k, 0 ≤ t * w k) (ht' : ∀ k, t * w k ≤ 1 / 4) :
    (∫ g, Real.exp (t * gaussianWeightedEnergy w g) ∂gaussianCoefficientMeasure n) ≤
      Real.exp (t * ∑ k, w k + 2 * t ^ 2 * ∑ k, w k ^ 2) := by
  simp_rw [exp_gaussianWeightedEnergy_eq_prod]
  rw [gaussianCoefficientMeasure, integral_fintype_prod_eq_prod
    (fun k (x : ℝ) => Real.exp ((t * w k) * x ^ 2))]
  calc
    _ ≤ ∏ k, Real.exp (t * w k + 2 * (t * w k) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro k _
        exact integral_nonneg_of_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
      · intro k _
        exact integral_exp_mul_sq_gaussianReal_le (ht k) (ht' k)
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- A maximum weight bounds the squared weight sum. -/
theorem sum_sq_weights_le_max {n : ℕ} (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) {W : ℝ} (hW : ∀ k, w k ≤ W) :
    ∑ k, w k ^ 2 ≤ W := by
  calc
    _ ≤ ∑ k, W * w k := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hW k) (hw k)
    _ = W := by rw [← Finset.mul_sum, hsum, mul_one]

/-- Weighted Gaussian energy has the exponential exceptional-event budget used in the manuscript. -/
theorem gaussianWeightedEnergy_gt_two_le {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    {W : ℝ} (hWpos : 0 < W) (hW : ∀ k, w k ≤ W) :
    gaussianCoefficientMeasure n {g | 2 < gaussianWeightedEnergy w g} ≤
      ENNReal.ofReal (Real.exp (-3 / (32 * W))) := by
  let t : ℝ := 1 / (8 * W)
  have ht : 0 < t := by dsimp [t]; positivity
  have htw (k : Fin n) : 0 ≤ t * w k := mul_nonneg ht.le (hw k)
  have htw' (k : Fin n) : t * w k ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (hW k) ht.le
    have he : t * W = 1 / 8 := by dsimp [t]; field_simp
    rw [he] at h
    linarith
  have hI := integrable_exp_gaussianWeightedEnergy w t (fun k => lt_of_le_of_lt (htw' k) (by norm_num))
  have hmgf := integral_exp_gaussianWeightedEnergy_le w t htw htw'
  rw [hsum, mul_one] at hmgf
  have hsq := sum_sq_weights_le_max w hw hsum hW
  have hmgf' : (∫ g, Real.exp (t * gaussianWeightedEnergy w g) ∂gaussianCoefficientMeasure n) ≤
      Real.exp (t + 2 * t ^ 2 * W) := hmgf.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianCoefficientMeasure n) (f := fun g => Real.exp (t * gaussianWeightedEnergy w g))
    (ae_of_all _ fun _ => (Real.exp_pos _).le) hI (Real.exp (2 * t))
  have hprob : (gaussianCoefficientMeasure n).real
      {g | Real.exp (2 * t) ≤ Real.exp (t * gaussianWeightedEnergy w g)} ≤
        Real.exp (-3 / (32 * W)) := by
    have hquot : (gaussianCoefficientMeasure n).real
        {g | Real.exp (2 * t) ≤ Real.exp (t * gaussianWeightedEnergy w g)} ≤
          Real.exp (t + 2 * t ^ 2 * W) / Real.exp (2 * t) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by nlinarith [hmarkov.trans hmgf'])
    refine hquot.trans_eq ?_
    rw [← Real.exp_sub]
    congr 1
    dsimp [t]
    field_simp
    ring
  have hsub : {g | 2 < gaussianWeightedEnergy w g} ⊆
      {g | Real.exp (2 * t) ≤ Real.exp (t * gaussianWeightedEnergy w g)} := by
    intro g hg
    change 2 < gaussianWeightedEnergy w g at hg
    exact Real.exp_le_exp.mpr (by nlinarith [ht])
  exact (measure_mono hsub).trans (by
    rw [← ofReal_measureReal (μ := gaussianCoefficientMeasure n)]
    exact ENNReal.ofReal_le_ofReal hprob)

end Erdos522
