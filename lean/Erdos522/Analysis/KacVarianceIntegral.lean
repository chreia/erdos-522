/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.WeightedVarianceLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral formulas for Kac variances

The continuum variance is an exponential integral over the unit interval.
The finite variance is the corresponding sampled integral, including the
constant coefficient exactly.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- The Kac variance profile as a unit-interval exponential integral. -/
theorem kacVarianceProfile_eq_integral (x : ℝ) :
    kacVarianceProfile x = ∫ t, Real.exp (2 * x * t) ∂unitIntervalMeasure := by
  change kacVarianceProfile x = ∫ t in Ico (0 : ℝ) 1, Real.exp (2 * x * t)
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hx : x = 0
  · simp [hx, kacVarianceProfile]
  · rw [intervalIntegral.integral_comp_mul_left Real.exp (mul_ne_zero (by norm_num) hx),
      integral_exp]
    simp only [mul_zero, Real.exp_zero, mul_one, smul_eq_mul, kacVarianceProfile,
      ite_eq_right_iff.mpr (fun h => (hx h).elim), div_eq_mul_inv]
    ring

/-- The continuum exponential kernel is integrable on the unit interval. -/
theorem integrable_kac_exponential (x : ℝ) :
    Integrable (fun t => Real.exp (2 * x * t)) unitIntervalMeasure := by
  exact ((show Continuous (fun t : ℝ => Real.exp (2 * x * t)) by fun_prop).integrableOn_Icc).mono_set
    Ico_subset_Icc_self

/-- A uniform lower bound for the continuum variance over a finite width. -/
theorem exp_neg_two_width_le_kacVarianceProfile {K x : ℝ} (hK : 0 ≤ K) (hx : |x| ≤ K) :
    Real.exp (-2 * K) ≤ kacVarianceProfile x := by
  rw [kacVarianceProfile_eq_integral]
  calc
    _ = ∫ _t, Real.exp (-2 * K) ∂unitIntervalMeasure := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (integrable_kac_exponential x)
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      apply Real.exp_le_exp.mpr
      have hxl : -K ≤ x := (abs_le.mp hx).1
      have hprod := mul_le_mul_of_nonneg_right hxl ht.1
      nlinarith [ht.2.le]

/-- The finite radial variance is one constant term plus a sampled integral. -/
theorem radialVariance_eq_sampled_integral {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    radialVariance N r / N = 1 / (N : ℝ) +
      ∫ t, Real.exp (2 * ((N : ℝ) * Real.log r) * rightEndpointSample N t)
        ∂unitIntervalMeasure := by
  change radialVariance N r / N = 1 / (N : ℝ) +
    ∫ t in Ico (0 : ℝ) 1, Real.exp (2 * ((N : ℝ) * Real.log r) * rightEndpointSample N t)
  rw [integral_rightEndpointSample hN (fun t => Real.exp (2 * ((N : ℝ) * Real.log r) * t))]
  have heq (j : Fin N) : Real.exp (2 * ((N : ℝ) * Real.log r) * (((j.val : ℝ) + 1) / N)) =
      r ^ (2 * (j.val + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using exp_scaled_log_radius (k := j.val + 1) hN hr
  simp_rw [heq]
  rw [radialVariance, ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, mul_zero, pow_zero, Fin.val_succ, add_div]

end Erdos522
