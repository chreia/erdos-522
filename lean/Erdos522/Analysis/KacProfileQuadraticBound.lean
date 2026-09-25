/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.KacVarianceIntegral
import Mathlib.Probability.Moments.SubGaussian

/-!
# A global quadratic bound for the Kac log-variance profile

Centering uniform measure on the unit interval represents the nonlinear
part of the profile as half a log moment-generating function. Hoeffding's
lemma gives the bound with constant `1/4`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Erdos522

/-- The uniform unit-interval coordinate has mean one half. -/
theorem integral_unitInterval_coordinate : (∫ t : ℝ, t ∂unitIntervalMeasure) = 1 / 2 := by
  change (∫ t in Ico (0 : ℝ) 1, t) = 1 / 2
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_id]
  norm_num

theorem integrable_unitInterval_coordinate : Integrable (fun t : ℝ => t) unitIntervalMeasure :=
  continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self

/-- The centered uniform coordinate has the exact Hoeffding proxy `1/4`. -/
theorem hasSubgaussianMGF_centered_unitInterval :
    HasSubgaussianMGF (fun t : ℝ => t - 1 / 2) (1 / 4) unitIntervalMeasure := by
  have hb : ∀ᵐ t ∂unitIntervalMeasure, t - 1 / 2 ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    constructor <;> linarith [ht.1, ht.2]
  have hm : (∫ t : ℝ, t - 1 / 2 ∂unitIntervalMeasure) = 0 := by
    rw [integral_sub integrable_unitInterval_coordinate (integrable_const _),
      integral_unitInterval_coordinate]
    simp
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (by fun_prop) hb hm
  convert h using 1
  norm_num

/-- The moment-generating function of the centered uniform coordinate is at least one. -/
theorem one_le_mgf_centered_unitInterval (s : ℝ) :
    1 ≤ mgf (fun t : ℝ => t - 1 / 2) unitIntervalMeasure s := by
  have hc : Integrable (fun t : ℝ => t - 1 / 2) unitIntervalMeasure :=
    integrable_unitInterval_coordinate.sub (integrable_const (1 / 2 : ℝ))
  have hint : Integrable (fun t : ℝ => s * (t - 1 / 2) + 1) unitIntervalMeasure :=
    (hc.const_mul s).add (integrable_const 1)
  calc
    1 = ∫ t : ℝ, s * (t - 1 / 2) + 1 ∂unitIntervalMeasure := by
      rw [integral_add (hc.const_mul s) (integrable_const 1), integral_const_mul,
        integral_sub integrable_unitInterval_coordinate (integrable_const _), integral_unitInterval_coordinate]
      simp
    _ ≤ _ := integral_mono_ae hint (hasSubgaussianMGF_centered_unitInterval.integrable_exp_mul s)
      (ae_of_all _ fun t => Real.add_one_le_exp _)

/-- The variance profile is the centered uniform moment-generating function times `exp x`. -/
theorem kacVarianceProfile_eq_centered_mgf (x : ℝ) :
    kacVarianceProfile x = Real.exp x * mgf (fun t : ℝ => t - 1 / 2) unitIntervalMeasure (2 * x) := by
  rw [kacVarianceProfile_eq_integral, mgf, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    change Real.exp (2 * x * t) = Real.exp x * Real.exp (2 * x * (t - 1 / 2))
    rw [← Real.exp_add]
    congr 1
    ring

/-- The nonlinear part of the logarithmic profile is between zero and `x²/4`. -/
theorem kacLogVarianceProfile_quadratic_bound (x : ℝ) :
    0 ≤ kacLogVarianceProfile x - x / 2 ∧
      kacLogVarianceProfile x - x / 2 ≤ x ^ 2 / 4 := by
  let M := mgf (fun t : ℝ => t - 1 / 2) unitIntervalMeasure (2 * x)
  have hM : 1 ≤ M := one_le_mgf_centered_unitInterval (2 * x)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hu : M ≤ Real.exp (x ^ 2 / 2) := by
    have h := hasSubgaussianMGF_centered_unitInterval.mgf_le (2 * x)
    have he : ((1 / 4 : ℝ≥0) : ℝ) * (2 * x) ^ 2 / 2 = x ^ 2 / 2 := by
      norm_num
      ring
    simpa only [he] using h
  have hlo := Real.log_nonneg hM
  have hhi := Real.log_le_log hMpos hu
  rw [Real.log_exp] at hhi
  have he : kacLogVarianceProfile x - x / 2 = (1 / 2 : ℝ) * Real.log M := by
    rw [kacLogVarianceProfile, kacVarianceProfile_eq_centered_mgf,
      Real.log_mul (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
    ring
  rw [he]
  constructor <;> linarith

/-- The error of the linear profile approximation has an explicit global bound. -/
theorem abs_kacLogVarianceProfile_sub_half_le (x : ℝ) :
    |kacLogVarianceProfile x - x / 2| ≤ x ^ 2 / 4 := by
  rw [abs_of_nonneg (kacLogVarianceProfile_quadratic_bound x).1]
  exact (kacLogVarianceProfile_quadratic_bound x).2

end Erdos522
