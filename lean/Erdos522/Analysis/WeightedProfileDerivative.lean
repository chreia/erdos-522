/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Derivatives of weighted variance profiles

The limiting variance for the weights `c₀ = 1`, `cₖ = k^τ` is the Laplace
transform of `t^(2τ)` on the unit interval.  The integrability threshold is
`τ > -1/2`.  Differentiation under the integral gives the logarithmic profile
as a ratio of its first moment to its mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Erdos522

/-- The variance profile associated with power weights. -/
def weightedVarianceProfile (τ x : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ) * Real.exp (2 * x * t)

/-- The logarithmic variance profile associated with power weights. -/
def weightedLogVarianceProfile (τ x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (weightedVarianceProfile τ x)

/-- The weighted exponential kernel is integrable throughout the natural range. -/
theorem integrableOn_weightedVarianceKernel {τ : ℝ} (hτ : -1 / 2 < τ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (2 * τ) * Real.exp (2 * x * t)) (Ioc 0 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2 * τ)).mul_continuousOn
    (by fun_prop)

/-- Every weighted variance profile is strictly positive. -/
theorem weightedVarianceProfile_pos {τ : ℝ} (hτ : -1 / 2 < τ) (x : ℝ) :
    0 < weightedVarianceProfile τ x := by
  rw [weightedVarianceProfile, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (integrableOn_weightedVarianceKernel hτ x))
  · intro t ht
    exact mul_pos (Real.rpow_pos_of_pos ht.1 _) (Real.exp_pos _)
  · norm_num

/-- The total weight on the unit interval has an elementary exact value. -/
theorem weightedVarianceProfile_zero {τ : ℝ} (hτ : -1 / 2 < τ) :
    weightedVarianceProfile τ 0 = 1 / (2 * τ + 1) := by
  simp only [weightedVarianceProfile, mul_zero, zero_mul, Real.exp_zero, mul_one]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < 2 * τ))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : 2 * τ + 1 ≠ 0), sub_zero]

/-- Differentiation of the weighted variance is differentiation of its exponential kernel. -/
theorem hasDerivAt_weightedVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) (x : ℝ) :
    HasDerivAt (weightedVarianceProfile τ)
      (2 * ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * x * t)) x := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ := fun y t => t ^ (2 * τ) * Real.exp (2 * y * t)
  let F' : ℝ → ℝ → ℝ := fun y t => t ^ (2 * τ) * Real.exp (2 * y * t) * (2 * t)
  let bound : ℝ → ℝ := fun t => (2 * Real.exp (2 * (|x| + 1))) * t ^ (2 * τ)
  have hpow : Integrable (fun t : ℝ => t ^ (2 * τ)) μ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2 * τ))
  have hFmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) μ := by
    filter_upwards with y
    exact (integrableOn_weightedVarianceKernel hτ y).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' x) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [F']
    fun_prop
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ Metric.ball x 1, ‖F' y t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y hy
    have hyx : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have hyabs : |y| ≤ |x| + 1 := by
      calc
        |y| = |y - x + x| := by ring_nf
        _ ≤ |y - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    have hyt : y * t ≤ |x| + 1 := by
      calc
        y * t ≤ |y| * t := mul_le_mul_of_nonneg_right (le_abs_self y) ht.1.le
        _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg y)
        _ ≤ |x| + 1 := by simpa using hyabs
    have hexp : Real.exp (2 * y * t) ≤ Real.exp (2 * (|x| + 1)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hp : 0 ≤ t ^ (2 * τ) := Real.rpow_nonneg ht.1.le _
    have hnonneg : 0 ≤ F' y t :=
      mul_nonneg (mul_nonneg hp (Real.exp_pos _).le) (mul_nonneg (by norm_num) ht.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp [F', bound]
    calc
      t ^ (2 * τ) * Real.exp (2 * y * t) * (2 * t) ≤
          t ^ (2 * τ) * Real.exp (2 * (|x| + 1)) * 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hp)
          (by linarith [ht.2]) (by linarith [ht.1]) (mul_nonneg hp (Real.exp_pos _).le)
      _ = (2 * Real.exp (2 * (|x| + 1))) * t ^ (2 * τ) := by ring
  have hdiff : ∀ᵐ t ∂μ, ∀ y ∈ Metric.ball x 1, HasDerivAt (F · t) (F' y t) y := by
    filter_upwards with t
    intro y _
    simpa only [F, F', mul_one, one_mul, mul_assoc, id_eq] using
      ((((hasDerivAt_id y).const_mul 2).mul_const t).exp.const_mul (t ^ (2 * τ)))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)) hFmeas
    (integrableOn_weightedVarianceKernel hτ x) hF'meas hbound
    (hpow.const_mul (2 * Real.exp (2 * (|x| + 1))))) hdiff
  have hint : (∫ t, F' x t ∂μ) =
      2 * ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * x * t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp [F']
    rw [Real.rpow_add ht.1, Real.rpow_one]
    ring
  rw [hint] at hd
  exact hd.2

/-- The derivative of the logarithmic profile is its normalized first moment. -/
theorem hasDerivAt_weightedLogVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) (x : ℝ) :
    HasDerivAt (weightedLogVarianceProfile τ)
      ((∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * x * t)) /
        weightedVarianceProfile τ x) x := by
  have h := ((hasDerivAt_weightedVarianceProfile hτ x).log
    (weightedVarianceProfile_pos hτ x).ne').const_mul (1 / 2 : ℝ)
  unfold weightedLogVarianceProfile
  convert h using 1
  ring

/-- At the unit-circle scale, the logarithmic derivative is an elementary ratio. -/
theorem hasDerivAt_weightedLogVarianceProfile_zero {τ : ℝ} (hτ : -1 / 2 < τ) :
    HasDerivAt (weightedLogVarianceProfile τ) ((2 * τ + 1) / (2 * τ + 2)) 0 := by
  have h := hasDerivAt_weightedLogVarianceProfile hτ 0
  have hm : (∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * 0 * t)) =
      1 / (2 * τ + 2) := by
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by linarith : -1 < 2 * τ + 1))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : 2 * τ + 1 + 1 ≠ 0), sub_zero]
    congr 1
    ring
  rw [hm, weightedVarianceProfile_zero hτ] at h
  convert h using 1
  field_simp

/-- Continuity of the weighted variance profile. -/
theorem continuous_weightedVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) :
    Continuous (weightedVarianceProfile τ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_weightedVarianceProfile hτ x).continuousAt

/-- Continuity of the logarithmic variance profile. -/
theorem continuous_weightedLogVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) :
    Continuous (weightedLogVarianceProfile τ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_weightedLogVarianceProfile hτ x).continuousAt

/-- The exact derivative as a quotient of weighted moments. -/
theorem deriv_weightedLogVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) (x : ℝ) :
    deriv (weightedLogVarianceProfile τ) x =
      (∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * x * t)) /
        weightedVarianceProfile τ x :=
  (hasDerivAt_weightedLogVarianceProfile hτ x).deriv

/-- The exact central slope of the logarithmic variance profile. -/
theorem deriv_weightedLogVarianceProfile_zero {τ : ℝ} (hτ : -1 / 2 < τ) :
    deriv (weightedLogVarianceProfile τ) 0 = (2 * τ + 1) / (2 * τ + 2) :=
  (hasDerivAt_weightedLogVarianceProfile_zero hτ).deriv

/-- The first moment is another variance profile with the weight exponent shifted by one half. -/
theorem weightedVarianceProfile_add_half (τ x : ℝ) :
    weightedVarianceProfile (τ + 1 / 2) x =
      ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * τ + 1) * Real.exp (2 * x * t) := by
  unfold weightedVarianceProfile
  congr 1
  funext t
  congr 2
  ring

/-- The logarithmic derivative is continuous on the entire real axis. -/
theorem continuous_deriv_weightedLogVarianceProfile {τ : ℝ} (hτ : -1 / 2 < τ) :
    Continuous (deriv (weightedLogVarianceProfile τ)) := by
  have hquot : Continuous (fun x => weightedVarianceProfile (τ + 1 / 2) x /
      weightedVarianceProfile τ x) :=
    (continuous_weightedVarianceProfile (by linarith : -1 / 2 < τ + 1 / 2)).div
      (continuous_weightedVarianceProfile hτ) (fun x => (weightedVarianceProfile_pos hτ x).ne')
  convert hquot using 1
  funext x
  rw [deriv_weightedLogVarianceProfile hτ x, weightedVarianceProfile_add_half]

end Erdos522
