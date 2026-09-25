/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Geometric means of complex-valued functions

For a nonzero function with integrable logarithmic modulus, the geometric
mean is the exponential of the average logarithmic modulus. Jensen's
inequality compares its square with the mean square modulus.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- The exponential of the average logarithmic modulus. -/
def geometricMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℂ) : ℝ :=
  Real.exp (⨍ x, Real.log ‖f x‖ ∂μ)

theorem geometricMean_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℂ) : 0 < geometricMean μ f := Real.exp_pos _

/-- Integration preserves almost-everywhere inequalities between integrable
functions after normalization by the total mass. -/
theorem average_mono_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) : (⨍ x, f x ∂μ) ≤ ⨍ x, g x ∂μ := by
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg)
    (inv_nonneg.mpr measureReal_nonneg)

/-- An additive logarithmic comparison becomes a multiplicative comparison
of geometric means. -/
theorem geometricMean_le_exp_mul_of_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℂ) (B : ℝ)
    (h : (⨍ x, Real.log ‖g x‖ ∂μ) ≤ B + ⨍ x, Real.log ‖f x‖ ∂μ) :
    geometricMean μ g ≤ Real.exp B * geometricMean μ f := by
  simpa only [geometricMean, Real.exp_add] using Real.exp_le_exp.mpr h

/-- The geometric mean respects a constant modulus bound. -/
theorem geometricMean_le_of_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (f : Ω → ℂ)
    (hf : Integrable (fun x => Real.log ‖f x‖) μ) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ᵐ x ∂μ, f x ≠ 0) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    geometricMean μ f ≤ M := by
  have hlog : ∀ᵐ x ∂μ, Real.log ‖f x‖ ≤ Real.log M := by
    filter_upwards [hzero, hbound] with x hx hb
    exact Real.log_le_log (norm_pos_iff.mpr hx) hb
  have h := average_mono_of_integrable hf (integrable_const (Real.log M)) hlog
  rw [average_const] at h
  simpa only [geometricMean, Real.exp_log hM] using Real.exp_le_exp.mpr h

/-- Jensen's inequality bounds the square of the geometric mean by the
average square modulus. -/
theorem geometricMean_sq_le_average_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (f : Ω → ℂ)
    (hf : Integrable (fun x => Real.log ‖f x‖) μ)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) (hzero : ∀ᵐ x ∂μ, f x ≠ 0) :
    geometricMean μ f ^ 2 ≤ ⨍ x, ‖f x‖ ^ 2 ∂μ := by
  have heq : (fun x => Real.exp (2 * Real.log ‖f x‖)) =ᵐ[μ] fun x => ‖f x‖ ^ 2 := by
    filter_upwards [hzero] with x hx
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (norm_pos_iff.mpr hx)]
  have hexp : Integrable (fun x => Real.exp (2 * Real.log ‖f x‖)) μ :=
    hf2.congr heq.symm
  have h := convexOn_exp.map_average_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) (hf.const_mul 2) hexp
  rw [average_const_mul, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul] at h
  exact h.trans_eq (average_congr heq)

end Erdos522
