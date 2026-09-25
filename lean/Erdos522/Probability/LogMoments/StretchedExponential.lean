/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Moments controlled by stretched exponentials

An exponential integral of a fractional power controls all nonnegative real moments.
-/

noncomputable section

open MeasureTheory

namespace Erdos522
namespace LogMoments

theorem abs_rpow_le_stretchedExponential (x : ℝ) {β t p : ℝ}
    (hβ : 0 < β) (ht : 0 < t) (hp : 0 ≤ p) :
    |x| ^ p ≤ (β * p / t) ^ (β * p) * Real.exp (t * |x| ^ β⁻¹) := by
  have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (|x| ^ β⁻¹)
    (t := t) (p := β * p) (mul_nonneg hβ.le hp) ht.ne'
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _), abs_of_pos ht,
    ← Real.rpow_mul (abs_nonneg x), inv_mul_cancel_left₀ hβ.ne'] at h
  exact h

theorem integrable_abs_rpow_of_stretchedExponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {β t p : ℝ}
    (hX : Measurable X) (hβ : 0 < β) (ht : 0 < t) (hp : 0 ≤ p)
    (hI : Integrable (fun ω => Real.exp (t * |X ω| ^ β⁻¹)) μ) :
    Integrable (fun ω => |X ω| ^ p) μ := by
  have hm : Measurable (fun ω => |X ω| ^ p) := by
    simpa only [Real.norm_eq_abs] using hX.norm.pow_const p
  apply (hI.const_mul ((β * p / t) ^ (β * p))).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
    abs_rpow_le_stretchedExponential (X ω) hβ ht hp

theorem integral_abs_rpow_le_stretchedExponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {β t p : ℝ}
    (hX : Measurable X) (hβ : 0 < β) (ht : 0 < t) (hp : 0 ≤ p)
    (hI : Integrable (fun ω => Real.exp (t * |X ω| ^ β⁻¹)) μ) :
    (∫ ω, |X ω| ^ p ∂μ) ≤
      (β * p / t) ^ (β * p) * ∫ ω, Real.exp (t * |X ω| ^ β⁻¹) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono
    (integrable_abs_rpow_of_stretchedExponential hX hβ ht hp hI)
    (hI.const_mul _) (fun ω => abs_rpow_le_stretchedExponential (X ω) hβ ht hp)

theorem integral_abs_rpow_le_of_stretchedExponential_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {β t p B : ℝ}
    (hX : Measurable X) (hβ : 1 ≤ β) (ht : 0 < t) (hp : 1 ≤ p) (hB : 1 ≤ B)
    (hI : Integrable (fun ω => Real.exp (t * |X ω| ^ β⁻¹)) μ)
    (hbound : (∫ ω, Real.exp (t * |X ω| ^ β⁻¹) ∂μ) ≤ B) :
    (∫ ω, |X ω| ^ p ∂μ) ≤ (β * B / t * p) ^ (β * p) := by
  have hβp : 1 ≤ β * p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hp)]
  have hc : 0 ≤ β * p / t := by positivity
  calc
    (∫ ω, |X ω| ^ p ∂μ) ≤
        (β * p / t) ^ (β * p) * ∫ ω, Real.exp (t * |X ω| ^ β⁻¹) ∂μ :=
      integral_abs_rpow_le_stretchedExponential hX (zero_lt_one.trans_le hβ) ht
        (zero_le_one.trans hp) hI
    _ ≤ (β * p / t) ^ (β * p) * B :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hc _)
    _ ≤ (β * p / t) ^ (β * p) * B ^ (β * p) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc _)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hβp
    _ = (β * B / t * p) ^ (β * p) := by
      rw [← Real.mul_rpow hc (zero_le_one.trans hB)]
      congr 1
      ring

end LogMoments
end Erdos522
