/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausLaw
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Circular second moments of Steinhaus coefficients

Fourier orthogonality gives a vanishing complex second moment. Together
with unit modulus, this identifies the real covariance as half the identity.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- Every nonconstant Fourier character has zero Haar integral. -/
theorem integral_circle_character_eq_zero {n : ℤ} (hn : n ≠ 0) :
    (∫ θ : AddCircle (1 : ℝ), fourier n θ ∂AddCircle.haarAddCircle) = 0 :=
  integral_eq_zero_of_add_right_eq_neg
    (fourier_add_half_inv_index hn (by norm_num : (0 : ℝ) < 1))

/-- Every natural power of a Steinhaus coefficient is integrable. -/
theorem integrable_steinhaus_pow (n : ℕ) :
    Integrable (fun z : ℂ => z ^ n) steinhausMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_norm_steinhaus_eq_one] with z hz
  simp only [norm_pow, hz, one_pow, le_refl]

/-- Circular symmetry makes the complex second moment vanish. -/
theorem integral_sq_steinhaus : (∫ z : ℂ, z ^ 2 ∂steinhausMeasure) = 0 := by
  rw [steinhausMeasure, integral_map (fourier 1).continuous.measurable.aemeasurable (by fun_prop)]
  have heq (θ : AddCircle (1 : ℝ)) : fourier 1 θ ^ 2 = fourier 2 θ := by
    rw [sq]
    exact (fourier_add (m := 1) (n := 1)).symm
  simp_rw [heq]
  exact integral_circle_character_eq_zero (by norm_num)

/-- Each real coordinate square is integrable. -/
theorem integrable_steinhaus_re_sq :
    Integrable (fun z : ℂ => z.re ^ 2) steinhausMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_norm_steinhaus_eq_one] with z hz
  have h := Complex.abs_re_le_norm z
  rw [hz] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr h

theorem integrable_steinhaus_im_sq :
    Integrable (fun z : ℂ => z.im ^ 2) steinhausMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_norm_steinhaus_eq_one] with z hz
  have h := Complex.abs_im_le_norm z
  rw [hz] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr h

/-- The two coordinate second moments add to one. -/
theorem integral_steinhaus_coordinate_sq_sum :
    (∫ z : ℂ, z.re ^ 2 ∂steinhausMeasure) + (∫ z : ℂ, z.im ^ 2 ∂steinhausMeasure) = 1 := by
  rw [← integral_add integrable_steinhaus_re_sq integrable_steinhaus_im_sq]
  calc
    _ = ∫ z : ℂ, ‖z‖ ^ 2 ∂steinhausMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
    _ = 1 := by simpa only [Real.rpow_natCast] using integral_norm_rpow_steinhaus (2 : ℕ)

/-- The two coordinate second moments coincide. -/
theorem integral_steinhaus_coordinate_sq_eq :
    (∫ z : ℂ, z.re ^ 2 ∂steinhausMeasure) = (∫ z : ℂ, z.im ^ 2 ∂steinhausMeasure) := by
  have h := integral_re (integrable_steinhaus_pow 2)
  change (∫ z : ℂ, (z ^ 2).re ∂steinhausMeasure) =
    (∫ z : ℂ, z ^ 2 ∂steinhausMeasure).re at h
  rw [integral_sq_steinhaus, Complex.zero_re] at h
  have heq (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq, Complex.mul_re]
  simp_rw [heq] at h
  rw [integral_sub integrable_steinhaus_re_sq integrable_steinhaus_im_sq] at h
  linarith

theorem integral_steinhaus_re_sq : (∫ z : ℂ, z.re ^ 2 ∂steinhausMeasure) = 1 / 2 := by
  linarith [integral_steinhaus_coordinate_sq_sum, integral_steinhaus_coordinate_sq_eq]

theorem integral_steinhaus_im_sq : (∫ z : ℂ, z.im ^ 2 ∂steinhausMeasure) = 1 / 2 := by
  linarith [integral_steinhaus_coordinate_sq_sum, integral_steinhaus_coordinate_sq_eq]

/-- Each coordinate of the circular coefficient is centered. -/
theorem integral_steinhaus_re : (∫ z : ℂ, z.re ∂steinhausMeasure) = 0 := by
  change (∫ z : ℂ, RCLike.re z ∂steinhausMeasure) = 0
  rw [integral_re integrable_steinhaus, integral_steinhaus]
  rfl

theorem integral_steinhaus_im : (∫ z : ℂ, z.im ∂steinhausMeasure) = 0 := by
  change (∫ z : ℂ, RCLike.im z ∂steinhausMeasure) = 0
  rw [integral_im integrable_steinhaus, integral_steinhaus]
  rfl

/-- The mixed real second moment is integrable. -/
theorem integrable_steinhaus_re_mul_im :
    Integrable (fun z : ℂ => z.re * z.im) steinhausMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_norm_steinhaus_eq_one] with z hz
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hz
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans_eq hz
  simpa only [Real.norm_eq_abs, abs_mul, one_mul] using
    mul_le_mul hre him (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The real and imaginary coordinates have zero mixed moment. -/
theorem integral_steinhaus_re_mul_im :
    (∫ z : ℂ, z.re * z.im ∂steinhausMeasure) = 0 := by
  have h := integral_im (integrable_steinhaus_pow 2)
  change (∫ z : ℂ, (z ^ 2).im ∂steinhausMeasure) =
    (∫ z : ℂ, z ^ 2 ∂steinhausMeasure).im at h
  rw [integral_sq_steinhaus, Complex.zero_im] at h
  have heq (z : ℂ) : (z ^ 2).im = 2 * (z.re * z.im) := by
    simp only [sq, Complex.mul_im]
    ring
  simp_rw [heq] at h
  rw [integral_const_mul] at h
  linarith

end Erdos522
