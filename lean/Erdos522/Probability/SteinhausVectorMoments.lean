/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausMoments
import ProbabilityApproximation.Bentkus.CovarianceAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real vector moments of circular coefficients

A real linear image of a circular coefficient has covariance equal to half
the Gram form of its two coordinate images. Independence then adds these
forms for finite sums.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators ENNReal
namespace Erdos522

/-- The real linear image determined by the images of `1` and `I`. -/
def circularVector {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) (z : ℂ) :
    EuclideanSpace ℝ (Fin d) := z.re • a + z.im • b

theorem norm_circularVector_le {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) (z : ℂ) :
    ‖circularVector a b z‖ ≤ ‖z‖ * (‖a‖ + ‖b‖) := by
  calc
    _ ≤ ‖z.re • a‖ + ‖z.im • b‖ := norm_add_le _ _
    _ = |z.re| * ‖a‖ + |z.im| * ‖b‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * ‖a‖ + ‖z‖ * ‖b‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = _ := by ring

theorem memLp_circularVector {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) (p : ℝ≥0∞) :
    MemLp (circularVector a b) p steinhausMeasure := by
  apply MemLp.of_bound (by unfold circularVector; fun_prop) (‖a‖ + ‖b‖)
  filter_upwards [ae_norm_steinhaus_eq_one] with z hz
  simpa only [hz, one_mul] using norm_circularVector_le a b z

/-- The circular vector has mean zero. -/
theorem integral_circularVector {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ z, circularVector a b z ∂steinhausMeasure) = 0 := by
  have hre : Integrable (fun z : ℂ => z.re) steinhausMeasure := integrable_steinhaus.re
  have him : Integrable (fun z : ℂ => z.im) steinhausMeasure := integrable_steinhaus.im
  unfold circularVector
  rw [integral_add (hre.smul_const a) (him.smul_const b)]
  simp only [integral_smul_const, integral_steinhaus_re, integral_steinhaus_im, zero_smul, add_zero]

/-- The product of two real projections has the circular Gram integral. -/
theorem integral_steinhaus_projection_mul (a b c d : ℝ) :
    (∫ z : ℂ, (a * z.re + b * z.im) * (c * z.re + d * z.im) ∂steinhausMeasure) =
      (a * c + b * d) / 2 := by
  have heq (z : ℂ) : (a * z.re + b * z.im) * (c * z.re + d * z.im) =
      a * c * z.re ^ 2 + (a * d + b * c) * (z.re * z.im) + b * d * z.im ^ 2 := by ring
  simp_rw [heq]
  have hab : Integrable (fun z : ℂ => a * c * z.re ^ 2 +
      (a * d + b * c) * (z.re * z.im)) steinhausMeasure :=
    (integrable_steinhaus_re_sq.const_mul (a * c)).add
      (integrable_steinhaus_re_mul_im.const_mul (a * d + b * c))
  rw [integral_add hab (integrable_steinhaus_im_sq.const_mul (b * d)),
    integral_add (integrable_steinhaus_re_sq.const_mul (a * c))
      (integrable_steinhaus_re_mul_im.const_mul (a * d + b * c))]
  simp only [integral_const_mul, integral_steinhaus_re_sq, integral_steinhaus_im_sq,
    integral_steinhaus_re_mul_im]
  ring

/-- The real covariance form of one circular vector. -/
theorem covarianceBilin_circularVector {d : ℕ} (a b x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (steinhausMeasure.map (circularVector a b)) x y =
      (⟪x, a⟫ * ⟪y, a⟫ + ⟪x, b⟫ * ⟪y, b⟫) / 2 := by
  have h2 := memLp_circularVector a b 2
  rw [covarianceBilin_map_apply_eq_cov_projection h2,
    covariance_eq_sub (h2.const_inner x) (h2.const_inner y)]
  have hmean (v : EuclideanSpace ℝ (Fin d)) :
      (∫ z, ⟪v, circularVector a b z⟫ ∂steinhausMeasure) = 0 := by
    rw [integral_inner ((memLp_circularVector a b 1).integrable (by norm_num)),
      integral_circularVector]
    simp
  rw [hmean x, hmean y, mul_zero, sub_zero]
  simpa only [circularVector, inner_add_right, real_inner_smul_right, mul_comm,
    Pi.mul_apply] using
    integral_steinhaus_projection_mul ⟪x, a⟫ ⟪x, b⟫ ⟪y, a⟫ ⟪y, b⟫

/-- A sum of independent circular vectors on the finite coefficient space. -/
def circularVectorSum {n d : ℕ} (a b : Fin n → EuclideanSpace ℝ (Fin d))
    (ω : Fin n → ℂ) : EuclideanSpace ℝ (Fin d) := ∑ k, circularVector (a k) (b k) (ω k)

/-- Coordinate evaluation preserves every finite circular-vector moment. -/
theorem memLp_circularVector_coordinate {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (k : Fin n) (p : ℝ≥0∞) :
    MemLp (fun ω : Fin n → ℂ => circularVector (a k) (b k) (ω k)) p
      (Measure.pi (fun _ => steinhausMeasure)) :=
  (memLp_circularVector (a k) (b k) p).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => steinhausMeasure) k)

/-- Circular summands at distinct coordinates are independent. -/
theorem iIndepFun_circularVector {n d : ℕ} (a b : Fin n → EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun k (ω : Fin n → ℂ) => circularVector (a k) (b k) (ω k))
      (Measure.pi (fun _ => steinhausMeasure)) := by
  exact iIndepFun_pi (fun k => (show Measurable (circularVector (a k) (b k)) by
    unfold circularVector; fun_prop).aemeasurable)

/-- Independent circular coefficients add their covariance Gram forms. -/
theorem covarianceBilin_circularVectorSum {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin ((Measure.pi (fun _ : Fin n => steinhausMeasure)).map
      (circularVectorSum a b)) x y =
      ∑ k, (⟪x, a k⟫ * ⟪y, a k⟫ + ⟪x, b k⟫ * ⟪y, b k⟫) / 2 := by
  unfold circularVectorSum
  rw [covarianceBilin_map_sum_eq_sum
    (fun k => memLp_circularVector_coordinate a b k 2) (iIndepFun_circularVector a b)]
  apply Finset.sum_congr rfl
  intro k _
  have hm := measurePreserving_eval (fun _ : Fin n => steinhausMeasure) k
  have hmap : (Measure.pi (fun _ : Fin n => steinhausMeasure)).map
      (fun ω => circularVector (a k) (b k) (ω k)) =
      steinhausMeasure.map (circularVector (a k) (b k)) := by
    change (Measure.pi (fun _ : Fin n => steinhausMeasure)).map
      ((circularVector (a k) (b k)) ∘ Function.eval k) = _
    rw [← Measure.map_map (by unfold circularVector; fun_prop) hm.measurable, hm.map_eq]
  rw [hmap, covarianceBilin_circularVector]

end Erdos522
