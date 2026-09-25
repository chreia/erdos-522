/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.LogarithmicTails
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Circular complex Gaussian coefficients

The standard circular complex Gaussian has independent real and imaginary
coordinates of variance one half, so its complex quadratic moment is one.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped RealInnerProductSpace NNReal

namespace Erdos522

/-- The real-linear isometry identifying the Euclidean plane with the complex line. -/
def valueComplexLinearMap : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  (EuclideanSpace.proj 0).smulRight (1 : ℂ) +
    (EuclideanSpace.proj 1).smulRight Complex.I

@[simp]
theorem valueComplexLinearMap_apply (x : EuclideanSpace ℝ (Fin 2)) :
    valueComplexLinearMap x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  simp [valueComplexLinearMap, Complex.real_smul]

@[simp]
theorem norm_valueComplexLinearMap (x : EuclideanSpace ℝ (Fin 2)) :
    ‖valueComplexLinearMap x‖ = ‖x‖ := by
  have h : ‖valueComplexLinearMap x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [Complex.normSq_apply, pow_two]
  nlinarith [norm_nonneg (valueComplexLinearMap x), norm_nonneg x]

/-- The standard complex Gaussian with unit complex variance. -/
def circularComplexGaussian : Measure ℂ := circularGaussian.map valueComplexLinearMap

instance : IsProbabilityMeasure circularComplexGaussian := by
  unfold circularComplexGaussian
  exact (Measure.isProbabilityMeasure_map_iff valueComplexLinearMap.measurable.aemeasurable).mpr inferInstance

instance : IsGaussian circularComplexGaussian := by
  unfold circularComplexGaussian circularGaussian
  infer_instance

/-- The centered circular law has zero complex mean. -/
theorem integral_id_circularComplexGaussian :
    (∫ z, z ∂circularComplexGaussian) = 0 := by
  let : IsGaussian circularGaussian := by unfold circularGaussian; infer_instance
  rw [circularComplexGaussian, valueComplexLinearMap.integral_id_map
    (show Integrable id circularGaussian from IsGaussian.integrable_id)]
  simp [circularGaussian]

/-- Its complex quadratic moment equals one. -/
theorem integral_norm_sq_circularComplexGaussian :
    (∫ z, ‖z‖ ^ 2 ∂circularComplexGaussian) = 1 := by
  rw [circularComplexGaussian, integral_map valueComplexLinearMap.measurable.aemeasurable
    (by fun_prop)]
  simpa only [norm_valueComplexLinearMap] using integral_norm_sq_circularGaussian

/-- Its quadratic moment is integrable. -/
theorem memLp_two_id_circularComplexGaussian : MemLp id 2 circularComplexGaussian :=
  IsGaussian.memLp_two_id

/-- Euclidean coordinates of the real inner product with a complex number. -/
theorem inner_valueComplexLinearMap (x : EuclideanSpace ℝ (Fin 2)) (z : ℂ) :
    inner ℝ (valueComplexLinearMap x) z = inner ℝ x (toLp 2 ![z.re, z.im]) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]

/-- The characteristic function in complex real coordinates. -/
theorem charFun_circularComplexGaussian (z : ℂ) :
    charFun circularComplexGaussian z = Complex.exp (-(‖z‖ ^ 2 : ℝ) / 4) := by
  rw [circularComplexGaussian, charFun_apply, integral_map
    valueComplexLinearMap.measurable.aemeasurable (by fun_prop)]
  simp_rw [inner_valueComplexLinearMap]
  change charFun circularGaussian (toLp 2 ![z.re, z.im]) = _
  rw [circularGaussian, charFun_multivariateGaussian
    (show (Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℝ))).PosSemidef from
      Matrix.PosSemidef.diagonal (by intro; norm_num))]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  simp [dotProduct, Fin.sum_univ_two,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Central symmetry of the circular Gaussian law. -/
instance : circularComplexGaussian.IsNegInvariant where
  neg_eq_self := by
    change circularComplexGaussian.map (fun z => -z) = circularComplexGaussian
    apply Measure.ext_of_charFun
    ext z
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    simp only [inner_neg_left, ← inner_neg_right]
    change charFun circularComplexGaussian (-z) = charFun circularComplexGaussian z
    simp only [charFun_circularComplexGaussian, norm_neg]

/-- The exact disk distribution of a standard circular complex Gaussian. -/
theorem circularComplexGaussian_real_norm_le {t : ℝ} (ht : 0 ≤ t) :
    circularComplexGaussian.real {z | ‖z‖ ≤ t} = 1 - Real.exp (-t ^ 2) := by
  rw [circularComplexGaussian, measureReal_def, Measure.map_apply_of_aemeasurable
    valueComplexLinearMap.measurable.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
  convert circularGaussian_real_closedBall t ht using 1
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, norm_valueComplexLinearMap,
    Metric.mem_closedBall, dist_zero_right]

/-- A circular complex Gaussian coefficient is nonzero almost surely. -/
theorem ae_circularComplexGaussian_ne_zero : ∀ᵐ z ∂circularComplexGaussian, z ≠ 0 := by
  have h := circularComplexGaussian_real_norm_le (t := 0) le_rfl
  simp only [norm_le_zero_iff, neg_zero, zero_pow (by norm_num : 2 ≠ 0),
    Real.exp_zero, sub_self] at h
  rw [ae_iff]
  simpa only [not_not] using (measureReal_eq_zero_iff).mp h

end Erdos522
