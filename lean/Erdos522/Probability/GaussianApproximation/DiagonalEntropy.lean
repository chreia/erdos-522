/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.ProductEntropy
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Relative entropy for diagonal Gaussian covariance matrices

The product formula for real Gaussian densities agrees with Mathlib's native
multivariate Gaussian measure on Euclidean space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Matrix WithLp Complex
open scoped ENNReal NNReal MatrixOrder

namespace Erdos522

/-- Independent real Gaussian coordinates have diagonal covariance. -/
theorem map_pi_gaussianReal_eq_multivariateGaussian {n : ℕ} (v : Fin n → ℝ≥0) :
    (Measure.pi fun i => gaussianReal 0 (v i)).map (toLp 2) =
      multivariateGaussian 0 (Matrix.diagonal fun i => (v i : ℝ)) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ (Fin n))
  ext t
  have hdiag : (Matrix.diagonal fun i => (v i : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => (v i).property)
  rw [charFun_pi, charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin n))) hdiag t]
  simp only [charFun_gaussianReal, ofReal_zero, mul_zero, zero_mul, zero_sub,
    ← Complex.exp_sum, inner_zero_right]
  congr 1
  simp only [Matrix.mulVec_diagonal, dotProduct, ← ofReal_pow,
    ← ofReal_mul, ← ofReal_sum, Finset.sum_neg_distrib, ← Finset.sum_div]
  push_cast
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact entropy for positive diagonal Gaussian covariance matrices. -/
theorem klDiv_multivariateGaussian_diagonal {n : ℕ} (v w : Fin n → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) :
    klDiv (multivariateGaussian 0 (Matrix.diagonal fun i => (v i : ℝ)))
        (multivariateGaussian 0 (Matrix.diagonal fun i => (w i : ℝ))) =
      ∑ i, ENNReal.ofReal (((v i : ℝ) / w i - 1 - Real.log ((v i : ℝ) / w i)) / 2) := by
  rw [← map_pi_gaussianReal_eq_multivariateGaussian,
    ← map_pi_gaussianReal_eq_multivariateGaussian,
    ← MeasurableEquiv.coe_toLp,
    klDiv_map_measurableEquiv, klDiv_pi_gaussianReal v w hv hw]

/-- Quadratic entropy bound for nearby positive diagonal Gaussian covariance matrices. -/
theorem klDiv_multivariateGaussian_diagonal_le {n : ℕ} (v w : Fin n → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hvw : ∀ i, 1 / 2 ≤ (v i : ℝ) / w i) :
    klDiv (multivariateGaussian 0 (Matrix.diagonal fun i => (v i : ℝ)))
        (multivariateGaussian 0 (Matrix.diagonal fun i => (w i : ℝ))) ≤
      ENNReal.ofReal (∑ i, ((v i : ℝ) / w i - 1) ^ 2) := by
  rw [← map_pi_gaussianReal_eq_multivariateGaussian,
    ← map_pi_gaussianReal_eq_multivariateGaussian,
    ← MeasurableEquiv.coe_toLp, klDiv_map_measurableEquiv]
  exact klDiv_pi_gaussianReal_le v w hv hw hvw

end Erdos522
