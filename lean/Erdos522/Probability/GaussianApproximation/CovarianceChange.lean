/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.DiagonalEntropy

/-!
# Gaussian covariance under linear changes of coordinates

A common linear image preserves the entropy upper bound for two Gaussian
laws. This identifies the covariance matrices explicitly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Erdos522

/-- A centered Gaussian transformed by a matrix has the conjugated covariance matrix. -/
theorem map_multivariateGaussian_matrix {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      multivariateGaussian 0 (A * S * A.conjTranspose) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [(Matrix.toEuclideanCLM (𝕜 := ℝ) A).integral_id_map IsGaussian.integrable_id]
    simp
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian (hS.mul_mul_conjTranspose_same A),
      ← Matrix.inner_toEuclideanCLM, ← Matrix.inner_toEuclideanCLM,
      ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [map_mul, map_mul, mul_apply_eq_comp,
      mul_apply_eq_comp]
    congr 2
    exact congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => f y)
      (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) A).symm

/-- Common linear images of positive diagonal Gaussian laws obey the same entropy bound. -/
theorem klDiv_gaussian_covariance_conjugate_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v w : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hvw : ∀ i, 1 / 2 ≤ (v i : ℝ) / w i) :
    klDiv (multivariateGaussian 0 (A * (Matrix.diagonal fun i => (v i : ℝ)) * A.conjTranspose))
        (multivariateGaussian 0 (A * (Matrix.diagonal fun i => (w i : ℝ)) * A.conjTranspose)) ≤
      ENNReal.ofReal (∑ i, ((v i : ℝ) / w i - 1) ^ 2) := by
  have hvdiag : (Matrix.diagonal fun i => (v i : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => (v i).property)
  have hwdiag : (Matrix.diagonal fun i => (w i : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => (w i).property)
  rw [← map_multivariateGaussian_matrix _ A hvdiag,
    ← map_multivariateGaussian_matrix _ A hwdiag]
  exact (klDiv_map_le _ _ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).measurable).trans
    (klDiv_multivariateGaussian_diagonal_le v w hv hw hvw)

end Erdos522
