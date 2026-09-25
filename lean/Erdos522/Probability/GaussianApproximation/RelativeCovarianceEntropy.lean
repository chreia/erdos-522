/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.SpectralEntropy

/-!
# Relative entropy of nearby positive Gaussian covariance matrices

The inverse square root of the reference covariance transforms the comparison
to the identity covariance. The entropy bound depends on the dimension and
the quadratic error after this normalization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Erdos522

/-- The covariance of the first Gaussian in coordinates normalized by the second. -/
def relativeCovariance {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (CFC.sqrt T)⁻¹ * S * ((CFC.sqrt T)⁻¹).conjTranspose

/-- Positive definite covariances stay positive definite after normalization. -/
theorem relativeCovariance_posDef {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) (hT : T.PosDef) : (relativeCovariance S T).PosDef := by
  have hR : IsUnit (CFC.sqrt T) := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).2 hT.isUnit
  have hW : IsUnit (CFC.sqrt T)⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hR
  exact hW.posDef_star_right_conjugate_iff.mpr hS

/-- The positive square root returns the normalized covariance to its original coordinates. -/
theorem sqrt_mul_relativeCovariance {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.PosDef) :
    CFC.sqrt T * relativeCovariance S T * (CFC.sqrt T).conjTranspose = S := by
  have hR : IsUnit (CFC.sqrt T) := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).2 hT.isUnit
  have hRW : CFC.sqrt T * (CFC.sqrt T)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  calc
    _ = (CFC.sqrt T * (CFC.sqrt T)⁻¹) * S *
        (CFC.sqrt T * (CFC.sqrt T)⁻¹).conjTranspose := by
      simp only [relativeCovariance, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = S := by rw [hRW]; simp

/-- Quantitative relative entropy for two positive definite Gaussian covariance matrices. -/
theorem klDiv_multivariateGaussian_le_of_relative_quadratic_bound {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      |x.ofLp ⬝ᵥ relativeCovariance S T *ᵥ x.ofLp - ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2) :
    klDiv (multivariateGaussian 0 S) (multivariateGaussian 0 T) ≤
      ENNReal.ofReal ((n : ℝ) * ε ^ 2) := by
  have hB := relativeCovariance_posDef S T hS hT
  have hroot : CFC.sqrt T * (1 : Matrix (Fin n) (Fin n) ℝ) * (CFC.sqrt T).conjTranspose = T := by
    rw [mul_one]
    change CFC.sqrt T * star (CFC.sqrt T) = T
    rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have hmapS := map_multivariateGaussian_matrix (relativeCovariance S T) (CFC.sqrt T) hB.posSemidef
  have hmapT := map_multivariateGaussian_matrix (1 : Matrix (Fin n) (Fin n) ℝ) (CFC.sqrt T) Matrix.PosSemidef.one
  rw [sqrt_mul_relativeCovariance S T hT] at hmapS
  rw [hroot] at hmapT
  rw [← hmapS, ← hmapT]
  exact (klDiv_map_le _ _ (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt T)).measurable).trans
    (klDiv_multivariateGaussian_identity_le_of_quadratic_bound _ hB ε hε hεhalf hbound)

/-- A reference covariance becomes the identity in its own normalized coordinates. -/
theorem relativeCovariance_self {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef) :
    relativeCovariance T T = 1 := by
  let R := CFC.sqrt T
  have hR : IsUnit R := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).2 hT.isUnit
  have hWR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hRW : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hWh : R⁻¹.IsHermitian := (CFC.sqrt_nonneg T).isSelfAdjoint.isHermitian.inv
  have hroot : R * R = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  change R⁻¹ * T * R⁻¹.conjTranspose = 1
  rw [hWh.eq, ← hroot]
  calc
    R⁻¹ * (R * R) * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by noncomm_ring
    _ = 1 := by rw [hWR, hRW, one_mul]

/-- The quadratic form of a conjugated real matrix is obtained by transforming its vector. -/
theorem quadratic_covariance_conjugate {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (A * S * A.conjTranspose) *ᵥ x =
      (A.conjTranspose *ᵥ x) ⬝ᵥ S *ᵥ (A.conjTranspose *ᵥ x) := by
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- Absolute quadratic covariance error becomes relative error after normalization. -/
theorem relativeCovariance_quadratic_error {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp)
    (herror : ∀ x : EuclideanSpace ℝ (Fin n),
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    |x.ofLp ⬝ᵥ relativeCovariance S T *ᵥ x.ofLp - ‖x‖ ^ 2| ≤
      (δ / c) * ‖x‖ ^ 2 := by
  let y : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (((CFC.sqrt T)⁻¹).conjTranspose *ᵥ x.ofLp)
  have hTform : y.ofLp ⬝ᵥ T *ᵥ y.ofLp = ‖x‖ ^ 2 := by
    change (((CFC.sqrt T)⁻¹).conjTranspose *ᵥ x.ofLp) ⬝ᵥ T *ᵥ
      (((CFC.sqrt T)⁻¹).conjTranspose *ᵥ x.ofLp) = _
    rw [← quadratic_covariance_conjugate]
    change x.ofLp ⬝ᵥ relativeCovariance T T *ᵥ x.ofLp = _
    rw [relativeCovariance_self T hT, Matrix.one_mulVec]
    simpa only [real_inner_self_eq_norm_sq, star_trivial] using
      (EuclideanSpace.inner_eq_star_dotProduct x x).symm
  have hnorm : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 / c := by
    rw [le_div_iff₀ hc, mul_comm]
    simpa only [hTform] using hlower y
  have hdiff : x.ofLp ⬝ᵥ relativeCovariance S T *ᵥ x.ofLp - ‖x‖ ^ 2 =
      y.ofLp ⬝ᵥ (S - T) *ᵥ y.ofLp := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hTform]
    exact congrArg (fun z : ℝ => z - ‖x‖ ^ 2)
      (quadratic_covariance_conjugate (CFC.sqrt T)⁻¹ S x.ofLp)
  rw [hdiff]
  calc
    _ ≤ δ * ‖y‖ ^ 2 := herror y
    _ ≤ δ * (‖x‖ ^ 2 / c) := mul_le_mul_of_nonneg_left hnorm hδ
    _ = δ / c * ‖x‖ ^ 2 := by ring

/-- Positive Gaussian covariances with a common spectral lower bound and quadratic
perturbation size `δ ≤ c/2` have entropy at most `n (δ/c)²`. -/
theorem klDiv_multivariateGaussian_le_of_quadratic_error {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ / c ≤ 1 / 2)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp)
    (herror : ∀ x : EuclideanSpace ℝ (Fin n),
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2) :
    klDiv (multivariateGaussian 0 S) (multivariateGaussian 0 T) ≤
      ENNReal.ofReal ((n : ℝ) * (δ / c) ^ 2) :=
  klDiv_multivariateGaussian_le_of_relative_quadratic_bound S T hS hT (δ / c)
    (div_nonneg hδ hc.le) hsmall (relativeCovariance_quadratic_error S T hT c δ hc hδ hlower herror)

end Erdos522
