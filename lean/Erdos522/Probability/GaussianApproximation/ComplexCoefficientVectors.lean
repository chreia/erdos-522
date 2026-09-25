/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.BoundedVectors
import Erdos522.Probability.ComplexCoefficientVectorMoments

/-!
# Gaussian approximation for bounded complex coefficients

The covariance is taken under the actual coefficient law. A lower spectral
bound and a coefficient bound `B` give the explicit cubic factor in Bentkus's
convex-set approximation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The covariance matrix of a real vector sum with independent complex coefficients. -/
def coefficientCovarianceMatrix (μ : Measure ℂ) {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  covarianceMatrix ((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b))

/-- A lower covariance form makes the actual coefficient covariance positive definite. -/
theorem coefficientCovarianceMatrix_posDef (μ : Measure ℂ) {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤
      covarianceBilin ((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b)) x x) :
    (coefficientCovarianceMatrix μ a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (covarianceMatrix_posSemidef _).isHermitian
  intro x hx
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hy : y ≠ 0 := fun h => hx (congrArg WithLp.ofLp h)
  have hpos := (mul_pos hc (pow_pos (norm_pos_iff.mpr hy) 2)).trans_le (hlower y)
  rw [← dotProduct_covarianceMatrix_mulVec] at hpos
  simpa only [star_trivial, y, coefficientCovarianceMatrix] using hpos

/-- A convex-set approximation with an explicit cubic coefficient-bound factor. -/
theorem exists_gaussian_approximation_complex_coefficients_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (B : ℝ) (_ : 0 ≤ B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (_ : (∫ z, z ∂μ) = 0)
      {n d : ℕ} (_ : 0 < d) (a b : Fin n → EuclideanSpace ℝ (Fin d))
      (c : ℝ) (_ : 0 < c)
      (_ : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤
        covarianceBilin ((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b)) x x)
      (A : Set (EuclideanSpace ℝ (Fin d))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |(((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b)) A).toReal -
        (multivariateGaussian 0 (coefficientCovarianceMatrix μ a b) A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
        (∑ k, (‖a k‖ + ‖b k‖) ^ 3) / Real.sqrt c ^ 3 := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_bounded_vectors_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ B _hB hbound hmean n d hd a b c hc hlower A hA hconvex
  let ν := Measure.pi (fun _ : Fin n => μ)
  let X := fun k (ω : Fin n → ℂ) => circularVector (a k) (b k) (ω k)
  have hI : Integrable (fun z : ℂ => z) μ := Integrable.of_bound (by fun_prop) B hbound
  have hm (k : Fin n) : AEStronglyMeasurable (X k) ν := by
    unfold X circularVector
    fun_prop
  have hind : iIndepFun X ν := iIndepFun_pi (fun k =>
    (show Measurable (circularVector (a k) (b k)) by unfold circularVector; fun_prop).aemeasurable)
  have hXmean (k : Fin n) : (∫ ω, X k ω ∂ν) = 0 := by
    have heval := measurePreserving_eval (fun _ : Fin n => μ) k
    have h := integral_complexCoefficientVector_eq_zero μ hI hmean (a k) (b k)
    rw [← heval.map_eq, integral_map heval.measurable.aemeasurable
      (by unfold circularVector; fun_prop)] at h
    exact h
  have hXbound (k : Fin n) : ∀ᵐ ω ∂ν, ‖X k ω‖ ≤ B * (‖a k‖ + ‖b k‖) := by
    have heval := (measurePreserving_eval (fun _ : Fin n => μ) k).quasiMeasurePreserving.ae hbound
    filter_upwards [heval] with ω hω
    exact (norm_circularVector_le (a k) (b k) (ω k)).trans
      (mul_le_mul_of_nonneg_right hω (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (ν.map (fun ω => ∑ k, X k ω)) x y =
        x ⬝ᵥ coefficientCovarianceMatrix μ a b *ᵥ y :=
    (dotProduct_covarianceMatrix_mulVec _ x y).symm
  have hmatrix (x : EuclideanSpace ℝ (Fin d)) :
      c * ‖x‖ ^ 2 ≤ x ⬝ᵥ coefficientCovarianceMatrix μ a b *ᵥ x := by
    rw [coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec]
    exact hlower x
  have h := happrox hd ν X hm hind hXmean (fun k => B * (‖a k‖ + ‖b k‖)) hXbound
    (coefficientCovarianceMatrix μ a b) (coefficientCovarianceMatrix_posDef μ a b hc hlower)
    hcov c hc hmatrix A hA hconvex
  have hsum : (∑ k, (B * (‖a k‖ + ‖b k‖)) ^ 3) =
      B ^ 3 * ∑ k, (‖a k‖ + ‖b k‖) ^ 3 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [hsum] at h
  convert h using 1
  · rfl
  · ring

end Erdos522
