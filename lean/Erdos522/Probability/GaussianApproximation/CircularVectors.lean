/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.BoundedVectors
import Erdos522.Probability.SteinhausVectorMoments

/-!
# Gaussian approximation for circular vector sums

The circular Gram form gives the covariance matrix. A lower bound on this
form and the coefficient third moments determine the approximation error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder RealInnerProductSpace
namespace Erdos522

private local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The covariance matrix of a finite circular vector sum. -/
def circularCovarianceMatrix {n d : ℕ} (a b : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  covarianceMatrix ((Measure.pi (fun _ : Fin n => steinhausMeasure)).map (circularVectorSum a b))

theorem circularCovarianceMatrix_form {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    x ⬝ᵥ circularCovarianceMatrix a b *ᵥ y =
      ∑ k, (⟪x, a k⟫ * ⟪y, a k⟫ + ⟪x, b k⟫ * ⟪y, b k⟫) / 2 := by
  rw [circularCovarianceMatrix, dotProduct_covarianceMatrix_mulVec,
    covarianceBilin_circularVectorSum]

/-- A positive circular Gram bound makes the covariance positive definite. -/
theorem circularCovarianceMatrix_posDef {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d),
      c * ‖x‖ ^ 2 ≤ ∑ k, (⟪x, a k⟫ ^ 2 + ⟪x, b k⟫ ^ 2) / 2) :
    (circularCovarianceMatrix a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (covarianceMatrix_posSemidef _).isHermitian
  intro x hx
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hy : y ≠ 0 := by
    intro h
    exact hx (congrArg WithLp.ofLp h)
  have hp : 0 < c * ‖y‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.mpr hy) 2)
  have heq := circularCovarianceMatrix_form a b y y
  simp only [← sq] at heq
  have h := hp.trans_le (hlower y)
  rw [← heq] at h
  simpa only [star_trivial, y, circularCovarianceMatrix] using h

/-- A universal convex-set approximation for independent circular vector sums. -/
theorem exists_gaussian_approximation_circular_vectors_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ} (_ : 0 < d)
      (a b : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ) (_ : 0 < c)
      (_ : ∀ x : EuclideanSpace ℝ (Fin d),
        c * ‖x‖ ^ 2 ≤ ∑ k, (⟪x, a k⟫ ^ 2 + ⟪x, b k⟫ ^ 2) / 2)
      (A : Set (EuclideanSpace ℝ (Fin d))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |(((Measure.pi (fun _ : Fin n => steinhausMeasure)).map (circularVectorSum a b)) A).toReal -
        (multivariateGaussian 0 (circularCovarianceMatrix a b) A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) * (∑ k, (‖a k‖ + ‖b k‖) ^ 3) / Real.sqrt c ^ 3 := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_bounded_vectors_constant
  refine ⟨C, hC, ?_⟩
  intro n d hd a b c hc hlower A hA hconvex
  let μ := Measure.pi (fun _ : Fin n => steinhausMeasure)
  let X := fun k (ω : Fin n → ℂ) => circularVector (a k) (b k) (ω k)
  have hm (k : Fin n) : AEStronglyMeasurable (X k) μ :=
    (memLp_circularVector_coordinate a b k 3).aestronglyMeasurable
  have hmean (k : Fin n) : (∫ ω, X k ω ∂μ) = 0 := by
    change (∫ ω, circularVector (a k) (b k) (ω k) ∂μ) = 0
    have hm := measurePreserving_eval (fun _ : Fin n => steinhausMeasure) k
    have h := integral_circularVector (a k) (b k)
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable
      (by unfold circularVector; fun_prop)] at h
    exact h
  have hbound (k : Fin n) : ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ ‖a k‖ + ‖b k‖ := by
    filter_upwards [ae_pi_norm_steinhaus_eq_one (ι := Fin n)] with ω hω
    simpa only [X, hω k, one_mul] using norm_circularVector_le (a k) (b k) (ω k)
  have hcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (μ.map (fun ω => ∑ k, X k ω)) x y =
        x ⬝ᵥ circularCovarianceMatrix a b *ᵥ y :=
    (dotProduct_covarianceMatrix_mulVec _ x y).symm
  have hmatrix (x : EuclideanSpace ℝ (Fin d)) :
      c * ‖x‖ ^ 2 ≤ x ⬝ᵥ circularCovarianceMatrix a b *ᵥ x := by
    rw [circularCovarianceMatrix_form]
    simpa only [sq] using hlower x
  exact happrox hd μ X hm (iIndepFun_circularVector a b) hmean
    (fun k => ‖a k‖ + ‖b k‖) hbound (circularCovarianceMatrix a b)
    (circularCovarianceMatrix_posDef a b c hc hlower) hcov c hc hmatrix A hA hconvex

end Erdos522
