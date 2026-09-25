/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.NormalizedValues
import Erdos522.Probability.GaussianApproximation.CovarianceComparison

/-!
# Circular Gaussian approximation for polynomial values

Exact variance normalization makes the limiting covariance one half of the
identity. The oscillatory covariance estimate and convex-set approximation
therefore give the standard circular Gaussian law, with an explicit error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

namespace Erdos522

local instance normalizedValueConvexSpace {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The standard circular complex Gaussian in two real coordinates. -/
def circularGaussian : Measure (EuclideanSpace ℝ (Fin 2)) :=
  multivariateGaussian 0 (Matrix.diagonal fun _ => (1 / 2 : ℝ))

instance : IsProbabilityMeasure circularGaussian := by unfold circularGaussian; infer_instance

/-- A scalar identity covariance has the corresponding scalar Euclidean quadratic form. -/
theorem quadratic_diagonal_const {d : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    x.ofLp ⬝ᵥ (Matrix.diagonal fun _ => c) *ᵥ x.ofLp = c * ‖x‖ ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quantitative degree threshold makes the normalized value covariance error at most one quarter. -/
theorem value_covariance_error_le_quarter (N : ℕ) (hN : 0 < N) (K : ℝ)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) :
    5 * Real.exp (8 * K) / Real.sqrt N ≤ 1 / 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hslo : 20 * Real.exp (8 * K) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hn.le, Real.exp_pos (8 * K)]
  exact (div_le_iff₀ hs).mpr (by linarith)

/-- The exact-variance normalized value covariance is bounded below by one quarter of the identity. -/
theorem realValue_covariance_lower (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤
      x.ofLp ⬝ᵥ signCovarianceMatrix (realValueCoefficient N r (Complex.exp (Complex.I * θ))) *ᵥ x.ofLp := by
  have h := (abs_le.mp (realValue_covariance_circular_error N hN K r θ hK hNK hrl hru hangle x)).1
  have hsmall := mul_le_mul_of_nonneg_right (value_covariance_error_le_quarter N hN K hdegree)
    (sq_nonneg ‖x‖)
  linarith

/-- The normalized value covariance is positive definite off the angular resonance. -/
theorem realValueCovarianceMatrix_posDef (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖) :
    (signCovarianceMatrix (realValueCoefficient N r (Complex.exp (Complex.I * θ)))).PosDef := by
  apply signCovarianceMatrix_posDef _ (1 / 4) (by norm_num)
  intro x
  rw [← dotProduct_covarianceMatrix_mulVec]
  exact realValue_covariance_lower N hN K r θ hK hNK hrl hru hdegree hangle x

/-- A Gaussian with the actual normalized value covariance is within `10 exp(8K)/sqrt N`
of the standard circular law on every measurable event. -/
theorem gaussian_normalizedValue_circular_comparison (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    |(multivariateGaussian 0 (signCovarianceMatrix
      (realValueCoefficient N r (Complex.exp (Complex.I * θ))))).real A - circularGaussian.real A| ≤
      10 * Real.exp (8 * K) / Real.sqrt N := by
  let S := signCovarianceMatrix (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
  let T : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => (1 / 2 : ℝ)
  let δ := 5 * Real.exp (8 * K) / Real.sqrt N
  have hS : S.PosDef := realValueCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hangle
  have hT : T.PosDef := Matrix.PosDef.diagonal (by intro i; norm_num)
  have hlower (x : EuclideanSpace ℝ (Fin 2)) : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp := by
    rw [quadratic_diagonal_const]
  have herror (x : EuclideanSpace ℝ (Fin 2)) :
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, quadratic_diagonal_const]
    exact realValue_covariance_circular_error N hN K r θ hK hNK hrl hru hangle x
  have hsmall : δ / (1 / 2) ≤ 1 / 2 := by
    have h := value_covariance_error_le_quarter N hN K hdegree
    dsimp [δ]
    linarith
  have h := gaussian_measureReal_sub_le_of_quadratic_error S T hS hT (1 / 2) δ
    (by norm_num) (by dsimp [δ]; positivity) hsmall hlower herror A hA
  change |(multivariateGaussian 0 S).real A - (multivariateGaussian 0 T).real A| ≤ _
  refine h.trans_eq ?_
  norm_num
  dsimp [δ]
  ring

/-- The one-point approximation constant combines the exact Bentkus constant with covariance comparison. -/
def valueGaussianErrorConstant (C K : ℝ) : ℝ :=
  8 * C * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) + 10 * Real.exp (8 * K)

/-- Convex events of exactly normalized Rademacher values converge uniformly to the standard circular law. -/
theorem exists_circular_gaussian_approximation_value_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r θ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 2))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |((LogMoments.signMeasure N).map
        (realRademacherValue N r (Complex.exp (Complex.I * θ)))).real A - circularGaussian.real A| ≤
        valueGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_approximation_sign_sum_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r θ hK hNK hrl hru hdegree hangle A hA hconvex
  let a := realValueCoefficient N r (Complex.exp (Complex.I * θ))
  let S := signCovarianceMatrix a
  have hS : S.PosDef := realValueCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hangle
  have hlower (x : EuclideanSpace ℝ (Fin 2)) : (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp :=
    realValue_covariance_lower N hN K r θ hK hNK hrl hru hdegree hangle x
  have hwhite := sum_third_norm_inverseCovarianceSqrt_le a S hS (1 / 4) (by norm_num) hlower
  have hmoment := sum_third_norm_realValueCoefficient_le N hN K r hK hNK hrl hru
    (Complex.exp (Complex.I * θ)) (Complex.norm_exp_I_mul_ofReal θ)
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num [Real.sqrt_div]
  rw [hsqrt] at hwhite
  have hthird : (∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3) ≤
      8 * (Real.exp (3 * K) / Real.sqrt N) := by
    have h := hwhite.trans (div_le_div_of_nonneg_right hmoment (by norm_num))
    convert h using 1; ring
  have h := (hbound (by norm_num : 0 < 2) a hS A hA hconvex).trans
    (mul_le_mul_of_nonneg_left hthird (by positivity))
  have hg := gaussian_normalizedValue_circular_comparison N hN K r θ hK hNK hrl hru hdegree hangle A hA
  change |((LogMoments.signMeasure N).map (realRademacherValue N r (Complex.exp (Complex.I * θ)))).real A -
    (multivariateGaussian 0 S).real A| ≤ _ at h
  calc
    _ ≤ |((LogMoments.signMeasure N).map (realRademacherValue N r (Complex.exp (Complex.I * θ)))).real A -
        (multivariateGaussian 0 S).real A| + |(multivariateGaussian 0 S).real A - circularGaussian.real A| :=
      abs_sub_le _ _ _
    _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) * (8 * (Real.exp (3 * K) / Real.sqrt N)) +
        10 * Real.exp (8 * K) / Real.sqrt N := add_le_add h hg
    _ = _ := by unfold valueGaussianErrorConstant; ring

end Erdos522
