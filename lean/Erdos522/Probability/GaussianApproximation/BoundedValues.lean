/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.ComplexCoefficientValues

/-!
# Circular approximation of bounded complex polynomial values

The exact variance normalization and covariance comparison identify the
standard circular Gaussian target. The approximation error separates the
third-moment cost from the oscillatory covariance error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule

/-- The Gaussian with the actual complex-coefficient value covariance is
close to the standard circular law away from doubled-angle resonance. -/
theorem gaussian_complexValue_circular_comparison
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r θ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    |(multivariateGaussian 0 (coefficientCovarianceMatrix μ
        (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
        (imaginaryValueCoefficient N r (Complex.exp (Complex.I * θ))))).real A -
      circularGaussian.real A| ≤ 10 * Real.exp (8 * K) / Real.sqrt N := by
  let S := coefficientCovarianceMatrix μ (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
    (imaginaryValueCoefficient N r (Complex.exp (Complex.I * θ)))
  let T : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => (1 / 2 : ℝ)
  let δ := 5 * Real.exp (8 * K) / Real.sqrt N
  have hlower (x : EuclideanSpace ℝ (Fin 2)) : (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤
      covarianceBilin ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
        (circularValue N r (Complex.exp (Complex.I * θ)))) x x := by
    rw [← dotProduct_covarianceMatrix_mulVec]
    exact complexValue_covariance_lower μ h2 hmean hnorm N hN K r θ hK hNK hrl hru hdegree hangle x
  have hS : S.PosDef := coefficientCovarianceMatrix_posDef μ _ _ (by norm_num) hlower
  have hT : T.PosDef := Matrix.PosDef.diagonal (by intro i; norm_num)
  have herror (x : EuclideanSpace ℝ (Fin 2)) :
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, quadratic_diagonal_const]
    exact complexValue_covariance_circular_error μ h2 hmean hnorm N hN K r θ hK hNK hrl hru hangle x
  have hsmall : δ / (1 / 2) ≤ 1 / 2 := by
    have h := value_covariance_error_le_quarter N hN K hdegree
    dsimp [δ]
    linarith
  have h := gaussian_measureReal_sub_le_of_quadratic_error S T hS hT (1 / 2) δ
    (by norm_num) (by dsimp [δ]; positivity) hsmall
    (fun x => by rw [quadratic_diagonal_const]) herror A hA
  refine h.trans_eq ?_
  norm_num
  dsimp [δ]
  ring

/-- The finite circular approximation constant for coefficients bounded by `B`. -/
def boundedValueGaussianErrorConstant (C B K : ℝ) : ℝ :=
  64 * C * (2 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 * Real.exp (3 * K) + 10 * Real.exp (8 * K)

/-- Exactly normalized values of independent bounded centered complex
coefficients approximate the standard circular law. -/
theorem exists_gaussian_approximation_bounded_value_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (B : ℝ) (_ : 0 ≤ B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
      (N : ℕ) (_ : 0 < N) (K r θ : ℝ) (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 2))) (_ : MeasurableSet A) (_ : Convexity.IsConvexSet ℝ A),
      |((Measure.pi (fun _ : Fin (N + 1) => μ)).map
        (circularValue N r (Complex.exp (Complex.I * θ)))).real A - circularGaussian.real A| ≤
        boundedValueGaussianErrorConstant C B K / Real.sqrt N := by
  obtain ⟨C, hC, happ⟩ := exists_gaussian_approximation_complex_coefficients_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ B hB hb hm hv N hN K r θ hK hNK hrl hru hdegree hangle A hA hconvex
  have h2 : MemLp (fun z : ℂ => z) 2 μ := MemLp.of_bound (by fun_prop) B hb
  let z := Complex.exp (Complex.I * θ)
  let S := coefficientCovarianceMatrix μ (realValueCoefficient N r z) (imaginaryValueCoefficient N r z)
  have hlower (x : EuclideanSpace ℝ (Fin 2)) : (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤
      covarianceBilin ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularValue N r z)) x x := by
    rw [← dotProduct_covarianceMatrix_mulVec]
    exact complexValue_covariance_lower μ h2 hm hv N hN K r θ hK hNK hrl hru hdegree hangle x
  have h := happ μ B hB hb hm (by norm_num : 0 < 2)
    (realValueCoefficient N r z) (imaginaryValueCoefficient N r z)
    (1 / 4) (by norm_num) hlower A hA hconvex
  have hthird := circular_value_third_moment_sum_le N hN K r hK hNK hrl hru z
    (Complex.norm_exp_I_mul_ofReal θ)
  have hfirst : |((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularValue N r z)).real A -
      (multivariateGaussian 0 S).real A| ≤
      (64 * C * (2 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 * Real.exp (3 * K)) / Real.sqrt N := by
    calc
      _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
          (∑ k, (‖realValueCoefficient N r z k‖ + ‖imaginaryValueCoefficient N r z k‖) ^ 3) /
            Real.sqrt (1 / 4 : ℝ) ^ 3 := h
      _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
          (8 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt (1 / 4 : ℝ) ^ 3 := by gcongr
      _ = _ := by norm_num [Real.sqrt_div]; ring
  have hsecond := gaussian_complexValue_circular_comparison μ h2 hm hv N hN K r θ hK hNK hrl hru
    hdegree hangle A hA
  exact (abs_sub_le _ ((multivariateGaussian 0 S).real A) _).trans
    ((add_le_add hfirst hsecond).trans_eq (by unfold boundedValueGaussianErrorConstant; ring))

end Erdos522
