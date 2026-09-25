/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.CircularValues
import Erdos522.Probability.GaussianApproximation.Values

/-!
# Gaussian approximation for exactly normalized circular values

The covariance is exactly that of the standard circular Gaussian.
Consequently the convex-set error consists solely of the finite-sum
Gaussian approximation, uniformly over all angles.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule

/-- The uniform circular-value approximation constant. -/
def circularValueGaussianErrorConstant (C K : ℝ) : ℝ :=
  64 * C * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K)

/-- Circular value coefficient third moments have the annular scale `N⁻¹/²`. -/
theorem circular_value_third_moment_sum_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ k, (‖realValueCoefficient N r z k‖ + ‖imaginaryValueCoefficient N r z k‖) ^ 3) ≤
      8 * Real.exp (3 * K) / Real.sqrt N := by
  simp_rw [norm_imaginaryValueCoefficient]
  have heq (t : ℝ) : (t + t) ^ 3 = 8 * t ^ 3 := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  calc
    _ ≤ 8 * (Real.exp (3 * K) / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left
        (sum_third_norm_realValueCoefficient_le N hN K r hK hNK hrl hru z hz) (by norm_num)
    _ = _ := by ring

/-- A quantitative standard-circular approximation for the actual Steinhaus
value law, with exact variance normalization and no angular exclusions. -/
theorem exists_gaussian_approximation_circular_value_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (z : ℂ) (_ : ‖z‖ = 1) (A : Set (EuclideanSpace ℝ (Fin 2)))
      (_ : MeasurableSet A) (_ : Convexity.IsConvexSet ℝ A),
      |((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
        (circularValue N r z)).real A - circularGaussian.real A| ≤
          circularValueGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_circular_vectors_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru z hz A hA hconvex
  have hgram (x : EuclideanSpace ℝ (Fin 2)) :
      (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤ ∑ k, (⟪x, realValueCoefficient N r z k⟫ ^ 2 +
        ⟪x, imaginaryValueCoefficient N r z k⟫ ^ 2) / 2 := by
    have h := circularValue_covariance_form N r z hz x x
    rw [circularCovarianceMatrix_form, real_inner_self_eq_norm_sq] at h
    simp only [sq] at h ⊢
    rw [h]
    nlinarith [sq_nonneg ‖x‖]
  have h := happrox (by norm_num : 0 < 2) (realValueCoefficient N r z)
    (imaginaryValueCoefficient N r z) (1 / 4) (by norm_num) hgram A hA hconvex
  rw [circularValue_covariance_eq N r z hz] at h
  have hthird := circular_value_third_moment_sum_le N hN K r hK hNK hrl hru z hz
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num [Real.sqrt_div]
  calc
    _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) *
        (∑ k, (‖realValueCoefficient N r z k‖ + ‖imaginaryValueCoefficient N r z k‖) ^ 3) /
          Real.sqrt (1 / 4 : ℝ) ^ 3 := h
    _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) * (8 * Real.exp (3 * K) / Real.sqrt N) /
        Real.sqrt (1 / 4 : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthird (by positivity)) (by positivity)
    _ = _ := by rw [hsqrt]; unfold circularValueGaussianErrorConstant; ring

end Erdos522
