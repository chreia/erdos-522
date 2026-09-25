/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.ComplexCoefficientVectors
import Erdos522.Probability.GaussianApproximation.CircularValues

/-!
# Circular covariance approximation for centered complex coefficients

The doubled-angle covariance error is uniform over real test directions.
Integration over coefficient rotations preserves this error for every
centered complex law of unit second moment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The adjoint quarter turn on one complex value direction. -/
def valueDirectionRotation (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![x 1, -x 0]

theorem inner_imaginaryValueCoefficient_rotation (N : ℕ) (r : ℝ) (z : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, imaginaryValueCoefficient N r z k⟫ =
      ⟪valueDirectionRotation x, realValueCoefficient N r z k⟫ := by
  simp only [imaginaryValueCoefficient, valueDirectionRotation, PiLp.inner_apply,
    Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem norm_sq_complex_value_direction (c : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖c.re • x + c.im • valueDirectionRotation x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, valueDirectionRotation,
    Complex.sq_norm, Complex.normSq_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The actual value covariance is the average real Gram form over
coefficient rotations and dilations. -/
theorem quadratic_coefficientCovarianceMatrix_value (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (N : ℕ) (r : ℝ) (z : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    x.ofLp ⬝ᵥ coefficientCovarianceMatrix μ (realValueCoefficient N r z)
      (imaginaryValueCoefficient N r z) *ᵥ x.ofLp =
      ∫ c, (c.re • x + c.im • valueDirectionRotation x).ofLp ⬝ᵥ
        signCovarianceMatrix (realValueCoefficient N r z) *ᵥ
          (c.re • x + c.im • valueDirectionRotation x).ofLp ∂μ := by
  rw [coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec,
    covarianceBilin_complexCoefficientSum μ h2 hmean]
  apply integral_congr_ae
  filter_upwards with c
  rw [signCovarianceMatrix_form]
  apply Finset.sum_congr rfl
  intro k _
  simp only [circularVector, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_imaginaryValueCoefficient_rotation]

/-- The normalized value covariance has the same circular error for every
centered complex coefficient law of unit second moment. -/
theorem complexValue_covariance_circular_error
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r θ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 2)) :
    |x.ofLp ⬝ᵥ coefficientCovarianceMatrix μ
        (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
        (imaginaryValueCoefficient N r (Complex.exp (Complex.I * θ))) *ᵥ x.ofLp -
      (1 / 2 : ℝ) * ‖x‖ ^ 2| ≤ (5 * Real.exp (8 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
  let Y := fun c : ℂ => c.re • x + c.im • valueDirectionRotation x
  let S := signCovarianceMatrix (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
  let δ := 5 * Real.exp (8 * K) / Real.sqrt N
  have hY : MemLp Y 2 μ := memLp_complexCoefficientVector μ h2 x (valueDirectionRotation x)
  have hquad : Integrable (fun c => (Y c).ofLp ⬝ᵥ S *ᵥ (Y c).ofLp) μ := by
    simp only [S, signCovarianceMatrix_form, ← sq]
    exact integrable_finsetSum _ fun k _ => by
      simpa only [real_inner_comm] using
        (hY.const_inner (realValueCoefficient N r (Complex.exp (Complex.I * θ)) k)).integrable_sq
  have hnormI : Integrable (fun c => ‖Y c‖ ^ 2) μ := hY.norm.integrable_sq
  have hnormmean : (∫ c, ‖Y c‖ ^ 2 ∂μ) = ‖x‖ ^ 2 := by
    simp only [Y, norm_sq_complex_value_direction, integral_mul_const, hnorm, one_mul]
  rw [quadratic_coefficientCovarianceMatrix_value μ h2 hmean]
  change |(∫ c, (Y c).ofLp ⬝ᵥ S *ᵥ (Y c).ofLp ∂μ) - (1 / 2 : ℝ) * ‖x‖ ^ 2| ≤ _
  rw [← hnormmean, ← integral_const_mul, ← integral_sub hquad (hnormI.const_mul (1 / 2))]
  calc
    _ ≤ ∫ c, |(Y c).ofLp ⬝ᵥ S *ᵥ (Y c).ofLp - (1 / 2 : ℝ) * ‖Y c‖ ^ 2| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ c, δ * ‖Y c‖ ^ 2 ∂μ := integral_mono
      (hquad.sub (hnormI.const_mul (1 / 2))).abs (hnormI.const_mul δ) (fun c =>
        realValue_covariance_circular_error N hN K r θ hK hNK hrl hru hangle (Y c))
    _ = _ := by rw [integral_const_mul, hnormmean]

/-- The finite degree threshold yields a quarter-identity covariance lower bound. -/
theorem complexValue_covariance_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r θ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ coefficientCovarianceMatrix μ
      (realValueCoefficient N r (Complex.exp (Complex.I * θ)))
      (imaginaryValueCoefficient N r (Complex.exp (Complex.I * θ))) *ᵥ x.ofLp := by
  have h := (abs_le.mp (complexValue_covariance_circular_error μ h2 hmean hnorm N hN K r θ
    hK hNK hrl hru hangle x)).1
  have hs := mul_le_mul_of_nonneg_right (value_covariance_error_le_quarter N hN K hdegree)
    (sq_nonneg ‖x‖)
  linarith

end Erdos522
