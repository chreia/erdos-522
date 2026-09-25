/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.WeightedVarianceProfile
import Erdos522.Probability.LogMoments.UniformLogarithmicMoments

/-!
# Exact energy and logarithmic moments for power-weighted signs

Power-weighted polynomials inherit the coefficient-uniform logarithmic
estimate after division by their exact radial standard deviation.  Parseval
gives unit angular energy for each individual sign vector.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
open LogMoments

/-- Power weights with constant coefficient one. -/
def powerWeight (τ : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else (k : ℝ) ^ τ

/-- A finite polynomial with power weights and Rademacher signs. -/
def powerWeightedPolynomial (τ : ℝ) (N : ℕ) (ω : SignVector N) : ℂ[X] :=
  signedPolynomial (fun k => (powerWeight τ k.val : ℂ)) ω

/-- Radial coefficients divided by the exact weighted standard deviation. -/
def normalizedWeightedRadialCoefficients (τ : ℝ) (N : ℕ) (r : ℝ)
    (k : Fin (N + 1)) : ℂ :=
  (powerWeight τ k.val : ℂ) * (r : ℂ) ^ k.val / (weightedRadialSigma τ N r : ℂ)

/-- The normalized polynomial value on a radial copy of the unit circle. -/
def normalizedWeightedValue (τ : ℝ) (N : ℕ) (r : ℝ) (ω : SignVector N)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  (powerWeightedPolynomial τ N ω).eval ((r : ℂ) * AddCircle.toCircle θ) /
    (weightedRadialSigma τ N r : ℂ)

theorem powerWeight_sq_succ (τ : ℝ) (k : ℕ) :
    powerWeight τ (k + 1) ^ 2 = ((k : ℝ) + 1) ^ (2 * τ) := by
  simp only [powerWeight, Nat.add_one_ne_zero, ite_false, Nat.cast_add, Nat.cast_one]
  rw [mul_comm (2 : ℝ) τ]
  exact (Real.rpow_mul_natCast (by positivity : 0 ≤ (k : ℝ) + 1) τ 2).symm

/-- The finite weighted variance is exactly the squared coefficient norm. -/
theorem sum_powerWeight_sq_radial (τ : ℝ) (N : ℕ) (r : ℝ) :
    (∑ k : Fin (N + 1), powerWeight τ k.val ^ 2 * r ^ (2 * k.val)) =
      weightedRadialVariance τ N r := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, powerWeight, ite_true, one_pow, mul_zero, pow_zero,
    mul_one, Fin.val_succ]
  unfold weightedRadialVariance
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← powerWeight_sq_succ]
  rfl

/-- Exact variance normalization has unit squared coefficient norm. -/
theorem sum_sq_norm_normalizedWeightedRadialCoefficients (τ : ℝ) (N : ℕ) (r : ℝ) :
    (∑ k, ‖normalizedWeightedRadialCoefficients τ N r k‖ ^ 2) = 1 := by
  simp only [normalizedWeightedRadialCoefficients, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weightedRadialSigma_pos τ N r),
    div_pow, mul_pow, sq_abs, ← pow_mul, Nat.mul_comm _ 2, even_two_mul, Even.pow_abs]
  rw [← Finset.sum_div, sum_powerWeight_sq_radial, weightedRadialSigma,
    Real.sq_sqrt (weightedRadialVariance_pos τ N r).le]
  exact div_self (weightedRadialVariance_pos τ N r).ne'

/-- The normalized polynomial is the Fourier polynomial of its radial coefficients. -/
theorem weighted_fourierPolynomial_eq (τ : ℝ) (N : ℕ) (r : ℝ) (ω : SignVector N)
    (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial (normalizedWeightedRadialCoefficients τ N r) ω θ =
      normalizedWeightedValue τ N r ω θ := by
  simp only [fourierPolynomial, normalizedWeightedValue, powerWeightedPolynomial,
    signedPolynomial, eval_finsetSum, eval_monomial, normalizedWeightedRadialCoefficients,
    Finset.sum_div, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The normalized angular logarithm has every real moment at least one, jointly
in the signs and angle, with the same absolute constant for all power weights. -/
theorem integrable_weighted_logarithmic_moment (τ : ℝ) (N : ℕ) (r : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : SignVector N × AddCircle (1 : ℝ) =>
      |Real.log ‖normalizedWeightedValue τ N r z.1 z.2‖| ^ p) (fourierMeasure N) := by
  have h := (uniform_logarithmic_moments (normalizedWeightedRadialCoefficients τ N r)
    (sum_sq_norm_normalizedWeightedRadialCoefficients τ N r) hp).1
  simpa only [randomFourier, weighted_fourierPolynomial_eq] using h

/-- The expected angular logarithmic moment obeys the coefficient-uniform
sixth-power bound, independently of the degree, radius, and weight exponent. -/
theorem integral_weighted_logarithmic_moment_le (τ : ℝ) (N : ℕ) (r : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, ∫ θ, |Real.log ‖normalizedWeightedValue τ N r ω θ‖| ^ p
      ∂AddCircle.haarAddCircle ∂signMeasure N) ≤
        (rademacherLogarithmicConstant * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := uniform_logarithmic_moments
    (normalizedWeightedRadialCoefficients τ N r)
    (sum_sq_norm_normalizedWeightedRadialCoefficients τ N r) hp
  rw [fourierMeasure, integral_prod _ hI] at hbound
  simpa only [randomFourier, weighted_fourierPolynomial_eq] using hbound

/-- Exact unit angular energy holds for every sign vector. -/
theorem integral_weighted_normalized_energy (τ : ℝ) (N : ℕ) (r : ℝ) (ω : SignVector N) :
    (∫ θ, ‖normalizedWeightedValue τ N r ω θ‖ ^ 2 ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [← weighted_fourierPolynomial_eq]
  rw [integral_norm_sq_fourierPolynomial, sum_sq_norm_normalizedWeightedRadialCoefficients]

end Erdos522
