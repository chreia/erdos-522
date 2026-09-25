/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianLogarithmicMoments
import Erdos522.Probability.RademacherLogarithmicConcentration

/-!
# Angular logarithmic moments of Gaussian polynomials

Multiplication by unit Fourier phases preserves the squared coefficient norm.
The coefficient-uniform Gaussian logarithmic estimate therefore integrates
over the angle, retaining the constant `16` for exactly normalized polynomials.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522

/-- A finite Fourier polynomial with independent real Gaussian coefficients. -/
def gaussianFourierPolynomial {n : ℕ} (a : Fin n → ℂ) (g : Fin n → ℝ)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  complexGaussianSum (fun k => a k * (AddCircle.toCircle θ : ℂ) ^ k.val) g

theorem measurable_gaussianFourierPolynomial {n : ℕ} (a : Fin n → ℂ) :
    Measurable (fun z : (Fin n → ℝ) × AddCircle (1 : ℝ) => gaussianFourierPolynomial a z.1 z.2) := by
  unfold gaussianFourierPolynomial complexGaussianSum
  fun_prop

/-- Fourier phases preserve the normalization of the deterministic coefficients. -/
theorem sum_sq_norm_fourier_phases {n : ℕ} (a : Fin n → ℂ)
    (θ : AddCircle (1 : ℝ)) :
    (∑ k, ‖a k * (AddCircle.toCircle θ : ℂ) ^ k.val‖ ^ 2) = ∑ k, ‖a k‖ ^ 2 := by
  simp only [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one]

/-- Absolute logarithmic moments are jointly integrable in the Gaussian coefficients and angle. -/
theorem integrable_gaussianFourier_logarithmic_moment {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : (Fin n → ℝ) × AddCircle (1 : ℝ) =>
      |Real.log ‖gaussianFourierPolynomial a z.1 z.2‖| ^ p)
      ((gaussianCoefficientMeasure n).prod AddCircle.haarAddCircle) := by
  have hm : Measurable (fun z : (Fin n → ℝ) × AddCircle (1 : ℝ) =>
      |Real.log ‖gaussianFourierPolynomial a z.1 z.2‖| ^ p) :=
    (measurable_gaussianFourierPolynomial a).norm.log.norm.pow_const p
  have hsection (θ : AddCircle (1 : ℝ)) := gaussian_logarithmic_moments
    (fun k => a k * (AddCircle.toCircle θ : ℂ) ^ k.val)
    (by rw [sum_sq_norm_fourier_phases, ha]) hp
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun θ => (hsection θ).1
  · apply (integrable_const ((16 * p) ^ p)).mono'
    · exact hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    · filter_upwards with θ
      have hn (g : Fin n → ℝ) : 0 ≤ |Real.log ‖gaussianFourierPolynomial a g θ‖| ^ p :=
        Real.rpow_nonneg (abs_nonneg _) _
      simp only [Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (hn _)]
      rw [abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae (ae_of_all _ hn))]
      exact (hsection θ).2

/-- The angular logarithmic estimate has the same constant for every normalized
finite Gaussian Fourier polynomial. -/
theorem integral_gaussianFourier_logarithmic_moment_le {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    (∫ g, ∫ θ, |Real.log ‖gaussianFourierPolynomial a g θ‖| ^ p
      ∂AddCircle.haarAddCircle ∂gaussianCoefficientMeasure n) ≤ (16 * p) ^ p := by
  have hI := integrable_gaussianFourier_logarithmic_moment a ha hp
  rw [integral_integral_swap hI]
  calc
    _ ≤ ∫ _ : AddCircle (1 : ℝ), (16 * p) ^ p ∂AddCircle.haarAddCircle := by
      apply integral_mono hI.integral_prod_right (integrable_const _)
      intro θ
      exact (gaussian_logarithmic_moments
        (fun k => a k * (AddCircle.toCircle θ : ℂ) ^ k.val)
        (by rw [sum_sq_norm_fourier_phases, ha]) hp).2
    _ = _ := by simp

/-- The Gaussian polynomial with coefficients through degree `N`. -/
def gaussianPolynomial (N : ℕ) (g : Fin (N + 1) → ℝ) : ℂ[X] :=
  ∑ k, monomial k.val (g k : ℂ)

/-- Exact radial normalization of the Gaussian polynomial. -/
theorem gaussianFourierPolynomial_radial_eq (N : ℕ) (r : ℝ)
    (g : Fin (N + 1) → ℝ) (θ : AddCircle (1 : ℝ)) :
    gaussianFourierPolynomial (normalizedRadialCoefficients N r) g θ =
      (gaussianPolynomial N g).eval ((r : ℂ) * AddCircle.toCircle θ) / (radialSigma N r : ℂ) := by
  simp only [gaussianFourierPolynomial, complexGaussianSum, normalizedRadialCoefficients,
    gaussianPolynomial, eval_finsetSum, eval_monomial, Finset.sum_div, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The manuscript's logarithmic-moment estimate for every degree and radius,
under the actual independent standard real Gaussian coefficient law. -/
theorem integral_normalizedGaussianPolynomial_logarithmic_moment_le (N : ℕ) (r : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ g, ∫ θ : AddCircle (1 : ℝ),
      |Real.log ‖(gaussianPolynomial N g).eval ((r : ℂ) * AddCircle.toCircle θ) /
        (radialSigma N r : ℂ)‖| ^ p
      ∂AddCircle.haarAddCircle ∂gaussianCoefficientMeasure (N + 1)) ≤ (16 * p) ^ p := by
  have h := integral_gaussianFourier_logarithmic_moment_le
    (normalizedRadialCoefficients N r) (sum_sq_norm_normalizedRadialCoefficients N r) hp
  simpa only [gaussianFourierPolynomial_radial_eq] using h

end Erdos522
