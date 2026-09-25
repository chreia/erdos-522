/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianEnergy
import Erdos522.Probability.GaussianFourierLogarithmicMoments
import Erdos522.Probability.AmplitudeEnergy

/-!
# Angular energy of Gaussian polynomials

Parseval identifies normalized angular energy with a weighted sum of
independent Gaussian squares.  The annular radial-weight bound then gives
the exponential exceptional-event probability with its explicit constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
namespace Erdos522
open LogMoments

/-- Gaussian Fourier energy is the sum of the squared random coefficients. -/
theorem integral_norm_sq_gaussianFourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (g : Fin (N + 1) → ℝ) :
    (∫ θ, ‖gaussianFourierPolynomial a g θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ k, ‖a k‖ ^ 2 * g k ^ 2 := by
  have he (θ : AddCircle (1 : ℝ)) : gaussianFourierPolynomial a g θ =
      fourierPolynomial (fun k => (g k : ℂ) * a k) (fun _ => true) θ := by
    simp only [gaussianFourierPolynomial, complexGaussianSum, fourierPolynomial,
      signedPolynomial, eval_finsetSum, eval_monomial, sign, ite_true, one_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_norm_sq_fourierPolynomial]
  apply Finset.sum_congr rfl
  intro k _
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Parseval identifies normalized polynomial energy with the exact radial energy weights. -/
theorem integral_normalizedGaussianPolynomial_energy (N : ℕ) (r : ℝ)
    (g : Fin (N + 1) → ℝ) :
    (∫ θ : AddCircle (1 : ℝ),
      ‖(gaussianPolynomial N g).eval ((r : ℂ) * AddCircle.toCircle θ) /
        (radialSigma N r : ℂ)‖ ^ 2 ∂AddCircle.haarAddCircle) =
      gaussianWeightedEnergy (radialEnergyWeight N r) g := by
  simp_rw [← gaussianFourierPolynomial_radial_eq]
  rw [integral_norm_sq_gaussianFourierPolynomial]
  simp only [norm_sq_normalizedRadialCoefficients, gaussianWeightedEnergy]

/-- The annular Gaussian energy exceptional event has probability at most
`exp (-3N/(32 exp(6K)))`. -/
theorem gaussian_radial_energy_gt_two_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) :
    gaussianCoefficientMeasure (N + 1) {g | 2 <
      ∫ θ : AddCircle (1 : ℝ),
        ‖(gaussianPolynomial N g).eval ((r : ℂ) * AddCircle.toCircle θ) /
          (radialSigma N r : ℂ)‖ ^ 2 ∂AddCircle.haarAddCircle} ≤
      ENNReal.ofReal (Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K)))) := by
  simp_rw [integral_normalizedGaussianPolynomial_energy]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := gaussianWeightedEnergy_gt_two_le (radialEnergyWeight N r)
    (radialEnergyWeight_nonneg N r) (sum_radialEnergyWeight N r)
    (div_pos (Real.exp_pos _) hn) (radialEnergyWeight_le N hN K r hK hNK hrl hru)
  convert h using 1
  congr 2
  field_simp

/-- The unweighted sum of squared Gaussian coefficients has the same relative-energy tail. -/
theorem gaussian_coefficient_energy_gt_two_dimension_le {n : ℕ} (hn : 0 < n) :
    gaussianCoefficientMeasure n {g | 2 * (n : ℝ) < ∑ k, g k ^ 2} ≤
      ENNReal.ofReal (Real.exp (-3 * (n : ℝ) / 32)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by simp [hn.ne']
  have h := gaussianWeightedEnergy_gt_two_le (fun _ : Fin n => (1 / (n : ℝ)))
    (fun _ => by positivity) hw (by positivity : 0 < 1 / (n : ℝ)) (fun _ => le_rfl)
  have he : {g : Fin n → ℝ | 2 < gaussianWeightedEnergy (fun _ : Fin n => (1 / (n : ℝ))) g} =
      {g | 2 * (n : ℝ) < ∑ k, g k ^ 2} := by
    ext g
    simp only [gaussianWeightedEnergy, one_div, inv_mul_eq_div, Set.mem_ofPred_eq]
    rw [← Finset.sum_div, lt_div_iff₀ hnR]
  rw [he] at h
  convert h using 1
  congr 2
  field_simp

end Erdos522
