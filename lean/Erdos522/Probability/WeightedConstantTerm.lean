/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.WeightedLogarithmicMoments

/-!
# Power weights with an arbitrary nonzero constant coefficient

A fixed constant coefficient changes the normalized variance by
`(‖b‖² - 1) / N^(2τ+1)`. This vanishing term preserves both compact-uniform
variance profiles when `τ > -1/2`. Exact normalization also preserves the
uniform logarithmic moments and pathwise angular energy of Rademacher sums.
-/

noncomputable section
open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators
namespace Erdos522
open LogMoments

/-- The radial variance when the constant coefficient is `b` and positive-degree weights are powers. -/
def weightedRadialVarianceWithConstant (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ‖b‖ ^ 2 + ∑ j : Fin N, ((j.val : ℝ) + 1) ^ (2 * τ) * r ^ (2 * (j.val + 1))

/-- The exact change caused by replacing the constant coefficient. -/
theorem weightedRadialVarianceWithConstant_eq (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ) :
    weightedRadialVarianceWithConstant b τ N r = weightedRadialVariance τ N r + (‖b‖ ^ 2 - 1) := by
  unfold weightedRadialVarianceWithConstant weightedRadialVariance
  ring

theorem weightedRadialVarianceWithConstant_pos {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (N : ℕ) (r : ℝ) : 0 < weightedRadialVarianceWithConstant b τ N r := by
  apply add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hb) 2)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by rw [pow_mul]; positivity)

/-- The radial standard deviation for these power weights. -/
def weightedRadialSigmaWithConstant (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (weightedRadialVarianceWithConstant b τ N r)

theorem weightedRadialSigmaWithConstant_pos {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (N : ℕ) (r : ℝ) : 0 < weightedRadialSigmaWithConstant b τ N r :=
  Real.sqrt_pos.mpr (weightedRadialVarianceWithConstant_pos hb τ N r)

/-- The perturbation of normalized variance vanishes for every fixed constant coefficient. -/
theorem tendsto_weighted_constant_perturbation (b : ℂ) (τ : ℝ) (hτ : -1 / 2 < τ) :
    Tendsto (fun N : ℕ => (‖b‖ ^ 2 - 1) / (N : ℝ) ^ (2 * τ + 1)) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 * τ + 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (‖b‖ ^ 2 - 1)
  simpa only [mul_zero, Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv] using h

/-- Pointwise variance convergence is unaffected by the constant coefficient. -/
theorem tendsto_weightedRadialVarianceWithConstant_profile (b : ℂ) (τ x : ℝ)
    (hτ : -1 / 2 < τ) :
    Tendsto (fun N : ℕ => weightedRadialVarianceWithConstant b τ N (1 + x / N) /
      (N : ℝ) ^ (2 * τ + 1)) atTop (𝓝 (weightedVarianceProfile τ x)) := by
  have h := (tendsto_weightedRadialVariance_profile τ x (by linarith)).add
    (tendsto_weighted_constant_perturbation b τ hτ)
  simpa only [weightedRadialVarianceWithConstant_eq, add_div, Pi.add_def, add_zero] using h

/-- Compact-uniform convergence of the variance with arbitrary fixed constant coefficient. -/
theorem weightedRadialVarianceWithConstant_profile_compact_uniform (b : ℂ) (τ : ℝ)
    (hτ : -1 / 2 < τ) {s : Set ℝ} (hs : IsCompact s) :
    TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
      weightedRadialVarianceWithConstant b τ N (1 + x / N) / (N : ℝ) ^ (2 * τ + 1))
      (weightedVarianceProfile τ) atTop s := by
  have h := (weightedRadialVariance_profile_compact_uniform τ hτ hs).add
    ((tendsto_weighted_constant_perturbation b τ hτ).tendstoUniformlyOn_const s)
  simpa only [weightedRadialVarianceWithConstant_eq, add_div, Pi.add_def, add_zero] using h

/-- Pointwise logarithmic normalization retains the exponent `τ+1/2`. -/
theorem tendsto_log_weightedRadialSigmaWithConstant_profile {b : ℂ} (hb : b ≠ 0)
    (τ x : ℝ) (hτ : -1 / 2 < τ) :
    Tendsto (fun N : ℕ => Real.log (weightedRadialSigmaWithConstant b τ N (1 + x / N)) -
      (τ + 1 / 2) * Real.log N) atTop (𝓝 (weightedLogVarianceProfile τ x)) := by
  have h := ((tendsto_weightedRadialVarianceWithConstant_profile b τ x hτ).log
    (weightedVarianceProfile_pos hτ x).ne').const_mul (1 / 2 : ℝ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.log_div (weightedRadialVarianceWithConstant_pos hb τ N _).ne'
    (Real.rpow_pos_of_pos hn _).ne', Real.log_rpow hn, weightedRadialSigmaWithConstant,
    Real.log_sqrt (weightedRadialVarianceWithConstant_pos hb τ N _).le]
  ring

/-- The locally uniform logarithmic variance profile is independent of the nonzero constant coefficient. -/
theorem log_weightedRadialSigmaWithConstant_profile_compact_uniform {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (hτ : -1 / 2 < τ) {s : Set ℝ} (hs : IsCompact s) :
    TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
      Real.log (weightedRadialSigmaWithConstant b τ N (1 + x / N)) -
        (τ + 1 / 2) * Real.log N) (weightedLogVarianceProfile τ) atTop s := by
  let f : ℕ → ℝ → ℝ := fun N x =>
    Real.log (weightedRadialSigmaWithConstant b τ N (max 0 (1 + x / N))) -
      (τ + 1 / 2) * Real.log N
  have hmono : ∀ N, Monotone (f N) := by
    intro N x y hxy
    apply sub_le_sub_right
    apply Real.log_le_log (weightedRadialSigmaWithConstant_pos hb τ N _)
    apply Real.sqrt_le_sqrt
    simp only [weightedRadialVarianceWithConstant_eq]
    apply add_le_add _ le_rfl
    apply weightedRadialVariance_mono N (le_max_left _ _)
    exact max_le_max_left _ (add_le_add le_rfl
      (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg N)))
  have hpoint : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (weightedLogVarianceProfile τ x)) := by
    intro x
    apply (tendsto_log_weightedRadialSigmaWithConstant_profile hb τ x hτ).congr'
    filter_upwards [(tendsto_kac_radius x).eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with N hN
    simp only [f, max_eq_right hN.le]
  have h := tendstoUniformlyOn_of_monotone_pointwise f (weightedLogVarianceProfile τ)
    hmono (continuous_weightedLogVarianceProfile hτ) hpoint hs
  apply h.congr
  filter_upwards [eventually_nonneg_scaled_radius_on_compact hs] with N hN
  intro x hx
  simp only [f, max_eq_right (hN x hx)]

/-- Complex power weights with prescribed constant coefficient. -/
def powerWeightWithConstant (b : ℂ) (τ : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then b else (((k : ℝ) ^ τ : ℝ) : ℂ)

/-- Exact radial coefficients for these weights. -/
def normalizedWeightedRadialCoefficientsWithConstant (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ)
    (k : Fin (N + 1)) : ℂ :=
  powerWeightWithConstant b τ k.val * (r : ℂ) ^ k.val /
    (weightedRadialSigmaWithConstant b τ N r : ℂ)

/-- Parseval's coefficient sum equals the variance with constant coefficient `b`. -/
theorem sum_powerWeightWithConstant_sq_radial (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ) :
    (∑ k : Fin (N + 1), ‖powerWeightWithConstant b τ k.val‖ ^ 2 * r ^ (2 * k.val)) =
      weightedRadialVarianceWithConstant b τ N r := by
  rw [Fin.sum_univ_succ]
  simp only [powerWeightWithConstant, Fin.val_zero, ite_true, mul_zero, pow_zero, mul_one,
    Fin.val_succ, Nat.add_one_ne_zero, ite_false, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold weightedRadialVarianceWithConstant
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ k.val + 1) τ 2]
  push_cast
  congr 1
  ring

/-- Exact radial normalization has unit squared coefficient norm. -/
theorem sum_sq_norm_normalizedWeightedRadialCoefficientsWithConstant {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (N : ℕ) (r : ℝ) :
    (∑ k, ‖normalizedWeightedRadialCoefficientsWithConstant b τ N r k‖ ^ 2) = 1 := by
  simp only [normalizedWeightedRadialCoefficientsWithConstant, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weightedRadialSigmaWithConstant_pos hb τ N r), div_pow, mul_pow,
    ← pow_mul, Nat.mul_comm _ 2, even_two_mul, Even.pow_abs]
  rw [← Finset.sum_div, sum_powerWeightWithConstant_sq_radial, weightedRadialSigmaWithConstant,
    Real.sq_sqrt (weightedRadialVarianceWithConstant_pos hb τ N r).le]
  exact div_self (weightedRadialVarianceWithConstant_pos hb τ N r).ne'

/-- The normalized weighted polynomial with the chosen constant coefficient. -/
def normalizedWeightedValueWithConstant (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ)
    (ω : SignVector N) (θ : AddCircle (1 : ℝ)) : ℂ :=
  (signedPolynomial (fun k : Fin (N + 1) => powerWeightWithConstant b τ k.val) ω).eval
    ((r : ℂ) * AddCircle.toCircle θ) / (weightedRadialSigmaWithConstant b τ N r : ℂ)

/-- The weighted polynomial is the Fourier sum of its exactly normalized radial coefficients. -/
theorem weighted_fourierPolynomial_with_constant_eq (b : ℂ) (τ : ℝ) (N : ℕ) (r : ℝ)
    (ω : SignVector N) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial (normalizedWeightedRadialCoefficientsWithConstant b τ N r) ω θ =
      normalizedWeightedValueWithConstant b τ N r ω θ := by
  simp only [fourierPolynomial, normalizedWeightedValueWithConstant, signedPolynomial,
    eval_finsetSum, eval_monomial, normalizedWeightedRadialCoefficientsWithConstant,
    Finset.sum_div, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The coefficient-uniform logarithmic estimate holds for every fixed nonzero constant coefficient. -/
theorem weighted_logarithmic_moments_with_constant {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : SignVector N × AddCircle (1 : ℝ) =>
      |Real.log ‖normalizedWeightedValueWithConstant b τ N r z.1 z.2‖| ^ p) (fourierMeasure N) ∧
    (∫ ω, ∫ θ, |Real.log ‖normalizedWeightedValueWithConstant b τ N r ω θ‖| ^ p
      ∂AddCircle.haarAddCircle ∂signMeasure N) ≤
        (rademacherLogarithmicConstant * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := uniform_logarithmic_moments
    (normalizedWeightedRadialCoefficientsWithConstant b τ N r)
    (sum_sq_norm_normalizedWeightedRadialCoefficientsWithConstant hb τ N r) hp
  rw [fourierMeasure, integral_prod _ hI] at hbound
  constructor
  · simpa only [randomFourier, weighted_fourierPolynomial_with_constant_eq] using hI
  · simpa only [randomFourier, weighted_fourierPolynomial_with_constant_eq] using hbound

/-- Unit angular energy holds for every sign vector after exact normalization. -/
theorem integral_weighted_normalized_energy_with_constant {b : ℂ} (hb : b ≠ 0)
    (τ : ℝ) (N : ℕ) (r : ℝ) (ω : SignVector N) :
    (∫ θ, ‖normalizedWeightedValueWithConstant b τ N r ω θ‖ ^ 2 ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [← weighted_fourierPolynomial_with_constant_eq]
  rw [integral_norm_sq_fourierPolynomial,
    sum_sq_norm_normalizedWeightedRadialCoefficientsWithConstant hb τ N r]

end Erdos522
