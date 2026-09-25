/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.UniformLogarithmicMoments

/-!
# Logarithmic moments under amplitude normalization

Conditioning on amplitudes leaves a deterministic complex coefficient vector.
If its energy is bounded above and away from zero, its logarithmic moments
follow from the normalized Rademacher estimate with a bounded additive shift.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Normalizing coefficients divides the random Fourier sum by the square
root of its deterministic coefficient energy. -/
theorem randomFourier_normalizedCoefficients {N : ℕ}
    (a : Fin (N + 1) → ℂ) (z : SignVector N × AddCircle (1 : ℝ)) :
    randomFourier (normalizedCoefficients a) z =
      randomFourier a z / (Real.sqrt (∑ k, ‖a k‖ ^ 2) : ℂ) := by
  simp only [randomFourier, fourierPolynomial_eq_sum, normalizedCoefficients]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Positive coefficient energy guarantees a nonzero coefficient. -/
theorem exists_coefficient_ne_zero_of_energy_pos {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : 0 < ∑ k, ‖a k‖ ^ 2) : ∃ k, a k ≠ 0 := by
  by_contra! h
  simp [h] at ha

/-- The logarithmic modulus changes by exactly half the logarithmic energy
when a nonzero coefficient vector is normalized. -/
theorem log_norm_randomFourier_eq_normalized {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : 0 < ∑ k, ‖a k‖ ^ 2) :
    ∀ᵐ z ∂fourierMeasure N,
      Real.log ‖randomFourier a z‖ =
        Real.log ‖randomFourier (normalizedCoefficients a) z‖ +
          (1 / 2 : ℝ) * Real.log (∑ k, ‖a k‖ ^ 2) := by
  have hn := sum_sq_norm_normalizedCoefficients a (exists_coefficient_ne_zero_of_energy_pos a ha)
  have hs : 0 < Real.sqrt (∑ k, ‖a k‖ ^ 2) := Real.sqrt_pos.mpr ha
  filter_upwards [randomFourier_ae_ne_zero (normalizedCoefficients a) hn] with z hz
  have hz' : randomFourier a z ≠ 0 := by
    intro h
    rw [randomFourier_normalizedCoefficients, h, zero_div] at hz
    exact hz rfl
  rw [randomFourier_normalizedCoefficients, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, Real.log_div (norm_pos_iff.mpr hz').ne' hs.ne',
    Real.log_sqrt ha.le]
  ring

/-- On the amplitude energy range `[1/2,B²]`, the logarithmic normalization
shift is bounded by the exact deterministic amplitude constant. -/
theorem abs_half_log_energy_le {V B : ℝ} (hV : 1 / 2 ≤ V)
    (hVB : V ≤ B ^ 2) :
    |(1 / 2 : ℝ) * Real.log V| ≤ max ((1 / 2 : ℝ) * Real.log 2) (Real.log B) := by
  have hVpos : 0 < V := by linarith
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hV
  have hhi := Real.log_le_log hVpos hVB
  rw [one_div, Real.log_inv] at hlo
  rw [Real.log_pow] at hhi
  norm_num at hhi
  apply abs_le.mpr
  constructor
  · have h := le_max_left ((1 / 2 : ℝ) * Real.log 2) (Real.log B)
    linarith
  · have h := le_max_right ((1 / 2 : ℝ) * Real.log 2) (Real.log B)
    linarith

/-- A nonnegative power of a sum is bounded by the sum of the powers at
the cost of `2^p`. -/
theorem rpow_add_le_two_rpow_mul {u v p : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hp : 0 ≤ p) : (u + v) ^ p ≤ (2 : ℝ) ^ p * (u ^ p + v ^ p) := by
  calc
    (u + v) ^ p ≤ (2 * max u v) ^ p :=
      Real.rpow_le_rpow (add_nonneg hu hv) (by
        linarith [le_max_left u v, le_max_right u v]) hp
    _ = (2 : ℝ) ^ p * max (u ^ p) (v ^ p) := by
      rw [Real.mul_rpow (by norm_num) (hu.trans (le_max_left _ _)), Real.rpow_max hu hv hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (Real.rpow_nonneg hv _))
        (le_add_of_nonneg_left (Real.rpow_nonneg hu _))) (Real.rpow_nonneg (by norm_num) _)

/-- A bound on half the logarithmic coefficient energy gives quantitative
moments before normalization. -/
theorem logarithmic_moments_of_energy_shift_bound {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : 0 < ∑ k, ‖a k‖ ^ 2)
    {H p : ℝ} (hH : 0 ≤ H) (hshift : |(1 / 2 : ℝ) * Real.log (∑ k, ‖a k‖ ^ 2)| ≤ H)
    (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (2 : ℝ) ^ p * ((rademacherLogarithmicConstant * p) ^ (6 * p) + H ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have hn := sum_sq_norm_normalizedCoefficients a (exists_coefficient_ne_zero_of_energy_pos a ha)
  obtain ⟨hI, hmoment⟩ := uniform_logarithmic_moments (normalizedCoefficients a) hn hp
  have hdom : ∀ᵐ z ∂fourierMeasure N,
      |Real.log ‖randomFourier a z‖| ^ p ≤
        (2 : ℝ) ^ p * (|Real.log ‖randomFourier (normalizedCoefficients a) z‖| ^ p + H ^ p) := by
    filter_upwards [log_norm_randomFourier_eq_normalized a ha] with z hz
    have hle : |Real.log ‖randomFourier a z‖| ≤
        |Real.log ‖randomFourier (normalizedCoefficients a) z‖| + H := by
      rw [hz]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) hshift)
    exact (Real.rpow_le_rpow (abs_nonneg _) hle hp0).trans
      (rpow_add_le_two_rpow_mul (abs_nonneg _) hH hp0)
  have hD : Integrable (fun z => (2 : ℝ) ^ p *
      (|Real.log ‖randomFourier (normalizedCoefficients a) z‖| ^ p + H ^ p))
      (fourierMeasure N) := (hI.add (integrable_const (H ^ p))).const_mul ((2 : ℝ) ^ p)
  have hactual : Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) := by
    have hmeas : AEStronglyMeasurable (fun z => |Real.log ‖randomFourier a z‖| ^ p)
        (fourierMeasure N) := by
      simpa only [Real.norm_eq_abs] using
        ((measurable_randomFourier a).norm.log.norm.pow_const p).aestronglyMeasurable
    apply hD.mono' hmeas
    filter_upwards [hdom] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hz
  refine ⟨hactual, (integral_mono_ae hactual hD hdom).trans ?_⟩
  rw [integral_const_mul, integral_add hI (integrable_const _), integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add hmoment (le_refl _))
    (Real.rpow_nonneg (by norm_num) _)

/-- Deterministic amplitude energies in `[1/2,B²]` satisfy the logarithmic
moment estimate used when conditioning a bounded symmetric law. -/
theorem logarithmic_moments_of_bounded_energy {N : ℕ}
    (a : Fin (N + 1) → ℂ) {B p : ℝ}
    (hlo : 1 / 2 ≤ ∑ k, ‖a k‖ ^ 2) (hhi : ∑ k, ‖a k‖ ^ 2 ≤ B ^ 2)
    (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (2 : ℝ) ^ p * ((rademacherLogarithmicConstant * p) ^ (6 * p) +
          max ((1 / 2 : ℝ) * Real.log 2) (Real.log B) ^ p) := by
  apply logarithmic_moments_of_energy_shift_bound a (by linarith)
    (le_trans (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (le_max_left _ _))
    (abs_half_log_energy_le hlo hhi) hp

/-- A bounded additive logarithmic shift preserves the sixth-power moment
scale with an explicit enlarged constant. -/
theorem logarithmic_moments_with_bounded_shift {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : 0 < ∑ k, ‖a k‖ ^ 2)
    {H p : ℝ} (hH : 0 ≤ H) (hshift : |(1 / 2 : ℝ) * Real.log (∑ k, ‖a k‖ ^ 2)| ≤ H)
    (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (2 * (rademacherLogarithmicConstant + H + 1) * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := logarithmic_moments_of_energy_shift_bound a ha hH hshift hp
  have hp0 : 0 ≤ p := by linarith
  have hC : 0 ≤ rademacherLogarithmicConstant := rademacherLogarithmicConstant_pos.le
  let u := (rademacherLogarithmicConstant + H + 1) * p
  have hu1 : 1 ≤ u := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ _ := mul_le_mul (by linarith : 1 ≤ rademacherLogarithmicConstant + H + 1)
        hp (by norm_num) (by positivity)
  have hu0 : 0 ≤ u := by linarith
  have hCu : rademacherLogarithmicConstant * p ≤ u := by dsimp [u]; nlinarith
  have hHu : H ≤ u := by
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ rademacherLogarithmicConstant + H + 1)
    dsimp [u]
    nlinarith
  have hCpower := Real.rpow_le_rpow (mul_nonneg hC hp0) hCu (by positivity : 0 ≤ 6 * p)
  have hHpower : H ^ p ≤ u ^ (6 * p) :=
    (Real.rpow_le_rpow hH hHu hp0).trans
      (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  refine ⟨hI, hbound.trans ?_⟩
  calc
    (2 : ℝ) ^ p * ((rademacherLogarithmicConstant * p) ^ (6 * p) + H ^ p) ≤
        (2 : ℝ) ^ p * (2 * u ^ (6 * p)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (p + 1) * u ^ (6 * p) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      ring
    _ ≤ (2 : ℝ) ^ (6 * p) * u ^ (6 * p) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
        (Real.rpow_nonneg hu0 _)
    _ = _ := by
      rw [← Real.mul_rpow (by norm_num) hu0]
      congr 1
      dsimp [u]
      ring

/-- The amplitude-dependent constant for the eventwise logarithmic estimate. -/
def amplitudeLogarithmicConstant (B : ℝ) : ℝ :=
  2 * (rademacherLogarithmicConstant + max ((1 / 2 : ℝ) * Real.log 2) (Real.log B) + 1)

/-- On the deterministic amplitude event, the absolute logarithmic moments
have the same exponent six as the normalized Rademacher law. -/
theorem uniform_logarithmic_moments_of_bounded_energy {N : ℕ}
    (a : Fin (N + 1) → ℂ) {B p : ℝ}
    (hlo : 1 / 2 ≤ ∑ k, ‖a k‖ ^ 2) (hhi : ∑ k, ‖a k‖ ^ 2 ≤ B ^ 2)
    (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (amplitudeLogarithmicConstant B * p) ^ (6 * p) :=
  logarithmic_moments_with_bounded_shift a (by linarith)
    (le_trans (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (le_max_left _ _))
    (abs_half_log_energy_le hlo hhi) hp

end Erdos522.LogMoments
