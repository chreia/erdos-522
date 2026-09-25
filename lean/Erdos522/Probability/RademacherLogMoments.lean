/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.FiniteFourier
import Erdos522.Probability.LogMoments.StretchedExponential
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Logarithms of finite Rademacher Fourier sums

The finite product sign law and normalized angular measure give the joint law
for arbitrary deterministic complex coefficients.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522
namespace LogMoments

def signMeasure (N : ℕ) : Measure (SignVector N) :=
  Measure.pi (fun _ : Fin (N + 1) => (PMF.uniformOfFintype Bool).toMeasure)

instance (N : ℕ) : IsProbabilityMeasure (signMeasure N) := by
  unfold signMeasure
  infer_instance

def fourierMeasure (N : ℕ) : Measure (SignVector N × AddCircle (1 : ℝ)) :=
  (signMeasure N).prod AddCircle.haarAddCircle

instance (N : ℕ) : IsProbabilityMeasure (fourierMeasure N) := by
  unfold fourierMeasure
  infer_instance

def randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) : ℂ :=
  fourierPolynomial a q.1 q.2

theorem measurable_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Measurable (randomFourier a) := by
  change Measurable (fun q : SignVector N × AddCircle (1 : ℝ) => fourierPolynomial a q.1 q.2)
  simp only [fourierPolynomial_eq_sum]
  have hs (k : Fin (N + 1)) : Measurable (fun ω : SignVector N => sign (ω k)) :=
    measurable_of_finite _
  fun_prop

theorem randomFourier_ae_ne_zero {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    ∀ᵐ q ∂fourierMeasure N, randomFourier a q ≠ 0 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (measurable_randomFourier a) measurable_const).compl).mpr
  exact ae_of_all _ (fun ω => fourierPolynomial_ae_ne_zero a ha ω)

theorem integrable_log_norm_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun q => Real.log ‖randomFourier a q‖) (fourierMeasure N) := by
  apply (integrable_prod_iff (measurable_randomFourier a).norm.log.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω => integrable_log_norm_fourierPolynomial a ω)
  · exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))

theorem integrable_abs_log_norm_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun q => |Real.log ‖randomFourier a q‖|) (fourierMeasure N) :=
  (integrable_log_norm_randomFourier a).abs

theorem integrable_norm_sq_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun q => ‖randomFourier a q‖ ^ 2) (fourierMeasure N) := by
  apply (integrable_prod_iff ((measurable_randomFourier a).norm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω =>
      ((continuous_fourierPolynomial a ω).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))

theorem integral_norm_sq_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    (∫ q, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) = ∑ k, ‖a k‖ ^ 2 := by
  rw [fourierMeasure, integral_prod _ (integrable_norm_sq_randomFourier a)]
  simp only [randomFourier, integral_norm_sq_fourierPolynomial, integral_const,
    probReal_univ, smul_eq_mul, one_mul]

def positiveLogNorm (z : ℂ) : ℝ := max (Real.log ‖z‖) 0

def negativeLogNorm (z : ℂ) : ℝ := max (-Real.log ‖z‖) 0

theorem positiveLogNorm_nonneg (z : ℂ) : 0 ≤ positiveLogNorm z :=
  le_max_right _ _

theorem negativeLogNorm_nonneg (z : ℂ) : 0 ≤ negativeLogNorm z :=
  le_max_right _ _

theorem abs_log_norm_rpow_eq (z : ℂ) {p : ℝ} (hp : 0 < p) :
    |Real.log ‖z‖| ^ p = positiveLogNorm z ^ p + negativeLogNorm z ^ p := by
  rcases le_total 0 (Real.log ‖z‖) with h | h
  · simp only [positiveLogNorm, negativeLogNorm, max_eq_left h,
      max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, Real.zero_rpow hp.ne', add_zero]
  · simp only [positiveLogNorm, negativeLogNorm, max_eq_right h,
      max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, Real.zero_rpow hp.ne', zero_add]

theorem exp_two_positiveLogNorm_le (z : ℂ) :
    Real.exp (2 * positiveLogNorm z) ≤ 1 + ‖z‖ ^ 2 := by
  by_cases hz : ‖z‖ ≤ 1
  · have hlog := Real.log_nonpos (norm_nonneg z) hz
    simp only [positiveLogNorm, max_eq_right hlog, mul_zero, Real.exp_zero]
    nlinarith [sq_nonneg ‖z‖]
  · have hz' : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge hz)
    have hlog := Real.log_nonneg (le_of_lt (lt_of_not_ge hz))
    rw [positiveLogNorm, max_eq_left hlog, two_mul, Real.exp_add,
      Real.exp_log hz']
    nlinarith

theorem integrable_exp_two_positiveLogNorm {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun q => Real.exp (2 * positiveLogNorm (randomFourier a q)))
      (fourierMeasure N) := by
  apply ((integrable_const 1).add (integrable_norm_sq_randomFourier a)).mono'
  · unfold positiveLogNorm
    exact (((measurable_randomFourier a).norm.log.max measurable_const).const_mul 2).exp.aestronglyMeasurable
  · apply ae_of_all
    intro q
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      exp_two_positiveLogNorm_le (randomFourier a q)

theorem integral_exp_two_positiveLogNorm_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    (∫ q, Real.exp (2 * positiveLogNorm (randomFourier a q)) ∂fourierMeasure N) ≤ 2 := by
  have h := integral_mono (integrable_exp_two_positiveLogNorm a)
    ((integrable_const 1).add (integrable_norm_sq_randomFourier a))
    (fun q => exp_two_positiveLogNorm_le (randomFourier a q))
  simpa only [Pi.add_apply, integral_add (integrable_const 1) (integrable_norm_sq_randomFourier a),
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_norm_sq_randomFourier, ha, one_add_one_eq_two] using h

theorem integrable_rpow_positiveLogNorm {N : ℕ} (a : Fin (N + 1) → ℂ)
    {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun q => positiveLogNorm (randomFourier a q) ^ p) (fourierMeasure N) := by
  have hm : Measurable (fun q => positiveLogNorm (randomFourier a q)) :=
    (measurable_randomFourier a).norm.log.max measurable_const
  have hi : Integrable (fun q =>
      Real.exp (2 * |positiveLogNorm (randomFourier a q)| ^ (1 : ℝ)⁻¹))
      (fourierMeasure N) := by
    simpa only [inv_one, Real.rpow_one, abs_of_nonneg (positiveLogNorm_nonneg _)] using
      integrable_exp_two_positiveLogNorm a
  simpa only [abs_of_nonneg (positiveLogNorm_nonneg _)] using
    integrable_abs_rpow_of_stretchedExponential hm (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 2) hp hi

theorem integral_rpow_positiveLogNorm_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 0 ≤ p) :
    (∫ q, positiveLogNorm (randomFourier a q) ^ p ∂fourierMeasure N) ≤
      (p / 2) ^ p * 2 := by
  have hm : Measurable (fun q => positiveLogNorm (randomFourier a q)) :=
    (measurable_randomFourier a).norm.log.max measurable_const
  have hi : Integrable (fun q =>
      Real.exp (2 * |positiveLogNorm (randomFourier a q)| ^ (1 : ℝ)⁻¹))
      (fourierMeasure N) := by
    simpa only [inv_one, Real.rpow_one, abs_of_nonneg (positiveLogNorm_nonneg _)] using
      integrable_exp_two_positiveLogNorm a
  have h := integral_abs_rpow_le_stretchedExponential hm (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 2) hp hi
  simp only [inv_one, Real.rpow_one, abs_of_nonneg (positiveLogNorm_nonneg _), one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (integral_exp_two_positiveLogNorm_le a ha)
    (Real.rpow_nonneg (by positivity) _))

theorem integrable_abs_log_norm_rpow_iff {N : ℕ} (a : Fin (N + 1) → ℂ)
    {p : ℝ} (hp : 0 < p) :
    Integrable (fun q => |Real.log ‖randomFourier a q‖| ^ p) (fourierMeasure N) ↔
      Integrable (fun q => negativeLogNorm (randomFourier a q) ^ p) (fourierMeasure N) := by
  have hpos := integrable_rpow_positiveLogNorm a hp.le
  constructor
  · intro h
    apply (h.sub hpos).congr
    apply ae_of_all
    intro q
    simp only [Pi.sub_apply, abs_log_norm_rpow_eq _ hp, add_sub_cancel_left]
  · intro h
    apply (hpos.add h).congr
    exact ae_of_all _ (fun q => (abs_log_norm_rpow_eq (randomFourier a q) hp).symm)

theorem integral_abs_log_norm_rpow_eq {N : ℕ} (a : Fin (N + 1) → ℂ)
    {p : ℝ} (hp : 0 < p)
    (hneg : Integrable (fun q => negativeLogNorm (randomFourier a q) ^ p) (fourierMeasure N)) :
    (∫ q, |Real.log ‖randomFourier a q‖| ^ p ∂fourierMeasure N) =
      (∫ q, positiveLogNorm (randomFourier a q) ^ p ∂fourierMeasure N) +
        ∫ q, negativeLogNorm (randomFourier a q) ^ p ∂fourierMeasure N := by
  simp_rw [abs_log_norm_rpow_eq _ hp]
  exact integral_add (integrable_rpow_positiveLogNorm a hp.le) hneg

end LogMoments
end Erdos522
