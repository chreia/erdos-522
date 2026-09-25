/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianCoefficients
import Erdos522.Probability.RademacherLogMoments
import Erdos522.Probability.LogMoments.ExponentialTails

/-!
# Uniform logarithmic moments of Gaussian sums

A normalized complex sum of independent real Gaussians has a projection of
variance at least one half.  Its linear small-ball bound controls the negative
logarithm, while unit quadratic energy controls the positive logarithm.
Together these give the bound `(16p)^p`, uniformly in all finite coefficients.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Erdos522
open LogMoments

/-- The negative logarithm has a linear exponential tail uniformly over normalized coefficients. -/
theorem negative_log_complexGaussianSum_tail {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {s : ℝ} (hs : 0 < s) :
    gaussianCoefficientMeasure n {g | s ≤ negativeLogNorm (complexGaussianSum a g)} ≤
      ENNReal.ofReal (2 * Real.exp (-s)) := by
  refine (measure_mono (show {g | s ≤ negativeLogNorm (complexGaussianSum a g)} ⊆
      {g | ‖complexGaussianSum a g‖ ≤ Real.exp (-s)} from ?_)).trans
    (complexGaussianSum_small_ball a ha (Real.exp_pos _).le)
  intro g hg
  change s ≤ max (-Real.log ‖complexGaussianSum a g‖) 0 at hg
  have hl : Real.log ‖complexGaussianSum a g‖ ≤ -s := by
    rcases le_max_iff.mp hg with h | h
    · linarith
    · linarith
  by_cases hz : complexGaussianSum a g = 0
  · simpa only [hz, norm_zero, mem_ofPred_eq] using (Real.exp_pos (-s)).le
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mp hl

/-- The negative logarithm has a uniformly bounded exponential moment. -/
theorem negative_log_complexGaussianSum_exponential {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    Integrable (fun g => Real.exp ((1 / 2 : ℝ) * negativeLogNorm (complexGaussianSum a g)))
      (gaussianCoefficientMeasure n) ∧
    (∫ g, Real.exp ((1 / 2 : ℝ) * negativeLogNorm (complexGaussianSum a g))
      ∂gaussianCoefficientMeasure n) ≤ 3 := by
  apply integrable_exp_half_and_integral_le
  · exact (measurable_complexGaussianSum a).norm.log.neg.max measurable_const
  · exact fun _ => negativeLogNorm_nonneg _
  · exact fun _ hs => negative_log_complexGaussianSum_tail a ha hs

/-- The positive logarithm is controlled by quadratic energy. -/
theorem positive_log_complexGaussianSum_exponential {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    Integrable (fun g => Real.exp (2 * positiveLogNorm (complexGaussianSum a g)))
      (gaussianCoefficientMeasure n) ∧
    (∫ g, Real.exp (2 * positiveLogNorm (complexGaussianSum a g))
      ∂gaussianCoefficientMeasure n) ≤ 2 := by
  have hdom := (integrable_const (1 : ℝ)).add (integrable_norm_sq_complexGaussianSum a)
  have hI : Integrable (fun g => Real.exp (2 * positiveLogNorm (complexGaussianSum a g)))
      (gaussianCoefficientMeasure n) := by
    apply hdom.mono'
    · exact (((measurable_complexGaussianSum a).norm.log.max measurable_const).const_mul 2).exp.aestronglyMeasurable
    · filter_upwards with g
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        exp_two_positiveLogNorm_le (complexGaussianSum a g)
  refine ⟨hI, ?_⟩
  have h := integral_mono hI hdom (fun g => exp_two_positiveLogNorm_le (complexGaussianSum a g))
  simpa only [Pi.add_apply, integral_add (integrable_const 1) (integrable_norm_sq_complexGaussianSum a),
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_norm_sq_complexGaussianSum, ha, one_add_one_eq_two] using h

/-- A half-exponential of the absolute logarithm has expectation at most five. -/
theorem abs_log_complexGaussianSum_exponential {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    Integrable (fun g => Real.exp ((1 / 2 : ℝ) * |Real.log ‖complexGaussianSum a g‖|))
      (gaussianCoefficientMeasure n) ∧
    (∫ g, Real.exp ((1 / 2 : ℝ) * |Real.log ‖complexGaussianSum a g‖|)
      ∂gaussianCoefficientMeasure n) ≤ 5 := by
  obtain ⟨hp, hpB⟩ := positive_log_complexGaussianSum_exponential a ha
  obtain ⟨hn, hnB⟩ := negative_log_complexGaussianSum_exponential a ha
  have hpoint (g : Fin n → ℝ) :
      Real.exp ((1 / 2 : ℝ) * |Real.log ‖complexGaussianSum a g‖|) ≤
        Real.exp (2 * positiveLogNorm (complexGaussianSum a g)) +
        Real.exp ((1 / 2 : ℝ) * negativeLogNorm (complexGaussianSum a g)) := by
    rcases le_total 0 (Real.log ‖complexGaussianSum a g‖) with h | h
    · rw [abs_of_nonneg h]
      have hle : Real.exp ((1 / 2 : ℝ) * Real.log ‖complexGaussianSum a g‖) ≤
          Real.exp (2 * positiveLogNorm (complexGaussianSum a g)) := by
        apply Real.exp_le_exp.mpr
        rw [positiveLogNorm, max_eq_left h]
        linarith
      exact hle.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos h]
      exact (le_add_of_nonneg_left (Real.exp_pos _).le).trans_eq (by
        rw [negativeLogNorm, max_eq_left (by linarith : 0 ≤ -Real.log ‖complexGaussianSum a g‖)])
  have hI : Integrable
      (fun g => Real.exp ((1 / 2 : ℝ) * |Real.log ‖complexGaussianSum a g‖|))
      (gaussianCoefficientMeasure n) := by
    apply (hp.add hn).mono'
    · exact (((measurable_complexGaussianSum a).norm.log.norm).const_mul (1 / 2 : ℝ)).exp.aestronglyMeasurable
    · filter_upwards with g
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint g
  refine ⟨hI, ?_⟩
  have h := integral_mono hI (hp.add hn) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hp hn] at h
  linarith

/-- Uniform logarithmic moments for actual finite sums of independent real
Gaussian coefficients, with the manuscript's constant `16` and exponent one. -/
theorem gaussian_logarithmic_moments {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun g => |Real.log ‖complexGaussianSum a g‖| ^ p) (gaussianCoefficientMeasure n) ∧
    (∫ g, |Real.log ‖complexGaussianSum a g‖| ^ p ∂gaussianCoefficientMeasure n) ≤ (16 * p) ^ p := by
  obtain ⟨hI, hB⟩ := abs_log_complexGaussianSum_exponential a ha
  have hI' : Integrable (fun g => Real.exp ((1 / 2 : ℝ) *
      |Real.log ‖complexGaussianSum a g‖| ^ (1 : ℝ)⁻¹)) (gaussianCoefficientMeasure n) := by
    simpa only [inv_one, Real.rpow_one] using hI
  have hm : Measurable (fun g => Real.log ‖complexGaussianSum a g‖) :=
    (measurable_complexGaussianSum a).norm.log
  refine ⟨integrable_abs_rpow_of_stretchedExponential hm (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (zero_le_one.trans hp) hI', ?_⟩
  have h := integral_abs_rpow_le_of_stretchedExponential_bound hm
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 2) hp
    (by norm_num : (1 : ℝ) ≤ 5) hI' (by simpa only [inv_one, Real.rpow_one] using hB)
  simp only [one_mul] at h
  apply h.trans
  apply Real.rpow_le_rpow (by positivity) _ (zero_le_one.trans hp)
  nlinarith

end Erdos522
