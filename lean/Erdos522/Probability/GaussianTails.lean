/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianCoefficients
import Mathlib.Probability.Moments.SubGaussian

/-!
# Scalar and complex Gaussian tail estimates

The exact projected Gaussian law gives the same energy-sensitive tails as
complex Hoeffding estimates. A finite union controls coefficient truncation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Erdos522

/-- A real Gaussian projection is sub-Gaussian with any upper bound on its coefficient energy. -/
theorem hasSubgaussianMGF_realGaussianSum_of_energy_le {n : ℕ} (a : Fin n → ℝ)
    {V : ℝ} (hV : 0 ≤ V) (ha : ∑ k, a k ^ 2 ≤ V) :
    HasSubgaussianMGF (realGaussianSum a) ⟨V, hV⟩ (gaussianCoefficientMeasure n) := by
  apply (HasSubgaussianMGF.id_map_iff (measurable_realGaussianSum a).aemeasurable).mp
  rw [map_realGaussianSum]
  constructor
  · exact fun t => integrable_exp_mul_gaussianReal t
  · intro t
    rw [mgf_id_gaussianReal]
    simp only [zero_mul, zero_add, Real.coe_toNNReal _ (Finset.sum_nonneg fun k _ => sq_nonneg (a k))]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (sq_nonneg t)) (by norm_num)

/-- A two-sided real Gaussian estimate with the coefficient energy kept explicit. -/
theorem measure_abs_realGaussianSum_ge_le {n : ℕ} (a : Fin n → ℝ)
    {V t : ℝ} (hV : 0 ≤ V) (ha : ∑ k, (a k) ^ 2 ≤ V) (ht : 0 ≤ t) :
    (gaussianCoefficientMeasure n).real {ω | t ≤ |realGaussianSum a ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * V)) := by
  have h := hasSubgaussianMGF_realGaussianSum_of_energy_le a hV ha
  have hpos := h.measure_ge_le ht
  have hneg := h.neg.measure_ge_le ht
  have hsplit : {ω : Fin n → ℝ | t ≤ |realGaussianSum a ω|} ⊆
      {ω | t ≤ realGaussianSum a ω} ∪
      {ω | t ≤ -(realGaussianSum a ω)} := by
    intro ω hω
    change t ≤ |realGaussianSum a ω| at hω
    exact le_abs.mp hω
  have hu := (measureReal_mono (μ := gaussianCoefficientMeasure n) hsplit).trans (measureReal_union_le _ _)
  change (gaussianCoefficientMeasure n).real {ω | t ≤ realGaussianSum a ω} ≤
    Real.exp (-t ^ 2 / (2 * V)) at hpos
  change (gaussianCoefficientMeasure n).real {ω | t ≤ -(realGaussianSum a ω)} ≤
    Real.exp (-t ^ 2 / (2 * V)) at hneg
  linarith

/-- A complex Gaussian estimate obtained by splitting between real and imaginary parts. -/
theorem measure_norm_complexGaussianSum_ge_le {n : ℕ} (a : Fin n → ℂ)
    {V t : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (ht : 0 ≤ t) :
    (gaussianCoefficientMeasure n).real {ω | t ≤ ‖complexGaussianSum a ω‖} ≤
      4 * Real.exp (-t ^ 2 / (8 * V)) := by
  have hre : ∑ k, (a k).re ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).im])).trans ha
  have him : ∑ k, (a k).im ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).re])).trans ha
  have hreal := measure_abs_realGaussianSum_ge_le (fun k => (a k).re) hV.le hre (by positivity : 0 ≤ t / 2)
  have himag := measure_abs_realGaussianSum_ge_le (fun k => (a k).im) hV.le him (by positivity : 0 ≤ t / 2)
  have hsplit : {ω : Fin n → ℝ | t ≤ ‖complexGaussianSum a ω‖} ⊆
      {ω | t / 2 ≤ |(complexGaussianSum a ω).re|} ∪
      {ω | t / 2 ≤ |(complexGaussianSum a ω).im|} := by
    intro ω hω
    change t ≤ ‖complexGaussianSum a ω‖ at hω
    change t / 2 ≤ |(complexGaussianSum a ω).re| ∨ t / 2 ≤ |(complexGaussianSum a ω).im|
    by_contra! h
    have hn := Complex.norm_le_abs_re_add_abs_im (complexGaussianSum a ω)
    linarith [h.1, h.2]
  have hu := (measureReal_mono (μ := gaussianCoefficientMeasure n) hsplit).trans (measureReal_union_le _ _)
  simp only [complexGaussianSum_re, complexGaussianSum_im] at hu
  have heq : -(t / 2) ^ 2 / (2 * V) = -t ^ 2 / (8 * V) := by ring
  rw [heq] at hreal himag
  linarith


/-- A single standard Gaussian coordinate has its usual two-sided tail. -/
theorem gaussian_coordinate_tail (n : ℕ) (k : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianCoefficientMeasure n).real {g | t ≤ |g k|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  classical
  have h := measure_abs_realGaussianSum_ge_le (fun j : Fin n => if j = k then (1 : ℝ) else 0)
    (by norm_num : (0 : ℝ) ≤ 1) (by simp) ht
  simpa [realGaussianSum] using h

/-- A finite coefficient truncation has an explicit union budget. -/
theorem gaussian_coefficient_truncation (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianCoefficientMeasure n).real {g | ∃ k, t < |g k|} ≤
      2 * n * Real.exp (-t ^ 2 / 2) := by
  have hsub : {g : Fin n → ℝ | ∃ k, t < |g k|} ⊆ ⋃ k : Fin n, {g | t ≤ |g k|} := by
    rintro g ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk.le⟩
  have h := (measureReal_mono (μ := gaussianCoefficientMeasure n) hsub).trans
    (measureReal_iUnion_fintype_le _)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (k : Fin n) _ => gaussian_coordinate_tail n k ht)
  apply (h.trans hsum).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Euclidean coordinate split gives the sharper denominator `4V`. -/
theorem measure_norm_complexGaussianSum_ge_le_sharp {n : ℕ} (a : Fin n → ℂ)
    {V t : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (ht : 0 ≤ t) :
    (gaussianCoefficientMeasure n).real {ω | t ≤ ‖complexGaussianSum a ω‖} ≤
      4 * Real.exp (-t ^ 2 / (4 * V)) := by
  have hre : ∑ k, (a k).re ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).im])).trans ha
  have him : ∑ k, (a k).im ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).re])).trans ha
  have hq : 0 ≤ t / Real.sqrt 2 := by positivity
  have hreal := measure_abs_realGaussianSum_ge_le (fun k => (a k).re) hV.le hre hq
  have himag := measure_abs_realGaussianSum_ge_le (fun k => (a k).im) hV.le him hq
  have hqsq : 2 * (t / Real.sqrt 2) ^ 2 = t ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hsplit : {ω : Fin n → ℝ | t ≤ ‖complexGaussianSum a ω‖} ⊆
      {ω | t / Real.sqrt 2 ≤ |(complexGaussianSum a ω).re|} ∪
      {ω | t / Real.sqrt 2 ≤ |(complexGaussianSum a ω).im|} := by
    intro ω hω
    change t ≤ ‖complexGaussianSum a ω‖ at hω
    change t / Real.sqrt 2 ≤ |(complexGaussianSum a ω).re| ∨
      t / Real.sqrt 2 ≤ |(complexGaussianSum a ω).im|
    by_contra! h
    have hr := (sq_lt_sq₀ (abs_nonneg _) hq).mpr h.1
    have hi := (sq_lt_sq₀ (abs_nonneg _) hq).mpr h.2
    rw [sq_abs] at hr hi
    have hn := pow_le_pow_left₀ ht hω 2
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    nlinarith
  have hu := (measureReal_mono (μ := gaussianCoefficientMeasure n) hsplit).trans (measureReal_union_le _ _)
  simp only [complexGaussianSum_re, complexGaussianSum_im] at hu
  have heq : -(t / Real.sqrt 2) ^ 2 / (2 * V) = -t ^ 2 / (4 * V) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [heq] at hreal himag
  linarith


end Erdos522
