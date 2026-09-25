/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.Khintchine

/-!
# Hoeffding bounds for complex Rademacher sums

The real and imaginary parts are sub-Gaussian real sums. Splitting a complex
large-deviation event between its two coordinates gives an explicit tail bound
under the finite product sign law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The sub-Gaussian proxy may be enlarged to any upper bound for the coefficient energy. -/
theorem hasSubgaussianMGF_sign_sum_of_energy_le {N : ℕ} (a : Fin (N + 1) → ℝ)
    {V : ℝ} (hV : 0 ≤ V) (ha : ∑ k, (a k) ^ 2 ≤ V) :
    HasSubgaussianMGF (fun ω : SignVector N => ∑ k, a k * realSign (ω k))
      ⟨V, hV⟩ (signMeasure N) := by
  have h := hasSubgaussianMGF_sign_sum a
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  simp only [NNReal.coe_sum, NNReal.coe_mk]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha (sq_nonneg t)) (by norm_num)

/-- A two-sided real Hoeffding estimate with the coefficient energy kept explicit. -/
theorem measure_abs_sign_sum_ge_le {N : ℕ} (a : Fin (N + 1) → ℝ)
    {V t : ℝ} (hV : 0 ≤ V) (ha : ∑ k, (a k) ^ 2 ≤ V) (ht : 0 ≤ t) :
    (signMeasure N).real {ω | t ≤ |∑ k, a k * realSign (ω k)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * V)) := by
  have h := hasSubgaussianMGF_sign_sum_of_energy_le a hV ha
  have hpos := h.measure_ge_le ht
  have hneg := h.neg.measure_ge_le ht
  have hsplit : {ω : SignVector N | t ≤ |∑ k, a k * realSign (ω k)|} ⊆
      {ω | t ≤ ∑ k, a k * realSign (ω k)} ∪
      {ω | t ≤ -(∑ k, a k * realSign (ω k))} := by
    intro ω hω
    change t ≤ |∑ k, a k * realSign (ω k)| at hω
    exact le_abs.mp hω
  have hu := (measureReal_mono (μ := signMeasure N) hsplit).trans (measureReal_union_le _ _)
  change (signMeasure N).real {ω | t ≤ ∑ k, a k * realSign (ω k)} ≤
    Real.exp (-t ^ 2 / (2 * V)) at hpos
  change (signMeasure N).real {ω | t ≤ -(∑ k, a k * realSign (ω k))} ≤
    Real.exp (-t ^ 2 / (2 * V)) at hneg
  linarith

/-- A complex Hoeffding estimate obtained by splitting between real and imaginary parts. -/
theorem measure_norm_complexSignSum_ge_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V t : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (ht : 0 ≤ t) :
    (signMeasure N).real {ω | t ≤ ‖complexSignSum a ω‖} ≤
      4 * Real.exp (-t ^ 2 / (8 * V)) := by
  have hre : ∑ k, (a k).re ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).im])).trans ha
  have him : ∑ k, (a k).im ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).re])).trans ha
  have hreal := measure_abs_sign_sum_ge_le (fun k => (a k).re) hV.le hre (by positivity : 0 ≤ t / 2)
  have himag := measure_abs_sign_sum_ge_le (fun k => (a k).im) hV.le him (by positivity : 0 ≤ t / 2)
  have hsplit : {ω : SignVector N | t ≤ ‖complexSignSum a ω‖} ⊆
      {ω | t / 2 ≤ |(complexSignSum a ω).re|} ∪
      {ω | t / 2 ≤ |(complexSignSum a ω).im|} := by
    intro ω hω
    change t ≤ ‖complexSignSum a ω‖ at hω
    change t / 2 ≤ |(complexSignSum a ω).re| ∨ t / 2 ≤ |(complexSignSum a ω).im|
    by_contra! h
    have hn := Complex.norm_le_abs_re_add_abs_im (complexSignSum a ω)
    linarith [h.1, h.2]
  have hu := (measureReal_mono (μ := signMeasure N) hsplit).trans (measureReal_union_le _ _)
  simp only [re_complexSignSum, im_complexSignSum] at hu
  have heq : -(t / 2) ^ 2 / (2 * V) = -t ^ 2 / (8 * V) := by ring
  rw [heq] at hreal himag
  linarith

/-- The finite union bound for an arbitrary family of complex sign sums. -/
theorem measure_exists_norm_complexSignSum_ge_le {N : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin (N + 1) → ℂ) {V t : ℝ} (hV : 0 < V)
    (ha : ∀ i, ∑ k, ‖a i k‖ ^ 2 ≤ V) (ht : 0 ≤ t) :
    (signMeasure N).real {ω | ∃ i, t ≤ ‖complexSignSum (a i) ω‖} ≤
      (Fintype.card ι : ℝ) * (4 * Real.exp (-t ^ 2 / (8 * V))) := by
  rw [show {ω : SignVector N | ∃ i, t ≤ ‖complexSignSum (a i) ω‖} =
      ⋃ i, {ω | t ≤ ‖complexSignSum (a i) ω‖} by ext ω; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => measure_norm_complexSignSum_ge_le (a i) hV (ha i) ht)

/-- The Euclidean coordinate split gives the sharper denominator `4V`. -/
theorem measure_norm_complexSignSum_ge_le_sharp {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V t : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (ht : 0 ≤ t) :
    (signMeasure N).real {ω | t ≤ ‖complexSignSum a ω‖} ≤
      4 * Real.exp (-t ^ 2 / (4 * V)) := by
  have hre : ∑ k, (a k).re ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).im])).trans ha
  have him : ∑ k, (a k).im ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).re])).trans ha
  have hq : 0 ≤ t / Real.sqrt 2 := by positivity
  have hreal := measure_abs_sign_sum_ge_le (fun k => (a k).re) hV.le hre hq
  have himag := measure_abs_sign_sum_ge_le (fun k => (a k).im) hV.le him hq
  have hqsq : 2 * (t / Real.sqrt 2) ^ 2 = t ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hsplit : {ω : SignVector N | t ≤ ‖complexSignSum a ω‖} ⊆
      {ω | t / Real.sqrt 2 ≤ |(complexSignSum a ω).re|} ∪
      {ω | t / Real.sqrt 2 ≤ |(complexSignSum a ω).im|} := by
    intro ω hω
    change t ≤ ‖complexSignSum a ω‖ at hω
    change t / Real.sqrt 2 ≤ |(complexSignSum a ω).re| ∨
      t / Real.sqrt 2 ≤ |(complexSignSum a ω).im|
    by_contra! h
    have hr := (sq_lt_sq₀ (abs_nonneg _) hq).mpr h.1
    have hi := (sq_lt_sq₀ (abs_nonneg _) hq).mpr h.2
    rw [sq_abs] at hr hi
    have hn := pow_le_pow_left₀ ht hω 2
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    nlinarith
  have hu := (measureReal_mono (μ := signMeasure N) hsplit).trans (measureReal_union_le _ _)
  simp only [re_complexSignSum, im_complexSignSum] at hu
  have heq : -(t / Real.sqrt 2) ^ 2 / (2 * V) = -t ^ 2 / (4 * V) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [heq] at hreal himag
  linarith

end Erdos522.LogMoments
