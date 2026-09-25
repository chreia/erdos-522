/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

/-!
# Hoeffding bounds for bounded complex coefficients

Independent mean-zero complex coefficients bounded by `B` have sub-Gaussian
real projections. The Euclidean coordinate split gives a complex tail with
denominator `4 B² Σ|aₖ|²`, uniformly in the individual coefficient laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Erdos522

/-- Central symmetry gives mean zero for the complex coefficient law. -/
theorem integral_id_eq_zero_of_negInvariant (μ : Measure ℂ) [μ.IsNegInvariant] :
    (∫ z, z ∂μ) = 0 := by
  have h := integral_neg_eq_self (fun z : ℂ => z) μ
  rw [integral_neg] at h
  exact neg_eq_self.mp h

/-- A contractive real projection of a bounded mean-zero complex coefficient
has the exact Hoeffding proxy `B²|a|²`. -/
theorem hasSubgaussianMGF_bounded_complex_projection
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (T : ℂ →L[ℝ] ℝ)
    (hT : ∀ z, |T z| ≤ ‖z‖) (a : ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hmean : (∫ z, z ∂μ) = 0) :
    HasSubgaussianMGF (fun z => T (a * z))
      (NNReal.mk (B ^ 2 * ‖a‖ ^ 2) (by positivity)) μ := by
  have hab : ∀ᵐ z ∂μ, ‖a * z‖ ≤ ‖a‖ * B := by
    filter_upwards [hbound] with z hz
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  have hint : Integrable (fun z : ℂ => a * z) μ :=
    Integrable.of_bound (by fun_prop) (‖a‖ * B) hab
  have hb : ∀ᵐ z ∂μ, T (a * z) ∈ Set.Icc (-(‖a‖ * B)) (‖a‖ * B) := by
    filter_upwards [hab] with z hz
    exact abs_le.mp ((hT _).trans hz)
  have hm : (∫ z, T (a * z) ∂μ) = 0 := by
    rw [T.integral_comp_comm hint, integral_const_mul, hmean, mul_zero, map_zero]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (by fun_prop) hb hm
  have heq : (‖‖a‖ * B - -(‖a‖ * B)‖₊ / 2) ^ 2 =
      (NNReal.mk (B ^ 2 * ‖a‖ ^ 2) (by positivity)) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [heq] at h
  exact h

/-- Projection of an independent complex sum, with any upper bound for its
deterministic coefficient energy. -/
theorem hasSubgaussianMGF_bounded_complex_sum_projection {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (T : ℂ →L[ℝ] ℝ) (hT : ∀ z, |T z| ≤ ‖z‖) (a : ι → ℂ)
    {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0) :
    HasSubgaussianMGF (fun ω : ι → ℂ => T (∑ k, a k * ω k))
      (NNReal.mk (B ^ 2 * V) (by positivity)) (Measure.pi μ) := by
  let X := fun k (ω : ι → ℂ) => T (a k * ω k)
  have hi : iIndepFun X (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun k z => T (a k * z)) (fun k =>
      (T.continuous.measurable.comp ((measurable_const (a := a k)).mul measurable_id)).aemeasurable)
  have hX (k : ι) : HasSubgaussianMGF (X k)
      (NNReal.mk (B ^ 2 * ‖a k‖ ^ 2) (by positivity)) (Measure.pi μ) := by
    have h := hasSubgaussianMGF_bounded_complex_projection (μ k) T hT (a k) hB
      (hbound k) (hmean k)
    rw [← (measurePreserving_eval μ k).map_eq] at h
    change HasSubgaussianMGF (fun ω : ι → ℂ => T (a k * ω k)) _ (Measure.pi μ)
    exact HasSubgaussianMGF.of_map (μ := Measure.pi μ)
      (Y := fun ω : ι → ℂ => ω k) (X := fun z : ℂ => T (a k * z))
      (measurable_pi_apply k).aemeasurable h
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun k _ => hX k)
  have hfun : (fun ω : ι → ℂ => ∑ k, X k ω) = fun ω => T (∑ k, a k * ω k) := by
    funext ω
    exact (map_sum T _ _).symm
  rw [hfun] at h
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  simp only [NNReal.coe_mk, NNReal.coe_sum]
  rw [← Finset.mul_sum]
  gcongr

/-- Two-sided tails for every real projection of an independent bounded
complex sum. -/
theorem measure_abs_bounded_complex_sum_projection_ge_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (T : ℂ →L[ℝ] ℝ) (hT : ∀ z, |T z| ≤ ‖z‖) (a : ι → ℂ)
    {B V t : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    (ht : 0 ≤ t) :
    (Measure.pi μ).real {ω | t ≤ |T (∑ k, a k * ω k)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * B ^ 2 * V)) := by
  have h := hasSubgaussianMGF_bounded_complex_sum_projection μ T hT a hB hV ha hbound hmean
  have hp := h.measure_ge_le ht
  have hn := h.neg.measure_ge_le ht
  have hs : {ω : ι → ℂ | t ≤ |T (∑ k, a k * ω k)|} ⊆
      {ω | t ≤ T (∑ k, a k * ω k)} ∪ {ω | t ≤ -T (∑ k, a k * ω k)} := by
    intro ω hω
    change t ≤ |T (∑ k, a k * ω k)| at hω
    exact le_abs.mp hω
  have hu := (measureReal_mono (μ := Measure.pi μ) hs).trans (measureReal_union_le _ _)
  change (Measure.pi μ).real {ω | t ≤ T (∑ k, a k * ω k)} ≤
    Real.exp (-t ^ 2 / (2 * (B ^ 2 * V))) at hp
  change (Measure.pi μ).real {ω | t ≤ -T (∑ k, a k * ω k)} ≤
    Real.exp (-t ^ 2 / (2 * (B ^ 2 * V))) at hn
  rw [← mul_assoc] at hp hn
  linarith

/-- The actual finite-product complex Hoeffding inequality. -/
theorem measure_norm_bounded_complex_sum_ge_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] (a : ι → ℂ)
    {B V t : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    (ht : 0 ≤ t) :
    (Measure.pi μ).real {ω | t ≤ ‖∑ k, a k * ω k‖} ≤
      4 * Real.exp (-t ^ 2 / (4 * B ^ 2 * V)) := by
  have htq : 0 ≤ t / Real.sqrt 2 := by positivity
  have hr := measure_abs_bounded_complex_sum_projection_ge_le μ Complex.reCLM
    Complex.abs_re_le_norm a hB hV ha hbound hmean htq
  have hi := measure_abs_bounded_complex_sum_projection_ge_le μ Complex.imCLM
    Complex.abs_im_le_norm a hB hV ha hbound hmean htq
  have hs : {ω : ι → ℂ | t ≤ ‖∑ k, a k * ω k‖} ⊆
      {ω | t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).re|} ∪
      {ω | t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).im|} := by
    intro ω hω
    change t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).re| ∨
      t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).im|
    by_contra! h
    have hr := (sq_lt_sq₀ (abs_nonneg _) htq).mpr h.1
    have hi := (sq_lt_sq₀ (abs_nonneg _) htq).mpr h.2
    rw [sq_abs] at hr hi
    have hn := pow_le_pow_left₀ ht hω 2
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    have hsq : 2 * (t / Real.sqrt 2) ^ 2 = t ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      ring
    nlinarith
  have hu := (measureReal_mono (μ := Measure.pi μ) hs).trans (measureReal_union_le _ _)
  have heq : -(t / Real.sqrt 2) ^ 2 / (2 * B ^ 2 * V) = -t ^ 2 / (4 * B ^ 2 * V) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [heq] at hr hi
  change (Measure.pi μ).real {ω | t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).re|} ≤ _ at hr
  change (Measure.pi μ).real {ω | t / Real.sqrt 2 ≤ |(∑ k, a k * ω k).im|} ≤ _ at hi
  linarith

/-- A finite family of bounded complex sums obeys the corresponding union bound. -/
theorem measure_exists_norm_bounded_complex_sum_ge_le {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] (a : κ → ι → ℂ)
    {B V t : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V) (ha : ∀ i, ∑ k, ‖a i k‖ ^ 2 ≤ V)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    (ht : 0 ≤ t) :
    (Measure.pi μ).real {ω | ∃ i, t ≤ ‖∑ k, a i k * ω k‖} ≤
      (Fintype.card κ : ℝ) * (4 * Real.exp (-t ^ 2 / (4 * B ^ 2 * V))) := by
  rw [show {ω : ι → ℂ | ∃ i, t ≤ ‖∑ k, a i k * ω k‖} =
    ⋃ i, {ω | t ≤ ‖∑ k, a i k * ω k‖} by ext ω; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset κ)) (fun i _ =>
    measure_norm_bounded_complex_sum_ge_le μ (a i) hB hV (ha i) hbound hmean ht)

end Erdos522
