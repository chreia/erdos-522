/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedSymmetricArcEnergy
import Erdos522.Probability.ComplexLocalZeroCount

/-!
# Local zero counts for bounded symmetric complex coefficients

The local Jensen numerator contains the coefficient bound through `log B`.
The exceptional probability is the sum of the conditional arc-energy tail and
the total-amplitude lower tail, multiplied by the finite angular cover size.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522.BoundedLocalZeroCount

/-- The coefficient bound gives exponential growth on a disk centered on the
unit circle. -/
theorem norm_eval_ofFn_le_exp {N : ℕ} (a : Fin (N + 1) → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B)
    {c z : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall c (2 * R)) :
    ‖(Polynomial.ofFn (N + 1) a).eval z‖ ≤ B * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
  have hnorm : ‖z‖ ≤ 1 + 2 * R := by
    have htri := norm_le_norm_sub_add z c
    have hdist : ‖z - c‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [hc] at htri
    linarith
  have hb := BoundedPolynomialSuprema.norm_iterate_derivative_ofFn_le N 0 a hB ha
    (by linarith : 1 ≤ 1 + 2 * R) hnorm
  simp only [Function.iterate_zero, id_eq, pow_zero, one_mul] at hb
  apply hb.trans
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + 2 * R)
    (by simpa only [add_comm] using Real.add_one_le_exp (2 * R)) N
  calc
    _ ≤ Real.exp (2 * R) ^ N := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A squared value at least `(N+1)/4` gives the explicit bounded-coefficient
Jensen quotient, with all root multiplicities retained. -/
theorem zero_count_bound_of_large_circle_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B)
    {c : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 < R)
    (hlarge : (N + 1 : ℝ) / 4 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall c R) : ℝ) ≤
      (Real.log B + Real.log (N + 1) / 2 + Real.log 2 + 2 * N * R) / Real.log 2 := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hnorm : 0 < ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    by_contra! h
    have hz : ‖(Polynomial.ofFn (N + 1) a).eval c‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hlarge
    nlinarith
  have hM : 1 ≤ B * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
    have hexp : 1 ≤ Real.exp (2 * N * R) := Real.one_le_exp (by positivity)
    have hn : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ B * (N + 1 : ℝ) * Real.exp (2 * N * R) := by gcongr
  have hbase := local_zero_count_bound (Polynomial.ofFn (N + 1) a) c hR (by linarith : R < 2 * R)
    hM (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_eval_ofFn_le_exp a hB0.le ha hc hR.le (Metric.sphere_subset_closedBall hz))
  have hloglarge : Real.log (N + 1) / 2 - Real.log 2 ≤
      Real.log ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    have h := Real.log_le_log (by positivity : 0 < (N + 1 : ℝ) / 4) hlarge
    rw [Real.log_div hN1.ne' (by norm_num), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h
    linarith
  rw [show (2 * R) / R = 2 by field_simp,
    Real.log_mul (mul_ne_zero hB0.ne' hN1.ne') (Real.exp_ne_zero _),
    Real.log_mul hB0.ne' hN1.ne', Real.log_exp] at hbase
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith

theorem local_count_of_nearby_large_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B)
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hN : 0 < N)
    {z₀ c : ℂ} (hc : ‖c‖ = 1) (hdist : dist z₀ c ≤ 1 / (N : ℝ) + 2 * h)
    (hlarge : (N + 1 : ℝ) / 4 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      (Real.log B + Real.log (N + 1) / 2 + Real.log 2 +
        2 * N * ((2 * K + 1) / N + 2 * h)) / Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 < (2 * K + 1) / (N : ℝ) + 2 * h := by positivity
  have hsub : Metric.closedBall z₀ (2 * K / (N : ℝ)) ⊆
      Metric.closedBall c ((2 * K + 1) / N + 2 * h) := by
    intro z hz
    have hzdist : dist z z₀ ≤ 2 * K / N := hz
    have htri := dist_triangle z z₀ c
    change dist z c ≤ _
    have heq : (2 * K + 1) / (N : ℝ) = 2 * K / N + 1 / N := by ring
    rw [heq]
    linarith
  have hcount : (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall c ((2 * K + 1) / N + 2 * h)) := by
    exact_mod_cast zeroCountIn_mono (Polynomial.ofFn (N + 1) a) hsub
  exact hcount.trans (zero_count_bound_of_large_circle_value a hB ha hc hR hlarge)

/-- The finite-cover large-value probability under actual bounded symmetric
coefficient laws. -/
theorem simultaneous_large_values (N : ℕ)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] {B h : ℝ} (hB : 0 < B) (hh : 0 < h) (hπ : h ≤ Real.pi)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1)
    {ι : Type*} [Fintype ι] (θ : ι → ArcEnergy.Angle) :
    (Measure.pi μ).real {a | ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) h,
      ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 4} ≤
      (Fintype.card ι : ℝ) *
        (2 * Real.exp (-((N + 1 : ℝ) * (h / Real.pi)) / (32768 * B ^ 2)) +
          Real.exp (-(N + 1 : ℝ) / (2 * B ^ 4))) := by
  have hsub : {a : Fin (N + 1) → ℂ | ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) h,
      ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 4} ⊆
      ⋃ i, {a | ArcEnergy.complexEnergy a (ArcEnergy.arc (θ i) h) ≤
        (N + 1 : ℝ) * (h / Real.pi) / 4} := by
    intro a ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hm := ArcEnergy.angularMeasure_arc (θ i) hh.le hπ
    have hc : Continuous (fun θ : ArcEnergy.Angle => ‖ArcEnergy.complexFourierSum a θ‖ ^ 2) := by
      unfold ArcEnergy.complexFourierSum
      fun_prop
    have hint := setIntegral_mono_on (μ := ArcEnergy.angularMeasure)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
      (integrableOn_const (by finiteness)) (ArcEnergy.measurableSet_arc _ _) hi
    rw [setIntegral_const, smul_eq_mul, hm] at hint
    change ArcEnergy.complexEnergy _ _ ≤ _
    unfold ArcEnergy.complexEnergy
    convert hint using 1
    ring
  have hp := (measureReal_mono (μ := Measure.pi μ) hsub).trans (measureReal_iUnion_fintype_le _)
  apply hp.trans
  have hpoint (i : ι) := ArcEnergy.complexEnergy_lower_tail_of_norm_le μ hB hbound hmean
    (ArcEnergy.arc (θ i) h) (by rw [ArcEnergy.angularMeasure_arc (θ i) hh.le hπ]; positivity)
  simp only [ArcEnergy.angularMeasure_arc _ hh.le hπ] at hpoint
  simpa [mul_add] using Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hpoint i)

/-- A finite angular cover controls every nearby closed-disk root count,
with its precise bounded-symmetric exceptional probability. -/
theorem simultaneous_local_count_of_cover (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] {B h : ℝ} (hB : 1 ≤ B) (hh : 0 < h) (hπ : h ≤ Real.pi)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1)
    {ι : Type*} [Fintype ι] (θ : ι → ArcEnergy.Angle)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤ h / (2 * Real.pi)) {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi μ).real {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      (Real.log B + Real.log (N + 1) / 2 + Real.log 2 +
        2 * N * ((2 * K + 1) / N + 2 * h)) / Real.log 2 <
      (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      (Fintype.card ι : ℝ) *
        (2 * Real.exp (-((N + 1 : ℝ) * (h / Real.pi)) / (32768 * B ^ 2)) +
          Real.exp (-(N + 1 : ℝ) / (2 * B ^ 4))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  apply le_trans _ (simultaneous_large_values N μ (zero_lt_one.trans_le hB) hh hπ hbound hmean θ)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [BoundedPolynomialSuprema.ae_coordinate_norm_le μ hbound] with a ha
  intro ⟨z₀, hz₀, hcount⟩
  by_contra hfailure
  change ¬ ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) h,
    ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 4 at hfailure
  push Not at hfailure
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_sub, abs_neg, abs_one] at hz₀
    have h := (one_le_div hN0).mp hz₀
    linarith
  have hvalues : ∀ i, ∃ t ∈ ArcEnergy.arc (θ i) h,
      (N + 1 : ℝ) / 4 ≤ ‖(Polynomial.ofFn (N + 1) a).eval (AddCircle.toCircle t : ℂ)‖ ^ 2 := by
    intro i
    obtain ⟨t, ht, hlarge⟩ := hfailure i
    exact ⟨t, ht, by rw [ComplexLocalZeroCount.eval_ofFn_circle]; exact hlarge.le⟩
  obtain ⟨c, hc, hdist, hlarge⟩ := ComplexLocalZeroCount.exists_large_value_near_center
    (Polynomial.ofFn (N + 1) a) θ hcover hvalues hz₀ne
  have hupper := local_count_of_nearby_large_value a hB ha hK hh.le (by omega) hc
    (hdist.trans (by linarith)) hlarge
  exact (not_lt_of_ge hupper) hcount

end Erdos522.BoundedLocalZeroCount
