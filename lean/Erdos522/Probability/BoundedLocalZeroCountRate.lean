/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedLocalZeroCount

/-!
# Logarithmic local-count constants for bounded symmetric laws

An arc of half-width `786432 π B² log N / N` makes the conditional energy
failure summable. The separate amplitude tail fits the same budget once
`12 B⁴ log N ≤ N+1`.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522.BoundedLocalZeroCount

/-- Logarithmic arc scale for a coefficient modulus bound `B`. -/
def arcScale (B : ℝ) : ℝ := 786432 * Real.pi * B ^ 2

/-- The local closed-disk zero-count constant for bounded symmetric coefficients. -/
def localCountConstant (B K : ℝ) : ℝ :=
  (4 * arcScale B + 4 * K + Real.log B + 5) / Real.log 2

theorem arcScale_ge_sign_scale {B : ℝ} (hB : 1 ≤ B) : ArcEnergy.arcScale ≤ arcScale B := by
  unfold ArcEnergy.arcScale arcScale
  have hsq : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hB
  nlinarith [Real.pi_pos]

/-- The conditional arc-energy term is at most `2N⁻²⁴`. -/
theorem arc_energy_exponential_le {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : 0 < B) :
    2 * Real.exp (-((N + 1 : ℝ) * (arcScale B * Real.log N / N / Real.pi)) /
      (32768 * B ^ 2)) ≤ 2 / (N : ℝ) ^ 24 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hquot : 24 * Real.log N ≤
      ((N + 1 : ℝ) * (arcScale B * Real.log N / N / Real.pi)) / (32768 * B ^ 2) := by
    have heq : ((N + 1 : ℝ) * (arcScale B * Real.log N / N / Real.pi)) /
        (32768 * B ^ 2) = 24 * Real.log N * ((N + 1 : ℝ) / N) := by
      unfold arcScale
      field_simp
      ring
    rw [heq]
    have hratio : (1 : ℝ) ≤ (N + 1 : ℝ) / N := (one_le_div hn).mpr (by linarith)
    nlinarith
  calc
    _ ≤ 2 * Real.exp (-(24 * Real.log N)) := by
      gcongr
      simpa only [neg_div] using neg_le_neg hquot
    _ = _ := by
      rw [Real.exp_neg, show (24 : ℝ) = (24 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hn, div_eq_mul_inv]

/-- The amplitude-energy term is at most `N⁻⁶` under the displayed finite threshold. -/
theorem amplitude_energy_exponential_le {N : ℕ} (hN : 0 < N) {B : ℝ} (hB : 0 < B)
    (hscale : 12 * B ^ 4 * Real.log N ≤ N + 1) :
    Real.exp (-(N + 1 : ℝ) / (2 * B ^ 4)) ≤ 1 / (N : ℝ) ^ 6 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hquot : 6 * Real.log N ≤ (N + 1 : ℝ) / (2 * B ^ 4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  calc
    _ ≤ Real.exp (-(6 * Real.log N)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hquot
    _ = _ := by
      rw [Real.exp_neg, show (6 : ℝ) = (6 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hn, one_div]

/-- At most `8N` arcs fit inside the combined `N⁻³` failure budget. -/
theorem angular_cover_failure_budget {N J : ℕ} (hN : 4 ≤ N) (hJ : J ≤ 8 * N) :
    (J : ℝ) * (2 / (N : ℝ) ^ 24 + 1 / (N : ℝ) ^ 6) ≤ 1 / (N : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hJr : (J : ℝ) ≤ 8 * N := by exact_mod_cast hJ
  have h20 : (32 : ℝ) ≤ (N : ℝ) ^ 20 := by
    calc
      (32 : ℝ) ≤ 4 ^ 20 := by norm_num
      _ ≤ (N : ℝ) ^ 20 := by gcongr
  have h2 : (16 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hfirst : 16 / (N : ℝ) ^ 20 ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hn _)).mpr
    linarith
  have hsecond : 8 / (N : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hn _)).mpr
    linarith
  calc
    _ ≤ (8 * N) * (2 / (N : ℝ) ^ 24 + 1 / (N : ℝ) ^ 6) := by gcongr
    _ = (16 / (N : ℝ) ^ 20 + 8 / (N : ℝ) ^ 2) * (1 / (N : ℝ) ^ 3) := by field_simp; ring
    _ ≤ 1 * (1 / (N : ℝ) ^ 3) := by gcongr; linarith
    _ = _ := one_mul _

/-- The exact Jensen numerator is bounded by the logarithmic local-count constant. -/
theorem local_jensen_quotient_le {N : ℕ} (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    {B K : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K) :
    (Real.log B + Real.log (N + 1) / 2 + Real.log 2 +
      2 * N * ((2 * K + 1) / N + 2 * (arcScale B * Real.log N / N))) / Real.log 2 ≤
        localCountConstant B K * Real.log N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogB := Real.log_nonneg hB
  have hlogNp : Real.log (N + 1 : ℝ) ≤ Real.log (N : ℝ) + Real.log 2 := by
    calc
      _ ≤ Real.log ((N : ℝ) * 2) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul hn.ne' (by norm_num)
  have heq : 2 * (N : ℝ) * ((2 * K + 1) / N + 2 * (arcScale B * Real.log N / N)) =
      4 * K + 2 + 4 * arcScale B * Real.log N := by field_simp; ring
  rw [heq, localCountConstant, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * K + Real.log B + 4) (sub_nonneg.mpr hlog)]

/-- The simultaneous local zero-count theorem for bounded centrally symmetric
complex coefficient laws, with an explicit finite `N⁻³` failure budget. -/
theorem simultaneous_local_zero_count (N : ℕ) (hN : 4 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] {B K : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1)
    (hwidth : arcScale B * Real.log N / N ≤ 1)
    (hamplitude : 12 * B ^ 4 * Real.log N ≤ N + 1) :
    (Measure.pi μ).real {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      localCountConstant B K * Real.log N <
        (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
          1 / (N : ℝ) ^ 3 := by
  have hN2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hl0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hwidthMono : ArcEnergy.arcScale * Real.log N / N ≤ arcScale B * Real.log N / N := by
    gcongr
    exact arcScale_ge_sign_scale hB
  have hlog := LocalZeroCount.one_le_log_of_arcWidth_le_one hN2 (hwidthMono.trans hwidth)
  obtain ⟨J, hJ, hcover⟩ := LocalZeroCount.exists_logarithmic_angular_cover hN2 hlog
  have hh : 0 < arcScale B * Real.log N / N := by unfold arcScale; positivity
  have hcover' : ∀ φ, ∃ i : Fin J, dist φ (LocalZeroCount.angularGrid J i) ≤
      (arcScale B * Real.log N / N) / (2 * Real.pi) := by
    intro φ
    obtain ⟨i, hi⟩ := hcover φ
    exact ⟨i, hi.trans (div_le_div_of_nonneg_right hwidthMono (by positivity))⟩
  have hp := simultaneous_local_count_of_cover N hN2 μ hB hh
    (hwidth.trans (by linarith [Real.two_le_pi])) hbound hmean (LocalZeroCount.angularGrid J) hcover' hK
  have hsmall := (measureReal_mono (μ := Measure.pi μ) (show
      {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
        localCountConstant B K * Real.log N <
          (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ⊆
      {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
        (Real.log B + Real.log (N + 1) / 2 + Real.log 2 +
          2 * N * ((2 * K + 1) / N + 2 * (arcScale B * Real.log N / N))) / Real.log 2 <
            (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} from by
      rintro a ⟨z₀, hz₀, hc⟩
      exact ⟨z₀, hz₀, lt_of_le_of_lt (local_jensen_quotient_le hN2 hlog hB hK) hc⟩)).trans hp
  apply hsmall.trans
  simp only [Fintype.card_fin]
  apply le_trans _ (angular_cover_failure_budget hN hJ)
  gcongr
  · exact arc_energy_exponential_le hN2 hB0
  · exact amplitude_energy_exponential_le (by omega) hB0 hamplitude

end Erdos522.BoundedLocalZeroCount
