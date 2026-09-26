/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicAnnularWidth

/-!
# Power margins at logarithmic annular width

An exponential factor in the width becomes a small power of the degree.
Positive power margins therefore absorb every fixed logarithmic factor. At the
critical margin `a / 128`, the correction `log log N` in the width supplies the
factor `(log N)^(-a)`, which absorbs polynomial and logarithmic factors of total
order less than `a`. The width is asymptotic to `log N / 128`.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- Explicit domination of a polynomial-exponential width factor. -/
theorem logarithmicAnnularWidth_factor_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {a b : ℝ} (ha : 0 ≤ a) (m p : ℕ) :
    (logarithmicAnnularWidth N + 1) ^ m * Real.exp (a * logarithmicAnnularWidth N) *
        (Real.log N) ^ p / (N : ℝ) ^ b ≤
      2 ^ m * (Real.log N) ^ (m + p) / (N : ℝ) ^ (b - a / 128) := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hK := logarithmicAnnularWidth_nonneg N
  calc
    _ ≤ (2 * Real.log N) ^ m * (N : ℝ) ^ (a / 128) *
        (Real.log N) ^ p / (N : ℝ) ^ b := by
      gcongr
      · exact logarithmicAnnularWidth_add_one_le hlog
      · exact exp_mul_logarithmicAnnularWidth_le hlog ha
    _ = 2 ^ m * (Real.log N) ^ (m + p) *
        ((N : ℝ) ^ (a / 128) / (N : ℝ) ^ b) := by rw [mul_pow, pow_add]; ring
    _ = _ := by rw [← Real.rpow_sub hn, show a / 128 - b = -(b - a / 128) by ring,
      Real.rpow_neg hn.le]; ring

/-- Every positive degree-power margin dominates polynomial-exponential width
factors at the logarithmic annular scale. -/
theorem tendsto_logarithmicAnnularWidth_factor {a b : ℝ} (ha : 0 ≤ a)
    (hab : a / 128 < b) (m p : ℕ) :
    Tendsto (fun N : ℕ =>
      (logarithmicAnnularWidth N + 1) ^ m * Real.exp (a * logarithmicAnnularWidth N) *
        (Real.log N) ^ p / (N : ℝ) ^ b) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div_nat_rpow (m + p) (sub_pos.mpr hab)).const_mul (2 ^ m : ℝ)
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl : 0 ≤ Real.log N := (show 1 ≤ Real.log N from hN).trans' zero_le_one
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    simpa only [mul_div_assoc] using logarithmicAnnularWidth_factor_le hN ha m p

/-- Explicit domination at the critical margin `a / 128`: the correction
`log log N` in the width turns `exp(a K)` into `N^(a/128) (log N)^(-a)`. -/
theorem logarithmicAnnularWidth_critical_factor_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    (hll : Real.log (Real.log N) ≤ Real.log N / 128) {a : ℝ} (ha : 0 ≤ a) (m p : ℕ) :
    (logarithmicAnnularWidth N + 1) ^ m * Real.exp (a * logarithmicAnnularWidth N) *
        (Real.log N) ^ p / (N : ℝ) ^ (a / 128) ≤
      2 ^ m * Real.log N ^ ((m + p : ℝ) - a) := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hl : 0 < Real.log N := by linarith
  have hK := logarithmicAnnularWidth_nonneg N
  have hNa : 0 < (N : ℝ) ^ (a / 128) := Real.rpow_pos_of_pos hn _
  calc
    _ ≤ (2 * Real.log N) ^ m * ((N : ℝ) ^ (a / 128) * Real.log N ^ (-a)) *
        (Real.log N) ^ p / (N : ℝ) ^ (a / 128) := by
      gcongr
      · exact logarithmicAnnularWidth_add_one_le hlog
      · exact exp_mul_logarithmicAnnularWidth_le_log hlog hll ha
    _ = 2 ^ m * (Real.log N ^ (m : ℝ) * Real.log N ^ (p : ℝ) * Real.log N ^ (-a)) := by
      rw [Real.rpow_natCast, Real.rpow_natCast, mul_pow]
      field_simp
    _ = _ := by rw [← Real.rpow_add hl, ← Real.rpow_add hl, ← sub_eq_add_neg]

/-- At the critical margin `a / 128`, the width factor still vanishes whenever
the polynomial and logarithmic orders together are smaller than `a`. -/
theorem tendsto_logarithmicAnnularWidth_critical_factor {a : ℝ} {m p : ℕ}
    (hmpa : (m + p : ℝ) < a) :
    Tendsto (fun N : ℕ =>
      (logarithmicAnnularWidth N + 1) ^ m * Real.exp (a * logarithmicAnnularWidth N) *
        (Real.log N) ^ p / (N : ℝ) ^ (a / 128)) atTop (𝓝 0) := by
  have ha : 0 ≤ a := by
    have : (0 : ℝ) ≤ m + p := by positivity
    linarith
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hmpa)).comp hlog).const_mul (2 ^ m : ℝ)
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [hlog.eventually_ge_atTop 1] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl : 0 ≤ Real.log N := (show 1 ≤ Real.log N from hN).trans' zero_le_one
    positivity
  · filter_upwards [eventually_log_log_le_log_div] with N hN
    rw [Function.comp_apply, Function.comp_apply, neg_sub]
    exact logarithmicAnnularWidth_critical_factor_le hN.1 hN.2 ha m p

/-- The growing annular width has its exact logarithmic asymptotic scale. -/
theorem tendsto_logarithmicAnnularWidth_div_log :
    Tendsto (fun N : ℕ => logarithmicAnnularWidth N / Real.log N) atTop (𝓝 (1 / 128)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlower : Tendsto (fun N : ℕ => 1 / 128 - Real.log (Real.log N) / Real.log N -
      (Real.log N)⁻¹) atTop (𝓝 (1 / 128)) := by
    have h := (tendsto_const_nhds (x := (1 / 128 : ℝ))).sub hratio |>.sub hinv
    simpa only [sub_zero, Function.comp_def, id] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [hlog.eventually_ge_atTop 1] with N hN
    change 1 ≤ Real.log N at hN
    have hl : 0 < Real.log N := by linarith
    have h := sub_one_lt_logarithmicAnnularWidth N
    rw [le_div_iff₀ hl]
    have he : (1 / 128 - Real.log (Real.log N) / Real.log N - (Real.log N)⁻¹) * Real.log N =
        Real.log N / 128 - Real.log (Real.log N) - 1 := by field_simp
    linarith
  · filter_upwards [hlog.eventually_ge_atTop 1] with N hN
    change 1 ≤ Real.log N at hN
    have hl : 0 < Real.log N := by linarith
    rw [div_le_iff₀ hl]
    linarith [logarithmicAnnularWidth_le hN]

/-- The logarithmic width tends to infinity. -/
theorem tendsto_logarithmicAnnularWidth_atTop :
    Tendsto logarithmicAnnularWidth atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := tendsto_logarithmicAnnularWidth_div_log.pos_mul_atTop (by norm_num) hlog
  apply h.congr'
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  change 1 ≤ Real.log N at hN
  exact div_mul_cancel₀ _ (by linarith)

/-- The reciprocal of the width minus one carries the coefficient `128` in the
logarithmic rate. -/
theorem tendsto_log_div_logarithmicAnnularWidth_sub_one :
    Tendsto (fun N : ℕ => Real.log N / (logarithmicAnnularWidth N - 1)) atTop (𝓝 128) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have h := (tendsto_logarithmicAnnularWidth_div_log.sub hinv).inv₀ (by norm_num)
  norm_num only [sub_zero, one_div, inv_inv] at h
  apply h.congr'
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  change 1 ≤ Real.log N at hN
  have hl : Real.log N ≠ 0 := by positivity
  simp only [Function.comp_apply]
  rw [← inv_div]
  field_simp

/-- The Gaussian density coefficient has exponential width rate six. -/
theorem annularJetDensityCoefficient_eq_exp (K : ℝ) :
    annularJetDensityCoefficient K (annularDerivativeScale K) =
      annularJetDensityCoefficient 0 (annularDerivativeScale 0) * Real.exp (6 * K) := by
  rw [annularDerivativeScale_eq_exp]
  unfold annularJetDensityCoefficient
  simp only [mul_zero, Real.exp_zero]
  rw [mul_pow, div_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have h : Real.exp ((2 : ℕ) * K) * Real.exp ((2 : ℕ) * (-4 * K)) = Real.exp (-6 * K) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  calc
    _ = (9 / (1024 * annularDerivativeScale 0 ^ 2 * ((1 : ℝ) / 80) ^ 2)) /
        (Real.exp ((2 : ℕ) * K) * Real.exp ((2 : ℕ) * (-4 * K))) := by ring
    _ = _ := by rw [h, show -6 * K = -(6 * K) by ring, Real.exp_neg]; simp only [div_inv_eq_mul]

end Erdos522
