/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicAnnularWidth

/-!
# Power margins at logarithmic annular width

An exponential factor in the width becomes a small power of the degree.
Positive power margins therefore absorb every fixed logarithmic factor.
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
      2 ^ m * (Real.log N) ^ (m + p) / (N : ℝ) ^ (b - a / 1000) := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast hn1.le
  have hK := logarithmicAnnularWidth_nonneg N
  calc
    _ ≤ (2 * Real.log N) ^ m * (N : ℝ) ^ (a / 1000) *
        (Real.log N) ^ p / (N : ℝ) ^ b := by
      gcongr
      · exact logarithmicAnnularWidth_add_one_le hlog
      · exact exp_mul_logarithmicAnnularWidth_le hN ha
    _ = 2 ^ m * (Real.log N) ^ (m + p) *
        ((N : ℝ) ^ (a / 1000) / (N : ℝ) ^ b) := by rw [mul_pow, pow_add]; ring
    _ = _ := by rw [← Real.rpow_sub hn, show a / 1000 - b = -(b - a / 1000) by ring,
      Real.rpow_neg hn.le]; ring

/-- Every positive degree-power margin dominates polynomial-exponential width
factors at the logarithmic annular scale. -/
theorem tendsto_logarithmicAnnularWidth_factor {a b : ℝ} (ha : 0 ≤ a)
    (hab : a / 1000 < b) (m p : ℕ) :
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
