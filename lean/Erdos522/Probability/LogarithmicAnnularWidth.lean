/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularConstantGrowth
import Erdos522.Probability.LogarithmicPowerConcentration

/-!
# Constants at a logarithmically growing annular width

At width `⌊log N / 1000⌋`, exponential width factors become small powers of
the degree. The bounds below substitute this width directly into the finite
occupation and derivative-count constants.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The annular width used for the logarithmic rate. -/
def logarithmicAnnularWidth (N : ℕ) : ℝ := (⌊Real.log N / 1000⌋₊ : ℕ)

theorem logarithmicAnnularWidth_nonneg (N : ℕ) : 0 ≤ logarithmicAnnularWidth N :=
  Nat.cast_nonneg _

theorem logarithmicAnnularWidth_le {N : ℕ} (hN : 1 ≤ N) :
    logarithmicAnnularWidth N ≤ Real.log N / 1000 := by
  exact Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (by norm_num))

theorem exp_mul_logarithmicAnnularWidth_le {N : ℕ} (hN : 1 ≤ N)
    {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a * logarithmicAnnularWidth N) ≤ (N : ℝ) ^ (a / 1000) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ Real.exp (a * (Real.log N / 1000)) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (logarithmicAnnularWidth_le hN) ha)
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

theorem logarithmicAnnularWidth_add_one_le {N : ℕ} (hlog : 1 ≤ Real.log N) :
    logarithmicAnnularWidth N + 1 ≤ 2 * Real.log N := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN : 1 ≤ N := by exact_mod_cast hn1.le
  linarith [logarithmicAnnularWidth_le hN]

/-- The occupation constant at the growing width is controlled by a single
fixed constant and a degree power. -/
theorem logarithmicAnnularWidth_occupationConstant_le {N : ℕ} (hN : 1 ≤ N)
    {C : ℝ} (hC : 0 < C) :
    rademacherOccupationConstant C (logarithmicAnnularWidth N) ≤
      rademacherOccupationConstant C 0 * (N : ℝ) ^ (9 / 1000 : ℝ) := by
  exact (rademacherOccupationConstant_le_exp hC (logarithmicAnnularWidth_nonneg N)).trans
    (mul_le_mul_of_nonneg_left (exp_mul_logarithmicAnnularWidth_le hN (by norm_num))
      (rademacherOccupationConstant_pos C 0).le)

/-- The bad-root constant keeps a fourth logarithmic power and exponent `13/1000`. -/
theorem logarithmicAnnularWidth_badRootConstant_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {C : ℝ} (hC : 0 < C) :
    annularSmallDerivativeFailureConstant C (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2) ≤
      16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (13 / 1000 : ℝ) * (Real.log N) ^ 4 := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN : 1 ≤ N := by exact_mod_cast hn1.le
  have hC0 : 0 ≤ annularSmallDerivativeFailureConstant C 0 2 := by
    have hv := annularJetPairConstant_pos C 0 hC
    unfold annularSmallDerivativeFailureConstant
    positivity
  have hK0 := logarithmicAnnularWidth_nonneg N
  calc
    _ ≤ annularSmallDerivativeFailureConstant C 0 2 *
        (logarithmicAnnularWidth N + 1) ^ 4 * Real.exp (13 * logarithmicAnnularWidth N) :=
      annularSmallDerivativeFailureConstant_le_exp hC (logarithmicAnnularWidth_nonneg N)
    _ ≤ annularSmallDerivativeFailureConstant C 0 2 *
        (2 * Real.log N) ^ 4 * (N : ℝ) ^ (13 / 1000 : ℝ) := by
      gcongr
      · exact logarithmicAnnularWidth_add_one_le hlog
      · exact exp_mul_logarithmicAnnularWidth_le hN (by norm_num)
    _ = _ := by ring

/-- The covariance nondegeneracy threshold has a vanishing ratio at the growing width. -/
theorem logarithmicAnnularWidth_covariance_ratio_le {N : ℕ} (hN : 1 ≤ N) :
    (6400 * Real.exp (8 * logarithmicAnnularWidth N)) ^ 2 / (N : ℝ) ≤
      6400 ^ 2 * (N : ℝ) ^ (-123 / 125 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ = 6400 ^ 2 * Real.exp (16 * logarithmicAnnularWidth N) / (N : ℝ) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      congr 1
      norm_num
      ring
    _ ≤ 6400 ^ 2 * (N : ℝ) ^ (16 / 1000 : ℝ) / (N : ℝ) := by
      gcongr
      exact exp_mul_logarithmicAnnularWidth_le hN (by norm_num)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hn.ne']
      congr 2
      norm_num

/-- Direct substitution into the complete mesh-variance term gives the degree
power `-181/500`, with a fixed coefficient and eight logarithmic powers. -/
theorem logarithmicAnnularWidth_badRootFailure_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {C : ℝ} (hC : 0 < C) :
    annularSmallDerivativeFailureConstant C (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2) *
      (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 ≤
      16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (-181 / 500 : ℝ) * (Real.log N) ^ 8 := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' zero_lt_one
  calc
    _ ≤ (16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (13 / 1000 : ℝ) * (Real.log N) ^ 4) *
          (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
      gcongr
      exact logarithmicAnnularWidth_badRootConstant_le hlog hC
    _ = 16 * annularSmallDerivativeFailureConstant C 0 2 *
        ((N : ℝ) ^ (13 / 1000 : ℝ) * (N : ℝ) ^ (-3 / 8 : ℝ)) * (Real.log N) ^ 8 := by ring
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

/-- The displayed growing-width mesh-variance envelope is summable along
rounded real-power degrees above `500/181`. -/
theorem summable_logarithmicAnnularWidth_badRootFailure {q C : ℝ}
    (hq : 500 / 181 < q) (hC : 0 < C) :
    Summable (fun j : ℕ => annularSmallDerivativeFailureConstant C
      (logarithmicAnnularWidth (realPowerDegree q j)) (logarithmicAnnularWidth (realPowerDegree q j) + 2) *
        (realPowerDegree q j : ℝ) ^ (-3 / 8 : ℝ) * (Real.log (realPowerDegree q j)) ^ 4) := by
  have hq0 : 0 < q := by linarith
  have hsum := (summable_realPowerDegree_rpow_mul_log_pow hq0
    (show q * (-181 / 500 : ℝ) < -1 by linarith) 8).mul_left
      (16 * annularSmallDerivativeFailureConstant C 0 2)
  apply hsum.of_norm_bounded_eventually_nat
  have hlog := (Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_realPowerDegree hq0))).eventually_ge_atTop 1
  filter_upwards [hlog] with j hj
  have hnonneg : 0 ≤ annularSmallDerivativeFailureConstant C
      (logarithmicAnnularWidth (realPowerDegree q j)) (logarithmicAnnularWidth (realPowerDegree q j) + 2) := by
    have hv := annularJetPairConstant_pos C (logarithmicAnnularWidth (realPowerDegree q j)) hC
    unfold annularSmallDerivativeFailureConstant
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [mul_assoc] using logarithmicAnnularWidth_badRootFailure_le hj hC

end Erdos522
