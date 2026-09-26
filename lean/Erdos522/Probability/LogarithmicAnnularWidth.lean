/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularConstantGrowth
import Erdos522.Probability.LogarithmicPowerConcentration

/-!
# Constants at a logarithmically growing annular width

At width `⌊log N / 128 - log log N⌋`, exponential width factors become small
powers of the degree, and the correction `log log N` gains a negative power of
`log N` in each of them. The bounds below substitute this width directly into
the finite occupation and derivative-count constants.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The annular width used for the logarithmic rate. -/
def logarithmicAnnularWidth (N : ℕ) : ℝ :=
  (⌊Real.log N / 128 - Real.log (Real.log N)⌋₊ : ℕ)

theorem logarithmicAnnularWidth_nonneg (N : ℕ) : 0 ≤ logarithmicAnnularWidth N :=
  Nat.cast_nonneg _

theorem logarithmicAnnularWidth_le {N : ℕ} (hlog : 1 ≤ Real.log N) :
    logarithmicAnnularWidth N ≤ Real.log N / 128 := by
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlog
  calc
    _ ≤ ((⌊Real.log N / 128⌋₊ : ℕ) : ℝ) := by
      unfold logarithmicAnnularWidth
      exact_mod_cast Nat.floor_le_floor (by linarith)
    _ ≤ _ := Nat.floor_le (by positivity)

/-- The width exceeds its defining real number minus one. -/
theorem sub_one_lt_logarithmicAnnularWidth (N : ℕ) :
    Real.log N / 128 - Real.log (Real.log N) - 1 < logarithmicAnnularWidth N := by
  have h := Nat.lt_floor_add_one (Real.log N / 128 - Real.log (Real.log N))
  unfold logarithmicAnnularWidth
  linarith

/-- Once `log log N ≤ log N / 128`, the width retains the correction `log log N`. -/
theorem logarithmicAnnularWidth_le_sub {N : ℕ}
    (hll : Real.log (Real.log N) ≤ Real.log N / 128) :
    logarithmicAnnularWidth N ≤ Real.log N / 128 - Real.log (Real.log N) :=
  Nat.floor_le (sub_nonneg.mpr hll)

/-- The correction `log log N` is eventually at most `log N / 128`. -/
theorem eventually_log_log_le_log_div :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N ∧ Real.log (Real.log N) ≤ Real.log N / 128 := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1,
    hratio.eventually_le_const (show (0 : ℝ) < 1 / 128 by norm_num)] with N hN hr
  change 1 ≤ Real.log N at hN
  refine ⟨hN, ?_⟩
  have hp : 0 < Real.log N := by linarith
  have hr' : Real.log (Real.log N) / Real.log N ≤ 1 / 128 := hr
  rw [div_le_iff₀ hp] at hr'
  linarith

theorem exp_mul_logarithmicAnnularWidth_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a * logarithmicAnnularWidth N) ≤ (N : ℝ) ^ (a / 128) := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' one_pos
  calc
    _ ≤ Real.exp (a * (Real.log N / 128)) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (logarithmicAnnularWidth_le hlog) ha)
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

/-- The correction `log log N` in the width gains the factor `(log N)^(-a)`. -/
theorem exp_mul_logarithmicAnnularWidth_le_log {N : ℕ} (hlog : 1 ≤ Real.log N)
    (hll : Real.log (Real.log N) ≤ Real.log N / 128) {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a * logarithmicAnnularWidth N) ≤
      (N : ℝ) ^ (a / 128) * Real.log N ^ (-a) := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' one_pos
  have hl : 0 < Real.log N := by linarith
  calc
    _ ≤ Real.exp (a * (Real.log N / 128 - Real.log (Real.log N))) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (logarithmicAnnularWidth_le_sub hll) ha)
    _ = _ := by
      rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hl, ← Real.exp_add]
      congr 1
      ring

theorem logarithmicAnnularWidth_add_one_le {N : ℕ} (hlog : 1 ≤ Real.log N) :
    logarithmicAnnularWidth N + 1 ≤ 2 * Real.log N := by
  linarith [logarithmicAnnularWidth_le hlog]

/-- The occupation constant at the growing width is controlled by a single
fixed constant and a degree power. -/
theorem logarithmicAnnularWidth_occupationConstant_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {C : ℝ} (hC : 0 < C) :
    rademacherOccupationConstant C (logarithmicAnnularWidth N) ≤
      rademacherOccupationConstant C 0 * (N : ℝ) ^ (9 / 128 : ℝ) := by
  exact (rademacherOccupationConstant_le_exp hC (logarithmicAnnularWidth_nonneg N)).trans
    (mul_le_mul_of_nonneg_left (exp_mul_logarithmicAnnularWidth_le hlog (by norm_num))
      (rademacherOccupationConstant_pos C 0).le)

/-- The bad-root constant keeps a fourth logarithmic power and exponent `13/128`. -/
theorem logarithmicAnnularWidth_badRootConstant_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {C : ℝ} (hC : 0 < C) :
    annularSmallDerivativeFailureConstant C (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2) ≤
      16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (13 / 128 : ℝ) * (Real.log N) ^ 4 := by
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
        (2 * Real.log N) ^ 4 * (N : ℝ) ^ (13 / 128 : ℝ) := by
      gcongr
      · exact logarithmicAnnularWidth_add_one_le hlog
      · exact exp_mul_logarithmicAnnularWidth_le hlog (by norm_num)
    _ = _ := by ring

/-- The covariance nondegeneracy threshold has a vanishing ratio at the growing width. -/
theorem logarithmicAnnularWidth_covariance_ratio_le {N : ℕ} (hlog : 1 ≤ Real.log N) :
    (6400 * Real.exp (8 * logarithmicAnnularWidth N)) ^ 2 / (N : ℝ) ≤
      6400 ^ 2 * (N : ℝ) ^ (-7 / 8 : ℝ) := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' one_pos
  calc
    _ = 6400 ^ 2 * Real.exp (16 * logarithmicAnnularWidth N) / (N : ℝ) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      congr 1
      norm_num
      ring
    _ ≤ 6400 ^ 2 * (N : ℝ) ^ (16 / 128 : ℝ) / (N : ℝ) := by
      gcongr
      exact exp_mul_logarithmicAnnularWidth_le hlog (by norm_num)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hn.ne']
      congr 2
      norm_num

/-- Direct substitution into the complete mesh-variance term at the count
threshold `N / (log N)^2` gives the degree power `-43/128`, with a fixed
coefficient and twelve logarithmic powers. -/
theorem logarithmicAnnularWidth_badRootFailure_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {C : ℝ} (hC : 0 < C) :
    annularSmallDerivativeFailureConstant C (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2) *
      (N : ℝ) ^ (-7 / 16 : ℝ) * (Real.log N) ^ 8 ≤
      16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (-43 / 128 : ℝ) * (Real.log N) ^ 12 := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' one_pos
  calc
    _ ≤ (16 * annularSmallDerivativeFailureConstant C 0 2 *
        (N : ℝ) ^ (13 / 128 : ℝ) * (Real.log N) ^ 4) *
          (N : ℝ) ^ (-7 / 16 : ℝ) * (Real.log N) ^ 8 := by
      gcongr
      exact logarithmicAnnularWidth_badRootConstant_le hlog hC
    _ = 16 * annularSmallDerivativeFailureConstant C 0 2 *
        ((N : ℝ) ^ (13 / 128 : ℝ) * (N : ℝ) ^ (-7 / 16 : ℝ)) * (Real.log N) ^ 12 := by ring
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

/-- The displayed growing-width mesh-variance envelope is summable along
rounded real-power degrees above `128/43`. -/
theorem summable_logarithmicAnnularWidth_badRootFailure {q C : ℝ}
    (hq : 128 / 43 < q) (hC : 0 < C) :
    Summable (fun j : ℕ => annularSmallDerivativeFailureConstant C
      (logarithmicAnnularWidth (realPowerDegree q j)) (logarithmicAnnularWidth (realPowerDegree q j) + 2) *
        (realPowerDegree q j : ℝ) ^ (-7 / 16 : ℝ) * (Real.log (realPowerDegree q j)) ^ 8) := by
  have hq0 : 0 < q := by linarith
  have hsum := (summable_realPowerDegree_rpow_mul_log_pow hq0
    (show q * (-43 / 128 : ℝ) < -1 by linarith) 12).mul_left
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
