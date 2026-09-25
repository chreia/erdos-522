/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.LogarithmicAnnularScales

/-!
# Vanishing logarithmic error at growing annular width

The occupation coefficient grows as `exp(9K)`. At logarithmic width this
still leaves a positive degree-power margin after the thin-band rescaling.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- A fixed coefficient controlling the logarithmic tolerance at every width. -/
def growingLogarithmicToleranceConstant (A H : ℝ) : ℝ :=
  5 / 2 + H / 16 + Real.exp 1 * (12 * A) ^ 6 * (2 + H)

/-- The finite logarithmic error retains its width dependence explicitly. -/
theorem logarithmicPowerTolerance_width_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {B : ℝ} (hB : 0 < B) (A : ℝ) :
    logarithmicPowerTolerance (1 / 32) A (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N ≤
      growingLogarithmicToleranceConstant A (rademacherOccupationConstant B 0) *
        Real.exp (9 * logarithmicAnnularWidth N) * (Real.log N) ^ 6 / (N : ℝ) ^ (1 / 32 : ℝ) := by
  let H := rademacherOccupationConstant B 0
  let K := logarithmicAnnularWidth N
  have hH : 0 < H := rademacherOccupationConstant_pos B 0
  have hK : 0 ≤ K := logarithmicAnnularWidth_nonneg N
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have he : 1 ≤ Real.exp (9 * K) := Real.one_le_exp_iff.mpr (by positivity)
  have hocc := rademacherOccupationConstant_le_exp hB hK
  have hsqrt : Real.sqrt (2 + rademacherOccupationConstant B K) ≤ (2 + H) * Real.exp (9 * K) := by
    have hp := rademacherOccupationConstant_pos B K
    calc
      _ ≤ 2 + rademacherOccupationConstant B K := (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
      _ ≤ _ := by dsimp [H] at *; nlinarith
  have hl₁ : Real.log N ≤ (Real.log N) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 6 by norm_num)
  have hl₀ : 1 ≤ (Real.log N) ^ 6 := one_le_pow₀ hlog
  have hconst : 5 / 2 ≤ (5 / 2 : ℝ) * Real.exp (9 * K) * (Real.log N) ^ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hl₀ (show 0 ≤ Real.exp (9 * K) by positivity)]
  have hlinear : 2 * (1 / 32 : ℝ) * rademacherOccupationConstant B K * Real.log N ≤
      H / 16 * Real.exp (9 * K) * (Real.log N) ^ 6 := by
    calc
      _ ≤ 2 * (1 / 32 : ℝ) * (H * Real.exp (9 * K)) * (Real.log N) ^ 6 := by gcongr
      _ = _ := by ring
  have hmoment : powerLogarithmicMomentCutoff A N * Real.sqrt (2 + rademacherOccupationConstant B K) ≤
      Real.exp 1 * (12 * A) ^ 6 * (2 + H) * Real.exp (9 * K) * (Real.log N) ^ 6 := by
    unfold powerLogarithmicMomentCutoff
    calc
      _ ≤ Real.exp 1 * (12 * A * Real.log N) ^ 6 * ((2 + H) * Real.exp (9 * K)) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  unfold logarithmicPowerTolerance growingLogarithmicToleranceConstant
  rw [Real.rpow_neg hn.le]
  calc
    _ ≤ ((N : ℝ) ^ (1 / 32 : ℝ))⁻¹ *
        ((5 / 2 : ℝ) * Real.exp (9 * K) * (Real.log N) ^ 6 +
          H / 16 * Real.exp (9 * K) * (Real.log N) ^ 6 +
          Real.exp 1 * (12 * A) ^ 6 * (2 + H) * Real.exp (9 * K) * (Real.log N) ^ 6) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hconst hlinear) hmoment) (by positivity)
    _ = _ := by dsimp [H, K]; ring

/-- Even after multiplication by `N^κ` and any fixed logarithmic power, the
growing-annulus tolerance vanishes whenever `κ < 89/4000`. -/
theorem tendsto_scaled_growingLogarithmicTolerance {B κ : ℝ} (hB : 0 < B)
    (hκ : κ < 89 / 4000) (A : ℝ) (m : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ κ * (Real.log N) ^ m *
      logarithmicPowerTolerance (1 / 32) A (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N)
      atTop (𝓝 0) := by
  let C := growingLogarithmicToleranceConstant A (rademacherOccupationConstant B 0)
  have h := (tendsto_logarithmicAnnularWidth_factor (a := 9) (b := 1 / 32 - κ)
    (by norm_num) (by linarith) 0 (m + 6)).const_mul C
  simp only [pow_zero, one_mul, mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    have hl : 0 ≤ Real.log N := (show 1 ≤ Real.log N from hN).trans' zero_le_one
    have hp := rademacherOccupationConstant_pos B (logarithmicAnnularWidth N)
    unfold logarithmicPowerTolerance powerLogarithmicMomentCutoff
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    have hl : 1 ≤ Real.log N := hN
    have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
    have hn : (0 : ℝ) < N := by linarith
    calc
      _ ≤ (N : ℝ) ^ κ * (Real.log N) ^ m *
          (C * Real.exp (9 * logarithmicAnnularWidth N) * (Real.log N) ^ 6 / (N : ℝ) ^ (1 / 32 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (logarithmicPowerTolerance_width_le hl hB A)
        positivity
      _ = C * (Real.exp (9 * logarithmicAnnularWidth N) * (Real.log N) ^ (m + 6) /
          (N : ℝ) ^ (1 / 32 - κ)) := by
        rw [pow_add, Real.rpow_sub hn]
        ring_nf
        simp only [inv_inv]
        ring

end Erdos522
