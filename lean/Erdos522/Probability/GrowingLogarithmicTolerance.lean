/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.LogarithmicAnnularScales

/-!
# Vanishing logarithmic error at growing annular width

The occupation coefficient grows as `exp(9K)`. The finite clipping threshold
at height `(1/32) log N` keeps this coefficient on the powers `N^(-1/2)` and
`N^(-1/4)` only, so the logarithmic error vanishes even after multiplication
by `log N` at logarithmic width.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The logarithmic tolerance at growing width. The occupation constant `H`
multiplies only the negative powers `N^(-1/2)` and `N^(-1/4)`. -/
def growingLogarithmicTolerance (A H : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-(1 / 32 : ℝ)) + Real.log N / 16 * H * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
    powerLogarithmicMomentCutoff A N *
      (Real.sqrt 2 * (N : ℝ) ^ (-(1 / 32 : ℝ)) + Real.sqrt H * (N : ℝ) ^ (-(1 / 4 : ℝ))) +
    (3 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 16 : ℝ))

/-- The finite clipping threshold at height `(1/32) log N` lies below the
growing-width tolerance. -/
theorem growing_logarithmic_threshold_le {N : ℕ} (hN : 1 ≤ N) (A : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (N : ℝ) ^ (-(1 / 32 : ℝ)) + 2 * ((1 / 32 : ℝ) * Real.log N) * (H / Real.sqrt N) +
      powerLogarithmicMomentCutoff A N * Real.sqrt
        (Real.exp (-2 * ((1 / 32 : ℝ) * Real.log N)) + H / Real.sqrt N +
          (N : ℝ) ^ (-2 * (1 / 32 : ℝ))) +
      (3 / 2 : ℝ) * Real.exp (-2 * ((1 / 32 : ℝ) * Real.log N)) ≤
    growingLogarithmicTolerance A H N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp : Real.exp (-2 * ((1 / 32 : ℝ) * Real.log N)) = (N : ℝ) ^ (-(1 / 16 : ℝ)) := by
    rw [power_logarithmic_clipping_exp hn]
    norm_num
  have hb : (N : ℝ) ^ (-2 * (1 / 32 : ℝ)) = (N : ℝ) ^ (-(1 / 16 : ℝ)) := by norm_num
  have hd : H / Real.sqrt N = H * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn.le, div_eq_mul_inv]
  have hsqrt₁ : Real.sqrt (2 * (N : ℝ) ^ (-(1 / 16 : ℝ))) =
      Real.sqrt 2 * (N : ℝ) ^ (-(1 / 32 : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((N : ℝ) ^ _), ← Real.rpow_mul hn.le]
    norm_num
  have hsqrt₂ : Real.sqrt (H * (N : ℝ) ^ (-(1 / 2 : ℝ))) =
      Real.sqrt H * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_mul hH, Real.sqrt_eq_rpow ((N : ℝ) ^ _), ← Real.rpow_mul hn.le]
    norm_num
  have hsplit : Real.sqrt (2 * (N : ℝ) ^ (-(1 / 16 : ℝ)) + H * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      Real.sqrt (2 * (N : ℝ) ^ (-(1 / 16 : ℝ))) + Real.sqrt (H * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hx : 0 ≤ 2 * (N : ℝ) ^ (-(1 / 16 : ℝ)) := by positivity
    have hy : 0 ≤ H * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg (2 * (N : ℝ) ^ (-(1 / 16 : ℝ))),
      Real.sqrt_nonneg (H * (N : ℝ) ^ (-(1 / 2 : ℝ)))]
  have hD : 0 ≤ powerLogarithmicMomentCutoff A N := by
    unfold powerLogarithmicMomentCutoff
    positivity
  rw [hexp, hb, hd, show (N : ℝ) ^ (-(1 / 16 : ℝ)) + H * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
    (N : ℝ) ^ (-(1 / 16 : ℝ)) = 2 * (N : ℝ) ^ (-(1 / 16 : ℝ)) + H * (N : ℝ) ^ (-(1 / 2 : ℝ)) by ring]
  have hmoment := mul_le_mul_of_nonneg_left (hsplit.trans_eq (by rw [hsqrt₁, hsqrt₂])) hD
  unfold growingLogarithmicTolerance
  nlinarith only [hmoment]

/-- Explicit bound for the logarithmically rescaled tolerance at growing width. -/
theorem log_mul_growingLogarithmicTolerance_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {B : ℝ} (hB : 0 < B) (A : ℝ) :
    Real.log N * growingLogarithmicTolerance A
      (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N ≤
    (Real.log N) ^ 1 / (N : ℝ) ^ (1 / 32 : ℝ) +
      rademacherOccupationConstant B 0 / 16 *
        (Real.exp (9 * logarithmicAnnularWidth N) * (Real.log N) ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ)) +
      Real.exp 1 * (12 * A) ^ 6 * Real.sqrt 2 * ((Real.log N) ^ 7 / (N : ℝ) ^ (1 / 32 : ℝ)) +
      Real.exp 1 * (12 * A) ^ 6 * Real.sqrt (rademacherOccupationConstant B 0) *
        (Real.exp (9 / 2 * logarithmicAnnularWidth N) * (Real.log N) ^ 7 /
          (N : ℝ) ^ (1 / 4 : ℝ)) +
      3 / 2 * ((Real.log N) ^ 1 / (N : ℝ) ^ (1 / 16 : ℝ)) := by
  let K := logarithmicAnnularWidth N
  let H₀ := rademacherOccupationConstant B 0
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hl : 0 ≤ Real.log N := by linarith
  have hH₀ : 0 < H₀ := rademacherOccupationConstant_pos B 0
  have hH : 0 ≤ rademacherOccupationConstant B K := (rademacherOccupationConstant_pos B K).le
  have hocc : rademacherOccupationConstant B K ≤ H₀ * Real.exp (9 * K) :=
    rademacherOccupationConstant_le_exp hB (logarithmicAnnularWidth_nonneg N)
  have hsqrt : Real.sqrt (rademacherOccupationConstant B K) ≤
      Real.sqrt H₀ * Real.exp (9 / 2 * K) := by
    calc
      _ ≤ Real.sqrt (H₀ * Real.exp (9 * K)) := Real.sqrt_le_sqrt hocc
      _ = _ := by
        rw [Real.sqrt_mul hH₀.le, ← Real.exp_half]
        congr 2
        ring
  have hp (b : ℝ) : (N : ℝ) ^ (-b) = 1 / (N : ℝ) ^ b := by
    rw [Real.rpow_neg hn.le, one_div]
  unfold growingLogarithmicTolerance powerLogarithmicMomentCutoff
  rw [hp, hp, hp, hp]
  have h₁ : Real.log N * (Real.log N / 16 * rademacherOccupationConstant B K * (1 / (N : ℝ) ^ (1 / 2 : ℝ))) ≤
      Real.log N * (Real.log N / 16 * (H₀ * Real.exp (9 * K)) * (1 / (N : ℝ) ^ (1 / 2 : ℝ))) := by
    gcongr
  have h₂ : Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
      (Real.sqrt (rademacherOccupationConstant B K) * (1 / (N : ℝ) ^ (1 / 4 : ℝ)))) ≤
      Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
        (Real.sqrt H₀ * Real.exp (9 / 2 * K) * (1 / (N : ℝ) ^ (1 / 4 : ℝ)))) := by
    gcongr
  calc
    _ = Real.log N * (1 / (N : ℝ) ^ (1 / 32 : ℝ)) +
        Real.log N * (Real.log N / 16 * rademacherOccupationConstant B K *
          (1 / (N : ℝ) ^ (1 / 2 : ℝ))) +
        Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
          (Real.sqrt 2 * (1 / (N : ℝ) ^ (1 / 32 : ℝ)))) +
        Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
          (Real.sqrt (rademacherOccupationConstant B K) * (1 / (N : ℝ) ^ (1 / 4 : ℝ)))) +
        Real.log N * (3 / 2 * (1 / (N : ℝ) ^ (1 / 16 : ℝ))) := by ring
    _ ≤ Real.log N * (1 / (N : ℝ) ^ (1 / 32 : ℝ)) +
        Real.log N * (Real.log N / 16 * (H₀ * Real.exp (9 * K)) * (1 / (N : ℝ) ^ (1 / 2 : ℝ))) +
        Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
          (Real.sqrt 2 * (1 / (N : ℝ) ^ (1 / 32 : ℝ)))) +
        Real.log N * (Real.exp 1 * (12 * A * Real.log N) ^ 6 *
          (Real.sqrt H₀ * Real.exp (9 / 2 * K) * (1 / (N : ℝ) ^ (1 / 4 : ℝ)))) +
        Real.log N * (3 / 2 * (1 / (N : ℝ) ^ (1 / 16 : ℝ))) := by linarith
    _ = _ := by dsimp only [K, H₀]; ring

/-- The growing-width tolerance vanishes after multiplication by `log N`. -/
theorem tendsto_log_mul_growingLogarithmicTolerance {B : ℝ} (hB : 0 < B) (A : ℝ) :
    Tendsto (fun N : ℕ => Real.log N * growingLogarithmicTolerance A
      (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N) atTop (𝓝 0) := by
  have h₁ := tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 32)
  have h₂ := (tendsto_logarithmicAnnularWidth_factor (a := 9) (b := 1 / 2)
    (by norm_num) (by norm_num) 0 2).const_mul (rademacherOccupationConstant B 0 / 16)
  have h₃ := (tendsto_log_pow_div_nat_rpow 7 (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
    (Real.exp 1 * (12 * A) ^ 6 * Real.sqrt 2)
  have h₄ := (tendsto_logarithmicAnnularWidth_factor (a := 9 / 2) (b := 1 / 4)
    (by norm_num) (by norm_num) 0 7).const_mul
      (Real.exp 1 * (12 * A) ^ 6 * Real.sqrt (rademacherOccupationConstant B 0))
  have h₅ := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 16)).const_mul (3 / 2 : ℝ)
  have ht := (((h₁.add h₂).add h₃).add h₄).add h₅
  simp only [pow_zero, one_mul, mul_zero, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    have hl : 0 ≤ Real.log N := (show 1 ≤ Real.log N from hN).trans' zero_le_one
    have hp := rademacherOccupationConstant_pos B (logarithmicAnnularWidth N)
    unfold growingLogarithmicTolerance powerLogarithmicMomentCutoff
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with N hN
    exact log_mul_growingLogarithmicTolerance_le hN hB A

end Erdos522
