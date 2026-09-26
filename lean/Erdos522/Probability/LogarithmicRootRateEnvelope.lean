/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GrowingAnnularMass
import Erdos522.Probability.ThinAnnularRadialBound
import Erdos522.Limits.LogarithmicBlockInterpolation

/-!
# The logarithmic root-count error envelope

The annular tail `1 / (K - 1)` supplies the leading term. Shrinking-window
errors, the logarithmic tolerance, small-derivative roots, and degree
increments vanish after logarithmic rescaling, leaving the constant `128`.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The growing annular mass envelope, with the exact finite variance error. -/
def growingAnnularMassEnvelope (B : ℝ) (N : ℕ) : ℝ :=
  let K := logarithmicAnnularWidth N
  1 / (K - 1) + 4 *
    (growingLogarithmicTolerance (fourierLogarithmicConstant harmonicRestrictionConstant)
      (rademacherOccupationConstant B K) N + kacVarianceApproximationError N K)

/-- The finite variance-profile error vanishes at logarithmic width, even
after multiplication by `log N`. -/
theorem tendsto_log_mul_growing_kacVarianceApproximationError :
    Tendsto (fun N : ℕ => Real.log N *
      kacVarianceApproximationError N (logarithmicAnnularWidth N)) atTop (𝓝 0) := by
  have h₁ := tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 1)
    (by norm_num) (by norm_num) 2 1
  have h₂ := (tendsto_logarithmicAnnularWidth_factor (a := 2) (b := 1)
    (by norm_num) (by norm_num) 0 1).div_const 2
  have ht := h₁.add h₂
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul, mul_one, Real.rpow_one, pow_one, zero_div,
    add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl := Real.log_natCast_nonneg N
    unfold kacVarianceApproximationError
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl := Real.log_natCast_nonneg N
    unfold kacVarianceApproximationError
    calc
      _ ≤ Real.log N * (((logarithmicAnnularWidth N + 1) ^ 2 +
          Real.exp (2 * logarithmicAnnularWidth N) / 2) / N) := by
        apply mul_le_mul_of_nonneg_left _ hl
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        nlinarith
      _ = _ := by ring

/-- The annular tail envelope has the exact logarithmic limit. -/
theorem tendsto_log_mul_growingAnnularMassEnvelope {B : ℝ} (hB : 0 < B) :
    Tendsto (fun N : ℕ => Real.log N * growingAnnularMassEnvelope B N)
      atTop (𝓝 128) := by
  have htol := tendsto_log_mul_growingLogarithmicTolerance hB
    (fourierLogarithmicConstant harmonicRestrictionConstant)
  have ht := tendsto_log_div_logarithmicAnnularWidth_sub_one.add
    ((htol.add tendsto_log_mul_growing_kacVarianceApproximationError).const_mul 4)
  simp only [add_zero, mul_zero] at ht
  apply ht.congr
  intro N
  unfold growingAnnularMassEnvelope
  ring

/-- A uniform normalized error envelope on an eighth-power degree block. -/
def logarithmicRootRateEnvelope (H B : ℝ) (j : ℕ) : ℝ :=
  let N := realPowerDegree 8 j
  3 * thinRadialError H N + growingAnnularMassEnvelope B N +
    1 / (Real.log N) ^ 2 + (3 / 2 : ℝ) * realPowerBlockLength 8 j / N

/-- Every lower-order matching error disappears under logarithmic rescaling. -/
theorem tendsto_log_mul_logarithmicRootRateEnvelope (H : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (fun j : ℕ => Real.log (realPowerDegree 8 j) * logarithmicRootRateEnvelope H B j)
      atTop (𝓝 128) := by
  have ht := tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)
  have hlog := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht)
  have h₁ := ((tendsto_log_mul_thinRadialError H).comp ht).const_mul 3
  have h₂ := (tendsto_log_mul_growingAnnularMassEnvelope hB).comp ht
  have h₃ : Tendsto (fun j : ℕ => Real.log (realPowerDegree 8 j) *
      (1 / (Real.log (realPowerDegree 8 j)) ^ 2)) atTop (𝓝 0) := by
    apply (tendsto_inv_atTop_zero.comp hlog).congr'
    filter_upwards [hlog.eventually_ge_atTop 1] with j hj
    have hl : Real.log (realPowerDegree 8 j) ≠ 0 := by
      have : (1 : ℝ) ≤ Real.log (realPowerDegree 8 j) := hj
      positivity
    simp only [Function.comp_apply]
    field_simp
  have h₄ := (tendsto_log_mul_realPowerBlockLength_div (q := 8) (by norm_num)).const_mul (3 / 2 : ℝ)
  have h := ((h₁.add h₂).add h₃).add h₄
  simp only [mul_zero, zero_add, add_zero] at h
  apply h.congr
  intro j
  unfold logarithmicRootRateEnvelope
  dsimp only [Function.comp_def]
  ring

end Erdos522
