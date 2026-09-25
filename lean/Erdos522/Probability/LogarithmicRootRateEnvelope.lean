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

The annular tail supplies the leading term. Shrinking-window errors,
small-derivative roots, and degree increments vanish after logarithmic
rescaling, leaving the constant `2000 log 2`.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The growing annular mass envelope, with the exact finite variance error. -/
def growingAnnularMassEnvelope (B : ℝ) (N : ℕ) : ℝ :=
  let K := logarithmicAnnularWidth N
  2 * Real.log 2 / K + 8 *
    (logarithmicPowerTolerance (1 / 32) (fourierLogarithmicConstant harmonicRestrictionConstant)
      (rademacherOccupationConstant B K) N + kacVarianceApproximationError N K) / K

/-- The finite variance-profile error still vanishes at logarithmic width. -/
theorem tendsto_growing_kacVarianceApproximationError :
    Tendsto (fun N : ℕ => kacVarianceApproximationError N (logarithmicAnnularWidth N))
      atTop (𝓝 0) := by
  have h₁ := tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 1)
    (by norm_num) (by norm_num) 2 0
  have h₂ := (tendsto_logarithmicAnnularWidth_factor (a := 2) (b := 1)
    (by norm_num) (by norm_num) 0 0).div_const 2
  have ht := h₁.add h₂
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul, mul_one, Real.rpow_one, zero_div, add_zero] at ht
  apply squeeze_zero (fun N => by
    have hK := logarithmicAnnularWidth_nonneg N
    unfold kacVarianceApproximationError
    positivity) _ ht
  intro N
  have hK := logarithmicAnnularWidth_nonneg N
  unfold kacVarianceApproximationError
  calc
    _ ≤ ((logarithmicAnnularWidth N + 1) ^ 2 + Real.exp (2 * logarithmicAnnularWidth N) / 2) / N := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      nlinarith
    _ = _ := by ring

/-- The annular tail envelope has the exact logarithmic limit. -/
theorem tendsto_log_mul_growingAnnularMassEnvelope {B : ℝ} (hB : 0 < B) :
    Tendsto (fun N : ℕ => Real.log N * growingAnnularMassEnvelope B N)
      atTop (𝓝 (2000 * Real.log 2)) := by
  have htol := tendsto_scaled_growingLogarithmicTolerance (κ := 0) hB
    (by norm_num) (fourierLogarithmicConstant harmonicRestrictionConstant) 0
  simp only [Real.rpow_zero, pow_zero, mul_one, one_mul] at htol
  have h₁ := tendsto_log_div_logarithmicAnnularWidth.const_mul (2 * Real.log 2)
  have h₂ := (tendsto_log_div_logarithmicAnnularWidth.mul
    (htol.add tendsto_growing_kacVarianceApproximationError)).const_mul 8
  have ht := h₁.add h₂
  simp only [add_zero, mul_zero] at ht
  convert ht using 1
  · ext N
    unfold growingAnnularMassEnvelope
    ring
  · congr 1
    ring

/-- A uniform normalized error envelope on an eighth-power degree block. -/
def logarithmicRootRateEnvelope (H B : ℝ) (j : ℕ) : ℝ :=
  let N := realPowerDegree 8 j
  3 * thinRadialError H N + growingAnnularMassEnvelope B N +
    (N : ℝ) ^ (-(1 / 32 : ℝ)) + (3 / 2 : ℝ) * realPowerBlockLength 8 j / N

/-- Every lower-order matching error disappears under logarithmic rescaling. -/
theorem tendsto_log_mul_logarithmicRootRateEnvelope (H : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (fun j : ℕ => Real.log (realPowerDegree 8 j) * logarithmicRootRateEnvelope H B j)
      atTop (𝓝 (2000 * Real.log 2)) := by
  have ht := tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)
  have h₁ := ((tendsto_log_mul_thinRadialError H).comp ht).const_mul 3
  have h₂ := (tendsto_log_mul_growingAnnularMassEnvelope hB).comp ht
  have h₃ : Tendsto (fun j : ℕ => Real.log (realPowerDegree 8 j) *
      (realPowerDegree 8 j : ℝ) ^ (-(1 / 32 : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 32)).comp ht
    simpa only [pow_one, Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv] using h
  have h₄ := (tendsto_log_mul_realPowerBlockLength_div (q := 8) (by norm_num)).const_mul (3 / 2 : ℝ)
  have h := ((h₁.add h₂).add h₃).add h₄
  simp only [mul_zero, zero_add, add_zero] at h
  apply h.congr
  intro j
  unfold logarithmicRootRateEnvelope
  dsimp only [Function.comp_def]
  ring

end Erdos522
