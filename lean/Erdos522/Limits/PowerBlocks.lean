/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lengths of polynomial degree blocks

The gap between consecutive eighth powers is bounded by nine times the
seven-eighths power of the lower degree, with an explicit starting index.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The length of a block between consecutive eighth powers. -/
def eighthPowerBlockLength (j : ℕ) : ℕ := (j + 1) ^ 8 - j ^ 8

/-- Consecutive eighth powers give nonempty degree blocks. -/
theorem eighthPowerBlockLength_pos (j : ℕ) : 0 < eighthPowerBlockLength j := by
  unfold eighthPowerBlockLength
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by norm_num))

/-- The block endpoint is exactly the next eighth power. -/
theorem eighthPowerBlockLength_endpoint (j : ℕ) :
    j ^ 8 + eighthPowerBlockLength j = (j + 1) ^ 8 := by
  unfold eighthPowerBlockLength
  exact Nat.add_sub_of_le (Nat.pow_le_pow_left (by omega) 8)

/-- From index sixty, each block contains at most `9 j^7` new degrees. -/
theorem eighthPowerBlockLength_le (j : ℕ) (hj : 60 ≤ j) :
    eighthPowerBlockLength j ≤ 9 * j ^ 7 := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj60 : (60 : ℝ) ≤ j := by exact_mod_cast hj
  have hb : (j : ℝ) + 1 ≤ (61 / 60 : ℝ) * j := by linarith
  have hp := abs_pow_sub_pow_le ((j : ℝ) + 1) (j : ℝ) 8
  have hpow : (j : ℝ) ^ 8 ≤ ((j : ℝ) + 1) ^ 8 := by gcongr; linarith
  simp only [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg hj0,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1),
    max_eq_left (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)] at hp
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hp
  have hdiff : ((j : ℝ) + 1) ^ 8 - (j : ℝ) ^ 8 ≤ 9 * (j : ℝ) ^ 7 := by
    calc
      _ ≤ 8 * ((j : ℝ) + 1) ^ 7 := by simpa using hp
      _ ≤ 8 * ((61 / 60 : ℝ) * j) ^ 7 := by gcongr
      _ = (8 * (61 / 60 : ℝ) ^ 7) * (j : ℝ) ^ 7 := by ring
      _ ≤ 9 * (j : ℝ) ^ 7 := by gcongr; norm_num
  have hcast : (eighthPowerBlockLength j : ℝ) =
      ((j : ℝ) + 1) ^ 8 - (j : ℝ) ^ 8 := by
    rw [eighthPowerBlockLength, Nat.cast_sub (Nat.pow_le_pow_left (by omega) 8)]
    push_cast
    rfl
  rw [← hcast] at hdiff
  exact_mod_cast hdiff

/-- The same length bound in terms of the lower degree. -/
theorem eighthPowerBlockLength_le_rpow (j : ℕ) (hj : 60 ≤ j) :
    (eighthPowerBlockLength j : ℝ) ≤ 9 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) := by
  have hpow : ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) = (j : ℝ) ^ 7 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg j)]
    norm_num
  rw [hpow]
  exact_mod_cast eighthPowerBlockLength_le j hj

/-- Each block is shorter than its lower degree from index sixty. -/
theorem eighthPowerBlockLength_le_degree (j : ℕ) (hj : 60 ≤ j) :
    eighthPowerBlockLength j ≤ j ^ 8 := by
  calc
    _ ≤ 9 * j ^ 7 := eighthPowerBlockLength_le j hj
    _ ≤ j * j ^ 7 := Nat.mul_le_mul_right _ (by omega)
    _ = j ^ 8 := by ring

/-- Eighth powers form a strictly increasing subsequence. -/
theorem strictMono_eighth_power : StrictMono (fun j : ℕ => j ^ 8) := by
  intro i j hij
  exact Nat.pow_lt_pow_left hij (by norm_num)

/-- The relative length of an eighth-power degree block tends to zero. -/
theorem tendsto_eighthPowerBlockLength_div :
    Tendsto (fun j : ℕ => (eighthPowerBlockLength j : ℝ) / ((j ^ 8 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have ht := tendsto_one_div_atTop_nhds_zero_nat.const_mul (9 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ ht
  filter_upwards [eventually_ge_atTop 60] with j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have h := eighthPowerBlockLength_le j hj
  have hr : (eighthPowerBlockLength j : ℝ) ≤ 9 * (j : ℝ) ^ 7 := by exact_mod_cast h
  calc
    _ ≤ (9 * (j : ℝ) ^ 7) / ((j ^ 8 : ℕ) : ℝ) := by gcongr
    _ = 9 * (1 / (j : ℝ)) := by push_cast; field_simp

/-- Consecutive eighth powers have ratio tending to one. -/
theorem tendsto_eighth_power_degree_ratio :
    Tendsto (fun j : ℕ => (((j + 1) ^ 8 : ℕ) : ℝ) / ((j ^ 8 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have ht := tendsto_eighthPowerBlockLength_div.const_add 1
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hN : (((j ^ 8 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [← eighthPowerBlockLength_endpoint, Nat.cast_add, add_div, div_self hN]

end Erdos522
