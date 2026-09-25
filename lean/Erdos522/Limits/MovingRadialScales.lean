/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.RootLocalizationScales
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Moving radial scales across degree blocks

The target radius `1 + x/n` moves by at most `9 |x| N^(-9/8)` in an
eighth-power degree block beginning at `N`. Relative to the matching window,
this has the decaying margin `9 |x| N^(-7/64)`. The maximal drift and the
root localization radius therefore fit inside the same reference window.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The largest change of the scaled radial target in a finite degree block. -/
def maximalRadialShift (N M : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (M + 1)).sup' (Finset.nonempty_range_iff.mpr (by omega))
    (fun m => |(1 + x / (N + m : ℕ)) - (1 + x / N)|)

/-- Every prefix's radial shift is at most the maximum over the block. -/
theorem radial_shift_le_maximalRadialShift (N M m : ℕ) (x : ℝ) (hm : m ≤ M) :
    |(1 + x / (N + m : ℕ)) - (1 + x / N)| ≤ maximalRadialShift N M x := by
  unfold maximalRadialShift
  exact Finset.le_sup' (fun k : ℕ => |(1 + x / (N + k : ℕ)) - (1 + x / N)|)
    (show m ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))

theorem maximalRadialShift_nonneg (N M : ℕ) (x : ℝ) : 0 ≤ maximalRadialShift N M x := by
  exact (abs_nonneg _).trans (radial_shift_le_maximalRadialShift N M 0 x (Nat.zero_le _))

/-- The exact radial shift has denominator `N(N+m)`, including `m=0`. -/
theorem radial_shift_eq {N : ℕ} (hN : 0 < N) (m : ℕ) (x : ℝ) :
    |(1 + x / (N + m : ℕ)) - (1 + x / N)| =
      |x| * m / ((N : ℝ) * (N + m : ℕ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnm : (0 : ℝ) < (N + m : ℕ) := by exact_mod_cast (show 0 < N + m by omega)
  have heq : (1 + x / N) - (1 + x / (N + m : ℕ)) =
      x * m / ((N : ℝ) * (N + m : ℕ)) := by
    push_cast
    field_simp
    ring
  rw [abs_sub_comm, heq, abs_div, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m), abs_of_pos (mul_pos hn hnm)]

/-- Replacing `N(N+m)` by `N²` gives the uniform elementary drift bound. -/
theorem radial_shift_le_degree_square {N : ℕ} (hN : 0 < N) (m : ℕ) (x : ℝ) :
    |(1 + x / (N + m : ℕ)) - (1 + x / N)| ≤ |x| * m / (N : ℝ) ^ 2 := by
  rw [radial_shift_eq hN m x]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn)
  push_cast
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Every target radius in an eighth-power block moves by at most
`9 |x| N^(-9/8)`, starting at index sixty. -/
theorem eighth_power_radial_shift_le (j : ℕ) (hj : 60 ≤ j) (m : ℕ)
    (hm : m ≤ eighthPowerBlockLength j) (x : ℝ) :
    |(1 + x / (j ^ 8 + m : ℕ)) - (1 + x / (j ^ 8 : ℕ))| ≤
      9 * |x| * ((j ^ 8 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) := by
  have hN : 0 < j ^ 8 := pow_pos (by omega) _
  have hn : (0 : ℝ) < (j ^ 8 : ℕ) := by exact_mod_cast hN
  have hm' : (m : ℝ) ≤ 9 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) :=
    (by exact_mod_cast hm : (m : ℝ) ≤ eighthPowerBlockLength j).trans
      (eighthPowerBlockLength_le_rpow j hj)
  calc
    _ ≤ |x| * m / ((j ^ 8 : ℕ) : ℝ) ^ 2 := radial_shift_le_degree_square hN m x
    _ ≤ |x| * (9 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) /
        ((j ^ 8 : ℕ) : ℝ) ^ 2 := by gcongr
    _ = (9 * |x|) * (((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) /
        ((j ^ 8 : ℕ) : ℝ) ^ 2) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_sub hn]
      norm_num

/-- The maximal target drift obeys the same explicit bound. -/
theorem eighth_power_maximalRadialShift_le (j : ℕ) (hj : 60 ≤ j) (x : ℝ) :
    maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) x ≤
      9 * |x| * ((j ^ 8 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) := by
  apply Finset.sup'_le
  intro m hm
  exact eighth_power_radial_shift_le j hj m (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm) x

/-- The maximal drift divided by the matching window has an explicit power margin. -/
theorem eighth_power_radial_shift_ratio_le (j : ℕ) (hj : 60 ≤ j) (x : ℝ) :
    maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) x / radialMatchingWindow (j ^ 8) ≤
      9 * |x| * ((j ^ 8 : ℕ) : ℝ) ^ (-7 / 64 : ℝ) := by
  have hn : (0 : ℝ) < (j ^ 8 : ℕ) := by positivity
  calc
    _ ≤ (9 * |x| * ((j ^ 8 : ℕ) : ℝ) ^ (-9 / 8 : ℝ)) /
        radialMatchingWindow (j ^ 8) := by
      apply div_le_div_of_nonneg_right (eighth_power_maximalRadialShift_le j hj x)
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ = (9 * |x|) * (((j ^ 8 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) /
        ((j ^ 8 : ℕ) : ℝ) ^ (-1 - 1 / 64 : ℝ)) := by unfold radialMatchingWindow; ring
    _ = _ := by rw [← Real.rpow_sub hn]; norm_num

/-- For every fixed scaled radius, the maximal target drift is negligible
relative to the radial matching window. -/
theorem tendsto_maximalRadialShift_div_window (x : ℝ) :
    Tendsto (fun j : ℕ => maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) x /
      radialMatchingWindow (j ^ 8)) atTop (𝓝 0) := by
  have ht := (tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 7 / 64)).const_mul (9 * |x|)
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun j =>
    div_nonneg (maximalRadialShift_nonneg _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    ?_ (ht.comp hp)
  filter_upwards [eventually_ge_atTop 60] with j hj
  simpa only [Function.comp_apply, neg_div, radialMatchingWindow] using
    eighth_power_radial_shift_ratio_le j hj x

/-- The actual root localization radius is negligible relative to the
matching window along eighth-power blocks. -/
theorem tendsto_eighth_power_root_displacement_ratio (K' : ℝ) :
    Tendsto (fun j : ℕ =>
      (2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K' /
        regularDerivativeThreshold (j ^ 8)) / radialMatchingWindow (j ^ 8)) atTop (𝓝 0) := by
  have ht := (tendsto_sqrt_log_div_nat_rpow (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
    (90 * Real.exp (2 * K'))
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun j => by
    unfold TailSupremum.tailAmplitude regularDerivativeThreshold radialMatchingWindow
    positivity) ?_ (ht.comp hp)
  filter_upwards [eventually_ge_atTop 60] with j hj
  have hN : 0 < j ^ 8 := pow_pos (by omega) _
  simpa only [Function.comp_apply, mul_div_assoc] using
    root_displacement_ratio_le hN (eighth_power_tailAmplitude_le j hj K')

/-- The sum of the maximal radial drift and the actual root localization
radius has vanishing ratio to the reference matching window. -/
theorem tendsto_eighth_power_total_radial_displacement_ratio (K' x : ℝ) :
    Tendsto (fun j : ℕ =>
      (2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K' /
        regularDerivativeThreshold (j ^ 8) +
          maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) x) /
        radialMatchingWindow (j ^ 8)) atTop (𝓝 0) := by
  have h := (tendsto_eighth_power_root_displacement_ratio K').add
    (tendsto_maximalRadialShift_div_window x)
  simpa only [add_zero, ← add_div] using h

/-- All localization conditions hold eventually with the maximal movement of
the target radius included, using the original tail amplitude and curvature envelope. -/
theorem eventually_eighth_power_moving_root_localization (K K' x : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let a := TailSupremum.tailAmplitude N (eighthPowerBlockLength j) K'
      let d := regularDerivativeThreshold N
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧
        2 * a / d + maximalRadialShift N (eighthPowerBlockLength j) x < radialMatchingWindow N := by
  have hratio := (tendsto_eighth_power_total_radial_displacement_ratio K' x).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_eighth_power_root_localization K K', hratio,
    eventually_ge_atTop 1] with j hlocal hsmall hj
  dsimp only at hlocal ⊢
  have hn : (0 : ℝ) < (j ^ 8 : ℕ) := by positivity
  have hw : 0 < radialMatchingWindow (j ^ 8) := Real.rpow_pos_of_pos hn _
  exact ⟨hlocal.1, hlocal.2.1, hlocal.2.2.1, hlocal.2.2.2.1, (div_lt_one hw).mp hsmall⟩

/-- The maximal localization inequality applies simultaneously to every
degree in the block and its own radial target. -/
theorem eventually_eighth_power_moving_radius_window (K' x : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
      2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K' /
          regularDerivativeThreshold (j ^ 8) +
        |(1 + x / (j ^ 8 + m : ℕ)) - (1 + x / (j ^ 8 : ℕ))| <
          radialMatchingWindow (j ^ 8) := by
  filter_upwards [eventually_eighth_power_moving_root_localization 0 K' x] with j hj
  intro m hm
  calc
    _ ≤ 2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K' /
        regularDerivativeThreshold (j ^ 8) +
          maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) x := by
      gcongr
      exact radial_shift_le_maximalRadialShift (j ^ 8) (eighthPowerBlockLength j) m x hm
    _ < _ := hj.2.2.2.2

end Erdos522
