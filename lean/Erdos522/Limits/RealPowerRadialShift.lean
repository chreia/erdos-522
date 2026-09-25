/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.RealPowerBlocks
import Erdos522.Limits.MovingRadialScales

/-!
# Moving radial targets on real-power degree blocks

For fixed `x`, the radial target changes by order `N^(-1-1/q)` through a
block. Every window with exponent `κ < 1/q` absorbs this change.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

theorem real_power_radial_shift_ratio_le {q : ℝ} (hq : 1 < q) {j : ℕ} (hj : 2 ≤ j)
    (x κ : ℝ) (m : ℕ) (hm : m ≤ realPowerBlockLength q j) :
    |(1 + x / (realPowerDegree q j + m : ℕ)) - (1 + x / realPowerDegree q j)| /
        (realPowerDegree q j : ℝ) ^ (-1 - κ) ≤
      ((2 + q * 2 ^ q) * |x|) * (realPowerDegree q j : ℝ) ^ (-(1 / q - κ)) := by
  have hN : 0 < realPowerDegree q j :=
    (by omega : 0 < j).trans_le ((strictMono_realPowerDegree hq.le).id_le j)
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast hN
  have hM : (m : ℝ) ≤ (2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q) :=
    (by exact_mod_cast hm : (m : ℝ) ≤ realPowerBlockLength q j).trans
      (realPowerBlockLength_le_rpow hq hj)
  calc
    _ ≤ (|x| * m / (realPowerDegree q j : ℝ) ^ 2) /
        (realPowerDegree q j : ℝ) ^ (-1 - κ) :=
      div_le_div_of_nonneg_right (radial_shift_le_degree_square hN m x)
        (Real.rpow_nonneg hn.le _)
    _ ≤ (|x| * ((2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q)) /
        (realPowerDegree q j : ℝ) ^ 2) / (realPowerDegree q j : ℝ) ^ (-1 - κ) := by gcongr
    _ = ((2 + q * 2 ^ q) * |x|) *
        ((realPowerDegree q j : ℝ) ^ (1 - 1 / q) /
          ((realPowerDegree q j : ℝ) ^ 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ))) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_add hn, ← Real.rpow_sub hn]
      congr 2
      ring

/-- Every partial block has target drift at most the prescribed matching window
once the lower degree is sufficiently large. -/
theorem eventually_real_power_radial_shift_le {q κ : ℝ} (hq : 1 < q)
    (hκ : κ < 1 / q) (x : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ realPowerBlockLength q j →
      |(1 + x / (realPowerDegree q j + m : ℕ)) - (1 + x / realPowerDegree q j)| ≤
        (realPowerDegree q j : ℝ) ^ (-1 - κ) := by
  have hlim := ((tendsto_nat_rpow_neg (show 0 < 1 / q - κ by linarith)).const_mul
    ((2 + q * 2 ^ q) * |x|)).comp (tendsto_realPowerDegree (show 0 < q by linarith))
  simp only [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 2,
    hlim.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with j hj hsmall
  intro m hm
  have hN : 0 < realPowerDegree q j :=
    (by omega : 0 < j).trans_le ((strictMono_realPowerDegree hq.le).id_le j)
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast hN
  have hw := Real.rpow_pos_of_pos hn (-1 - κ)
  exact ((div_lt_one hw).mp ((real_power_radial_shift_ratio_le hq hj x κ m hm).trans_lt hsmall)).le

end Erdos522
