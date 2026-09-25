/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.LogarithmicAnnularScales
import Erdos522.Limits.RealPowerLocalization

/-!
# Root isolation at logarithmic annular width

On the eighth-power schedule, the displacement and curvature margins are
`1/32`. The exponential width factors have rates two and three, respectively,
so both remain negligible at the logarithmic width.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- Translation of the width separates the fixed tail prefactor. -/
theorem realPowerTailConstant_add_one (q K : ℝ) :
    realPowerTailConstant q (K + 1) = realPowerTailConstant q 1 * Real.exp (2 * K) := by
  unfold realPowerTailConstant
  rw [show 2 * (K + 1) = 2 + 2 * K by ring, Real.exp_add]
  simp only [mul_one]
  ring

/-- The Taylor and displacement hypotheses hold at the actual block-tail
amplitude throughout the logarithmically growing annulus. -/
theorem eventually_growing_annular_root_localization :
    ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree 8 j
      let K := logarithmicAnnularWidth N
      let a := TailSupremum.tailAmplitude N (realPowerBlockLength 8 j) (K + 1)
      let d := (N : ℝ) ^ (3 / 2 - (1 / 64 : ℝ))
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧ 2 * a / d < radialMatchingWindow N := by
  let A := realPowerTailConstant 8 1
  have hA : 0 < A := realPowerTailConstant_pos (by norm_num) 1
  have ht := tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)
  have hr := (tendsto_logarithmicAnnularWidth_factor (a := 2) (b := 1 / 32)
    (by norm_num) (by norm_num) 0 1).const_mul (2 * A)
  have hc := (tendsto_logarithmicAnnularWidth_factor (a := 3) (b := 1 / 32)
    (by norm_num) (by norm_num) 0 1).const_mul (4 * (100 * Real.exp 4) * A)
  simp only [pow_zero, pow_one, one_mul, mul_zero] at hr hc
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop 2, ht.eventually hlog,
    (hr.comp ht).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (hc.comp ht).eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with j hj hN hl hrj hcj
  dsimp only
  let N := realPowerDegree 8 j
  let K := logarithmicAnnularWidth N
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 1 ≤ Real.log N := hl
  have hM : (0 : ℝ) < realPowerBlockLength 8 j := by
    exact_mod_cast realPowerBlockLength_pos (by norm_num : (1 : ℝ) ≤ 8) j
  have ha : 0 < TailSupremum.tailAmplitude N (realPowerBlockLength 8 j) (K + 1) := by
    unfold TailSupremum.tailAmplitude
    positivity
  have hd : 0 < (N : ℝ) ^ (3 / 2 - (1 / 64 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hw : 0 < (N : ℝ) ^ (-1 - (1 / 64 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hab := real_power_tailAmplitude_le (by norm_num : (1 : ℝ) < 8) hj (K + 1)
  have hdispl := real_power_displacement_ratio_le (ℓ := 1 / 64) (κ := 1 / 64)
    (by omega : 0 < realPowerDegree 8 j) hab
  have hcurve := real_power_curvature_ratio_le (ℓ := 1 / 64) (K := K)
    (by omega : 0 < realPowerDegree 8 j) hab
  rw [show (1 / (2 * (8 : ℝ)) - 1 / 64 - 1 / 64) = 1 / 32 by norm_num] at hdispl
  rw [show (1 / (2 * (8 : ℝ)) - 2 * (1 / 64 : ℝ)) = 1 / 32 by norm_num] at hcurve
  have hrj' : 2 * realPowerTailConstant 8 (K + 1) * Real.sqrt (Real.log N) /
      (N : ℝ) ^ (1 / 32 : ℝ) < 1 := by
    calc
      _ ≤ (2 * A) * (Real.exp (2 * K) * Real.log N / (N : ℝ) ^ (1 / 32 : ℝ)) := by
        rw [realPowerTailConstant_add_one]
        have hsqrt : Real.sqrt (Real.log N) ≤ Real.log N :=
          Real.sqrt_le_self_iff.mpr (Or.inr hlogN)
        calc
          _ ≤ 2 * (A * Real.exp (2 * K)) * Real.log N / (N : ℝ) ^ (1 / 32 : ℝ) := by gcongr
          _ = _ := by ring
      _ < 1 := hrj
  have hcj' : 4 * (100 * Real.exp (K + 4)) * realPowerTailConstant 8 (K + 1) *
      Real.log N / (N : ℝ) ^ (1 / 32 : ℝ) < 1 := by
    calc
      _ = (4 * (100 * Real.exp 4) * A) *
          (Real.exp (3 * K) * Real.log N / (N : ℝ) ^ (1 / 32 : ℝ)) := by
        rw [realPowerTailConstant_add_one, Real.exp_add,
          show 3 * K = K + 2 * K by ring, Real.exp_add]
        dsimp [A]
        ring
      _ < 1 := hcj
  have hsmall := (div_lt_one hw).mp (hdispl.trans_lt hrj')
  have hbudget := (div_le_one₀ (sq_pos_of_pos hd)).mp (hcurve.trans hcj'.le)
  have hwle : (N : ℝ) ^ (-1 - (1 / 64 : ℝ)) ≤ 1 / N := by
    calc
      _ ≤ (N : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = _ := by rw [Real.rpow_neg_one, one_div]
  exact ⟨ha, hd, hbudget, hsmall.le.trans hwle, hsmall⟩

end Erdos522
