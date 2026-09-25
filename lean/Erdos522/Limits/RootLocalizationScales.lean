/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.TailSupremum
import Erdos522.Probability.DerivativeSupremum
import Erdos522.Probability.AnnularSmallDerivativeLimits
import Erdos522.Limits.PowerBlocks

/-!
# Localization scales for degree perturbations

At the derivative cutoff `N^(3/2)/N^(1/64)`, the maximal block tail isolates
regular roots in disks smaller than the radial window `N^(-1-1/64)`.
The curvature and radius inequalities follow from an explicit `N^(-1/32)`
power margin after logarithmic factors are included.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The derivative cutoff for root localization in a degree block. -/
def regularDerivativeThreshold (N : ℕ) : ℝ :=
  (N : ℝ) ^ (3 / 2 : ℝ) / (N : ℝ) ^ (1 / 64 : ℝ)

/-- A radial window wider than the root displacement caused by a degree block. -/
def radialMatchingWindow (N : ℕ) : ℝ := (N : ℝ) ^ (-1 - 1 / 64 : ℝ)

/-- The cutoff written as one power. -/
theorem regularDerivativeThreshold_eq {N : ℕ} (hN : 0 < N) :
    regularDerivativeThreshold N = (N : ℝ) ^ (95 / 64 : ℝ) := by
  rw [regularDerivativeThreshold, ← Real.rpow_sub (by exact_mod_cast hN : (0 : ℝ) < N)]
  congr 1
  norm_num

/-- The exact block amplitude is bounded by the degree-only envelope. -/
theorem eighth_power_tailAmplitude_le (j : ℕ) (hj : 60 ≤ j) (K : ℝ) :
    TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
      45 * Real.exp (2 * K) * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 16 : ℝ) *
        Real.sqrt (Real.log (j ^ 8 : ℕ)) := by
  have hN : (0 : ℝ) ≤ (j ^ 8 : ℕ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (j ^ 8 : ℕ) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ j ^ 8 from Nat.one_le_pow _ _ (by omega)))
  have hroot : Real.sqrt (9 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) * Real.log (j ^ 8 : ℕ)) =
      3 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 16 : ℝ) * Real.sqrt (Real.log (j ^ 8 : ℕ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 9 = 3 by norm_num, Real.sqrt_eq_rpow, ← Real.rpow_mul hN]
    norm_num
  unfold TailSupremum.tailAmplitude
  calc
    _ ≤ 15 * Real.exp (2 * K) *
        Real.sqrt (9 * ((j ^ 8 : ℕ) : ℝ) ^ (7 / 8 : ℝ) * Real.log (j ^ 8 : ℕ)) := by
      gcongr
      exact eighthPowerBlockLength_le_rpow j hj
    _ = _ := by rw [hroot]; ring

/-- The radius of an isolating disk divided by the matching window has a power margin. -/
theorem root_displacement_ratio_le {N : ℕ} (hN : 0 < N) {a K : ℝ}
    (ha : a ≤ 45 * Real.exp (2 * K) * (N : ℝ) ^ (7 / 16 : ℝ) * Real.sqrt (Real.log N)) :
    (2 * a / regularDerivativeThreshold N) / radialMatchingWindow N ≤
      90 * Real.exp (2 * K) * Real.sqrt (Real.log N) / (N : ℝ) ^ (1 / 32 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [regularDerivativeThreshold_eq hN, radialMatchingWindow]
  calc
    _ ≤ (2 * (45 * Real.exp (2 * K) * (N : ℝ) ^ (7 / 16 : ℝ) *
        Real.sqrt (Real.log N)) / (N : ℝ) ^ (95 / 64 : ℝ)) /
          (N : ℝ) ^ (-1 - 1 / 64 : ℝ) := by gcongr
    _ = (90 * Real.exp (2 * K) * Real.sqrt (Real.log N)) *
        ((N : ℝ) ^ (7 / 16 : ℝ) /
          ((N : ℝ) ^ (95 / 64 : ℝ) * (N : ℝ) ^ (-1 - 1 / 64 : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hn, ← Real.rpow_sub hn]
      norm_num
      rw [Real.rpow_neg hn.le]
      ring

/-- The Taylor curvature error divided by the square of the derivative cutoff has the
    same power margin, with the derivative-supremum constant unchanged. -/
theorem root_curvature_ratio_le {N : ℕ} (hN : 0 < N) {a K K' : ℝ}
    (ha : a ≤ 45 * Real.exp (2 * K') * (N : ℝ) ^ (7 / 16 : ℝ) * Real.sqrt (Real.log N)) :
    4 * DerivativeSupremum.secondDerivativeEnvelope N K * a /
        (regularDerivativeThreshold N) ^ 2 ≤
      180 * (100 * Real.exp (K + 4)) * Real.exp (2 * K') * Real.log N /
        (N : ℝ) ^ (1 / 32 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [regularDerivativeThreshold_eq hN, DerivativeSupremum.secondDerivativeEnvelope_eq]
  calc
    _ ≤ 4 * ((100 * Real.exp (K + 4)) * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N)) *
        (45 * Real.exp (2 * K') * (N : ℝ) ^ (7 / 16 : ℝ) * Real.sqrt (Real.log N)) /
          ((N : ℝ) ^ (95 / 64 : ℝ)) ^ 2 := by gcongr
    _ = (180 * (100 * Real.exp (K + 4)) * Real.exp (2 * K')) *
        (Real.sqrt (Real.log N)) ^ 2 *
          (((N : ℝ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ (7 / 16 : ℝ)) /
            ((N : ℝ) ^ (95 / 64 : ℝ)) ^ 2) := by ring
    _ = _ := by
      rw [Real.sq_sqrt hlog, ← Real.rpow_add hn, ← Real.rpow_mul_natCast hn.le,
        ← Real.rpow_sub hn]
      norm_num
      rw [Real.rpow_neg hn.le]
      ring

/-- The square root of a logarithm is dominated by every positive power. -/
theorem tendsto_sqrt_log_div_nat_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / (N : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) hs).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
    h.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Every scalar condition for annular root isolation holds eventually along the degree
    blocks, with the original finite-degree tail and derivative envelopes. -/
theorem eventually_eighth_power_root_localization (K K' : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let a := TailSupremum.tailAmplitude N (eighthPowerBlockLength j) K'
      let d := regularDerivativeThreshold N
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧ 2 * a / d < radialMatchingWindow N := by
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  have hr := (tendsto_sqrt_log_div_nat_rpow (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
    (90 * Real.exp (2 * K'))
  have hc := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
    (180 * (100 * Real.exp (K + 4)) * Real.exp (2 * K'))
  simp only [pow_one, mul_zero] at hr hc
  filter_upwards [eventually_ge_atTop 60, ht.eventually_ge_atTop 2,
    (hr.comp ht).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (hc.comp ht).eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with j hj hN hrj hcj
  dsimp only
  have hNpos : 0 < j ^ 8 := by omega
  have hn : (0 : ℝ) < (j ^ 8 : ℕ) := by exact_mod_cast hNpos
  have hn1 : (1 : ℝ) ≤ (j ^ 8 : ℕ) := by exact_mod_cast (show 1 ≤ j ^ 8 by omega)
  have hlog : 0 < Real.log (j ^ 8 : ℕ) := Real.log_pos (by exact_mod_cast hN)
  have hM : (0 : ℝ) < eighthPowerBlockLength j := by exact_mod_cast eighthPowerBlockLength_pos j
  have ha : 0 < TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K' := by
    unfold TailSupremum.tailAmplitude
    positivity
  have hd : 0 < regularDerivativeThreshold (j ^ 8) := by
    rw [regularDerivativeThreshold_eq hNpos]
    positivity
  have hw : 0 < radialMatchingWindow (j ^ 8) := Real.rpow_pos_of_pos hn _
  have hab := eighth_power_tailAmplitude_le j hj K'
  have hdispl := root_displacement_ratio_le hNpos hab
  have hcurve := root_curvature_ratio_le (K := K) hNpos hab
  have hrj' : 90 * Real.exp (2 * K') * Real.sqrt (Real.log (j ^ 8 : ℕ)) /
      ((j ^ 8 : ℕ) : ℝ) ^ (1 / 32 : ℝ) < 1 := by simpa only [Function.comp_def, mul_div_assoc] using hrj
  have hcj' : 180 * (100 * Real.exp (K + 4)) * Real.exp (2 * K') * Real.log (j ^ 8 : ℕ) /
      ((j ^ 8 : ℕ) : ℝ) ^ (1 / 32 : ℝ) < 1 := by simpa only [Function.comp_def, mul_div_assoc] using hcj
  have hsmall := (div_lt_one hw).mp (hdispl.trans_lt hrj')
  have hbudget := (div_le_one₀ (sq_pos_of_pos hd)).mp (hcurve.trans hcj'.le)
  have hwindow : radialMatchingWindow (j ^ 8) ≤ 1 / ((j ^ 8 : ℕ) : ℝ) := by
    calc
      _ ≤ ((j ^ 8 : ℕ) : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        norm_num
      _ = _ := by rw [Real.rpow_neg_one, one_div]
  exact ⟨ha, hd, hbudget, hsmall.le.trans hwindow, hsmall⟩

end Erdos522
