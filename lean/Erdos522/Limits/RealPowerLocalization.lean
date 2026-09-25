/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.RealPowerBlocks
import Erdos522.Limits.RootLocalizationScales

/-!
# Root localization on real-power degree blocks

The maximal-tail amplitude and the second-derivative envelope determine two
power margins. For a derivative cutoff `N^(3/2-ℓ)`, isolation needs
`2ℓ < 1/(2q)`, while a radial window `N^(-1-κ)` absorbs the displacement
when `ℓ + κ < 1/(2q)`.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The finite prefactor in the appended-tail envelope for real-power blocks. -/
def realPowerTailConstant (q K : ℝ) : ℝ :=
  15 * Real.exp (2 * K) * Real.sqrt (2 + q * 2 ^ q)

theorem realPowerTailConstant_pos {q : ℝ} (hq : 1 < q) (K : ℝ) :
    0 < realPowerTailConstant q K := by
  have hq0 : 0 < q := by linarith
  unfold realPowerTailConstant
  positivity

/-- The block amplitude retains the finite constant `15 exp(2K)`. -/
theorem real_power_tailAmplitude_le {q : ℝ} (hq : 1 < q) {j : ℕ} (hj : 2 ≤ j) (K : ℝ) :
    TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K ≤
      realPowerTailConstant q K * (realPowerDegree q j : ℝ) ^ (1 / 2 - 1 / (2 * q)) *
        Real.sqrt (Real.log (realPowerDegree q j)) := by
  have hq0 : 0 < q := by linarith
  have hN1 : (1 : ℝ) ≤ realPowerDegree q j := by
    exact_mod_cast (show 1 ≤ realPowerDegree q j from
      (by omega : 1 ≤ j).trans ((strictMono_realPowerDegree hq.le).id_le j))
  have hlog : 0 ≤ Real.log (realPowerDegree q j) := Real.log_nonneg hN1
  have hC : 0 ≤ 2 + q * 2 ^ q := by positivity
  have hroot : Real.sqrt ((2 + q * 2 ^ q) *
      (realPowerDegree q j : ℝ) ^ (1 - 1 / q) * Real.log (realPowerDegree q j)) =
      Real.sqrt (2 + q * 2 ^ q) *
        (realPowerDegree q j : ℝ) ^ (1 / 2 - 1 / (2 * q)) *
          Real.sqrt (Real.log (realPowerDegree q j)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC, Real.sqrt_eq_rpow ((realPowerDegree q j : ℝ) ^ (1 - 1 / q)),
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 2
    congr 1
    field_simp
  unfold TailSupremum.tailAmplitude
  calc
    _ ≤ 15 * Real.exp (2 * K) * Real.sqrt ((2 + q * 2 ^ q) *
        (realPowerDegree q j : ℝ) ^ (1 - 1 / q) * Real.log (realPowerDegree q j)) := by
      gcongr
      exact realPowerBlockLength_le_rpow hq hj
    _ = _ := by rw [hroot]; unfold realPowerTailConstant; ring

/-- The displacement-to-window ratio exhibits its full power margin. -/
theorem real_power_displacement_ratio_le {q ℓ κ A a : ℝ} {N : ℕ} (hN : 0 < N)
    (ha : a ≤ A * (N : ℝ) ^ (1 / 2 - 1 / (2 * q)) * Real.sqrt (Real.log N)) :
    (2 * a / (N : ℝ) ^ (3 / 2 - ℓ)) / (N : ℝ) ^ (-1 - κ) ≤
      2 * A * Real.sqrt (Real.log N) / (N : ℝ) ^ (1 / (2 * q) - ℓ - κ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (2 * (A * (N : ℝ) ^ (1 / 2 - 1 / (2 * q)) * Real.sqrt (Real.log N)) /
        (N : ℝ) ^ (3 / 2 - ℓ)) / (N : ℝ) ^ (-1 - κ) := by gcongr
    _ = (2 * A * Real.sqrt (Real.log N)) *
        ((N : ℝ) ^ (1 / 2 - 1 / (2 * q)) /
          ((N : ℝ) ^ (3 / 2 - ℓ) * (N : ℝ) ^ (-1 - κ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hn, ← Real.rpow_sub hn]
      rw [show (1 / 2 - 1 / (2 * q)) - ((3 / 2 - ℓ) + (-1 - κ)) =
        -(1 / (2 * q) - ℓ - κ) by ring, Real.rpow_neg hn.le]
      ring

/-- The Taylor curvature ratio has twice the derivative-scale exponent. -/
theorem real_power_curvature_ratio_le {q ℓ A a K : ℝ} {N : ℕ} (hN : 0 < N)
    (ha : a ≤ A * (N : ℝ) ^ (1 / 2 - 1 / (2 * q)) * Real.sqrt (Real.log N)) :
    4 * DerivativeSupremum.secondDerivativeEnvelope N K * a /
        ((N : ℝ) ^ (3 / 2 - ℓ)) ^ 2 ≤
      4 * (100 * Real.exp (K + 4)) * A * Real.log N /
        (N : ℝ) ^ (1 / (2 * q) - 2 * ℓ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [DerivativeSupremum.secondDerivativeEnvelope_eq]
  calc
    _ ≤ 4 * ((100 * Real.exp (K + 4)) * (N : ℝ) ^ (5 / 2 : ℝ) *
        Real.sqrt (Real.log N)) *
        (A * (N : ℝ) ^ (1 / 2 - 1 / (2 * q)) * Real.sqrt (Real.log N)) /
          ((N : ℝ) ^ (3 / 2 - ℓ)) ^ 2 := by gcongr
    _ = (4 * (100 * Real.exp (K + 4)) * A) * (Real.sqrt (Real.log N)) ^ 2 *
        (((N : ℝ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 - 1 / (2 * q))) /
          ((N : ℝ) ^ (3 / 2 - ℓ)) ^ 2) := by ring
    _ = _ := by
      rw [Real.sq_sqrt hlog, ← Real.rpow_add hn, ← Real.rpow_mul_natCast hn.le,
        ← Real.rpow_sub hn]
      rw [show (5 / 2 + (1 / 2 - 1 / (2 * q))) - (3 / 2 - ℓ) * (2 : ℕ) =
        -(1 / (2 * q) - 2 * ℓ) by norm_num; ring, Real.rpow_neg hn.le]
      ring

/-- All deterministic Taylor and displacement hypotheses hold eventually at the
actual maximal-tail amplitude of a real-power block. -/
theorem eventually_real_power_root_localization {q ℓ κ : ℝ} (hq : 1 < q)
    (hκ : 0 ≤ κ) (hisolation : 2 * ℓ < 1 / (2 * q))
    (hwindow : ℓ + κ < 1 / (2 * q)) (K K' : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let a := TailSupremum.tailAmplitude N (realPowerBlockLength q j) K'
      let d := (N : ℝ) ^ (3 / 2 - ℓ)
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧ 2 * a / d < (N : ℝ) ^ (-1 - κ) := by
  have ht := tendsto_realPowerDegree (show 0 < q by linarith)
  have hr := (tendsto_sqrt_log_div_nat_rpow
    (show 0 < 1 / (2 * q) - ℓ - κ by linarith)).const_mul
      (2 * realPowerTailConstant q K')
  have hc := (tendsto_log_pow_div_nat_rpow 1
    (show 0 < 1 / (2 * q) - 2 * ℓ by linarith)).const_mul
      (4 * (100 * Real.exp (K + 4)) * realPowerTailConstant q K')
  simp only [pow_one, mul_zero] at hr hc
  filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop 2,
    (hr.comp ht).eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    (hc.comp ht).eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with j hj hN hrj hcj
  dsimp only
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast (show 0 < realPowerDegree q j by omega)
  have hn1 : (1 : ℝ) ≤ realPowerDegree q j := by exact_mod_cast (show 1 ≤ realPowerDegree q j by omega)
  have hlog : 0 < Real.log (realPowerDegree q j) := Real.log_pos (by exact_mod_cast hN)
  have hM : (0 : ℝ) < realPowerBlockLength q j := by exact_mod_cast realPowerBlockLength_pos hq.le j
  have ha : 0 < TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K' := by
    unfold TailSupremum.tailAmplitude
    positivity
  have hd : 0 < (realPowerDegree q j : ℝ) ^ (3 / 2 - ℓ) := Real.rpow_pos_of_pos hn _
  have hw : 0 < (realPowerDegree q j : ℝ) ^ (-1 - κ) := Real.rpow_pos_of_pos hn _
  have hab := real_power_tailAmplitude_le hq hj K'
  have hdispl := real_power_displacement_ratio_le (ℓ := ℓ) (κ := κ) (by omega : 0 < realPowerDegree q j) hab
  have hcurve := real_power_curvature_ratio_le (ℓ := ℓ) (K := K) (by omega : 0 < realPowerDegree q j) hab
  have hrj' : 2 * realPowerTailConstant q K' * Real.sqrt (Real.log (realPowerDegree q j)) /
      (realPowerDegree q j : ℝ) ^ (1 / (2 * q) - ℓ - κ) < 1 := by
    simpa only [Function.comp_def, mul_div_assoc] using hrj
  have hcj' : 4 * (100 * Real.exp (K + 4)) * realPowerTailConstant q K' *
      Real.log (realPowerDegree q j) / (realPowerDegree q j : ℝ) ^ (1 / (2 * q) - 2 * ℓ) < 1 := by
    simpa only [Function.comp_def, mul_div_assoc] using hcj
  have hsmall := (div_lt_one hw).mp (hdispl.trans_lt hrj')
  have hbudget := (div_le_one₀ (sq_pos_of_pos hd)).mp (hcurve.trans hcj'.le)
  have hwle : (realPowerDegree q j : ℝ) ^ (-1 - κ) ≤ 1 / realPowerDegree q j := by
    calc
      _ ≤ (realPowerDegree q j : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = _ := by rw [Real.rpow_neg_one, one_div]
  exact ⟨ha, hd, hbudget, hsmall.le.trans hwle, hsmall⟩

end Erdos522
