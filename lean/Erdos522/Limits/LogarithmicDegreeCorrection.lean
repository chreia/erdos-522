/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CoefficientSequence
import Erdos522.Probability.AnnularSmallDerivativeLimits

/-!
# Vanishing logarithmic degree corrections

A logarithmic trailing-zero allowance contributes zero to the normalized
root count. The rounding by a natural ceiling and the shift from `N` to
`N + 1` both have explicit bounds.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Every fixed nonnegative logarithmic ceiling is negligible compared with degree. -/
theorem tendsto_logarithmic_degree_correction {D : ℝ} (hD : 0 ≤ D) :
    Tendsto (fun N : ℕ => (⌈D * Real.log (N + 1 : ℕ)⌉₊ : ℝ) / N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one] using
      tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim := (hlog.const_mul D).add (hinv.const_mul (D * Real.log 2 + 1))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : Real.log (N + 1 : ℕ) ≤ Real.log N + Real.log 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ Real.log ((N : ℝ) * 2) := Real.log_le_log (by positivity)
        (by
          have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
          linarith)
      _ = _ := Real.log_mul hn.ne' (by norm_num)
  have hl : 0 ≤ Real.log (N + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hD hl)).le
  have hb : (⌈D * Real.log (N + 1 : ℕ)⌉₊ : ℝ) ≤ D * Real.log N + (D * Real.log 2 + 1) := by
    have hm := mul_le_mul_of_nonneg_left hlogN hD
    linarith
  exact (div_le_div_of_nonneg_right hb hn.le).trans_eq (by ring)

/-- The geometric zero-run constant is positive for every nontrivial law. -/
theorem zeroRunLogarithmicConstant_pos (μ : Measure ℂ) (hatom : μ.real {0} < 1) :
    0 < zeroRunLogarithmicConstant μ := by
  have hl := Real.log_neg (zeroRunProbability_pos μ) (zeroRunProbability_lt_one μ hatom)
  unfold zeroRunLogarithmicConstant
  exact div_pos (by norm_num) (neg_pos.mpr hl)

/-- The actual-degree correction for a unit-second-moment law has vanishing density. -/
theorem tendsto_zero_run_degree_correction (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) :
    Tendsto (fun N : ℕ =>
      (⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ : ℝ) / N) atTop (𝓝 0) :=
  tendsto_logarithmic_degree_correction
    (zeroRunLogarithmicConstant_pos μ (zero_atom_lt_one_of_second_moment_one μ hsecond)).le

end Erdos522
