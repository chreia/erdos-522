/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeLimits

/-!
# Summable annular small-derivative failures

At degrees `j^8`, the polynomial failure rate becomes a summable logarithmic
perturbation of `j^(-3)`. Finite initial degrees do not affect summability.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The inverse of a natural power is summable when its exponent exceeds one. -/
theorem summable_inverse_nat_power (s : ℕ) (hs : 1 < s) :
    Summable (fun j : ℕ => 1 / (j : ℝ) ^ s) := by
  have hs' : -(s : ℝ) < -1 := by
    have hsr : (1 : ℝ) < s := by exact_mod_cast hs
    linarith
  apply (Real.summable_nat_rpow.mpr hs').congr
  intro j
  rw [Real.rpow_neg (Nat.cast_nonneg j), Real.rpow_natCast, one_div]

/-- Every fixed power of a logarithm divided by the cube is summable on the natural numbers. -/
theorem summable_log_pow_div_nat_cube (m : ℕ) :
    Summable (fun j : ℕ => (Real.log j) ^ m / (j : ℝ) ^ 3) := by
  have hsum : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) := summable_inverse_nat_power 2 (by norm_num)
  apply hsum.of_norm_bounded_eventually_nat
  have ht := tendsto_log_pow_div_nat_rpow m (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop 1, ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with j hj hlog
  have hjr : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hlog0 : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.rpow_one] at hlog
  have hlog' : (Real.log j) ^ m ≤ j := ((div_lt_one hjr).mp hlog).le
  calc
    _ ≤ (j : ℝ) / (j : ℝ) ^ 3 := div_le_div_of_nonneg_right hlog' (by positivity)
    _ = 1 / (j : ℝ) ^ 2 := by field_simp

/-- The explicit annular failure envelope is summable along eighth-power degrees. -/
theorem summable_annular_failure_envelope (C : ℝ) :
    Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 3 + 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10 +
      C * ((j ^ 8 : ℕ) : ℝ) ^ (-3 / 8 : ℝ) * (Real.log (j ^ 8 : ℕ)) ^ 4) := by
  have h₁ : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 24) := summable_inverse_nat_power 24 (by norm_num)
  have h₂ : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 80) := summable_inverse_nat_power 80 (by norm_num)
  have h₃ := (summable_log_pow_div_nat_cube 4).mul_left (4096 * C)
  apply (h₁.add h₂ |>.add h₃).congr
  intro j
  have hp : ((j ^ 8 : ℕ) : ℝ) ^ (-3 / 8 : ℝ) = 1 / (j : ℝ) ^ 3 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg j)]
    norm_num
  rw [hp, Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

/-- The actual small-derivative root failures are summable along the eighth-power subsequence. -/
theorem summable_annular_small_derivative_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ => (LogMoments.signMeasure (j ^ 8)).real {ω |
      (((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ)) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial (j ^ 8) ω) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}) := by
  obtain ⟨C, _, hbound⟩ := eventually_annular_small_derivative_probability K (K + 2) hK le_rfl
  apply (summable_annular_failure_envelope C).of_norm_bounded_eventually_nat
  have hcomp := (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually hbound
  filter_upwards [hcomp] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

end Erdos522
