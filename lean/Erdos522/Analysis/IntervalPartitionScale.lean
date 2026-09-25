/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Choosing a uniform partition at a prescribed scale

Rounding the reciprocal of a target cell length produces a uniform partition
whose cell length lies between the target length and twice that length.
-/

namespace Erdos522

/-- A target scale at most one can be enlarged by a factor less than two so
that its reciprocal is a positive integer. -/
theorem exists_uniform_partition_scale {A τ : ℝ} (hA : 0 < A) (hτ : 0 < τ)
    (hsmall : A * τ ≤ 1) :
    ∃ (q : ℕ) (M : ℝ), 0 < q ∧ A ≤ M ∧ M < 2 * A ∧ 1 / (q : ℝ) = M * τ := by
  let q := ⌊1 / (A * τ)⌋₊
  have hprod := mul_pos hA hτ
  have hq1 : 1 ≤ q := (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hprod).mpr (by simpa))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlo : (q : ℝ) ≤ 1 / (A * τ) := Nat.floor_le (by positivity)
  have hhi : 1 / (A * τ) < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlower : (q : ℝ) * (A * τ) ≤ 1 := (le_div_iff₀ hprod).mp hlo
  have hupper : 1 < 2 * (q : ℝ) * (A * τ) := by
    have hh := (div_lt_iff₀ hprod).mp hhi
    nlinarith [mul_nonneg (sub_nonneg.mpr hqreal) hprod.le]
  refine ⟨q, 1 / ((q : ℝ) * τ), by omega, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos hqpos hτ)).mpr
    nlinarith [hlower]
  · apply (div_lt_iff₀ (mul_pos hqpos hτ)).mpr
    nlinarith [hupper]
  · field_simp

end Erdos522
