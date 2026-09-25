/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.UnitIntervalPartition
import Erdos522.Analysis.PartitionAverages

/-!
# Uniform cell averages and interval remainders

On a uniform cell, the average norm is `q` times its interval integral.
This identifies the interval remainder in an exponential approximation with
the corresponding piecewise constant norm average.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace Erdos522

/-- The average norm on a uniform cell is exactly `q` times its interval
    integral. The half-open endpoint convention leaves the integral unchanged. -/
theorem normCellAverage_unitIntervalCell {E : Type*} [NormedAddCommGroup E]
    {q : ℕ} (hq : 0 < q) (j : Fin q) (f : ℝ → E) :
    normCellAverage unitIntervalMeasure (unitIntervalCell j) f =
      (q : ℝ) * ∫ t in (j.val : ℝ) / q..((j.val : ℝ) + 1) / q, ‖f t‖ := by
  rw [normCellAverage, unitIntervalMeasure_real_cell hq j,
    unitIntervalMeasure_restrict_cell hq j]
  change (∫ t in Set.Ico ((j.val : ℝ) / q) (((j.val : ℝ) + 1) / q), ‖f t‖) /
    (1 / (q : ℝ)) = _
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (unitIntervalCell_endpoints hq j).2.1.le]
  rw [one_div, div_inv_eq_mul, mul_comm]

/-- The integral on a cell is the cell's length times its average norm. -/
theorem intervalIntegral_norm_eq_cell_length_mul_average {E : Type*} [NormedAddCommGroup E]
    {q : ℕ} (hq : 0 < q) (j : Fin q) (f : ℝ → E) :
    (∫ t in (j.val : ℝ) / q..((j.val : ℝ) + 1) / q, ‖f t‖) =
      (1 / (q : ℝ)) * normCellAverage unitIntervalMeasure (unitIntervalCell j) f := by
  rw [normCellAverage_unitIntervalCell hq j]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- The interval remainder of order `n` is the `n`-th power of the cell length
    times its average norm. -/
theorem cell_remainder_eq_length_pow_mul_average {E : Type*} [NormedAddCommGroup E]
    {q : ℕ} (hq : 0 < q) (j : Fin q) (f : ℝ → E) {n : ℕ} (hn : 0 < n) :
    (1 / (q : ℝ)) ^ (n - 1) *
      (∫ t in (j.val : ℝ) / q..((j.val : ℝ) + 1) / q, ‖f t‖) =
      (1 / (q : ℝ)) ^ n * normCellAverage unitIntervalMeasure (unitIntervalCell j) f := by
  rw [intervalIntegral_norm_eq_cell_length_mul_average hq j f, ← mul_assoc,
    ← pow_succ, Nat.sub_add_cancel hn]

/-- Within a cell, the piecewise average is the normalized interval integral
    for that same cell. -/
theorem partitionNormAverage_eq_cell_integral {E : Type*} [NormedAddCommGroup E]
    {q : ℕ} (hq : 0 < q) (j : Fin q) (f : ℝ → E) {x : ℝ}
    (hx : x ∈ unitIntervalCell j) :
    partitionNormAverage unitIntervalMeasure (@unitIntervalCell q) f x =
      (q : ℝ) * ∫ t in (j.val : ℝ) / q..((j.val : ℝ) + 1) / q, ‖f t‖ := by
  rw [partitionNormAverage_eq_of_mem unitIntervalMeasure _ f
    (pairwiseDisjoint_unitIntervalCell hq) hx, normCellAverage_unitIntervalCell hq j]

end Erdos522
