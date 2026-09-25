/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.Interval.Set.Union

/-!
# Uniform partitions of the unit interval

The half-open cells `[j/q,(j+1)/q)` partition `[0,1)` exactly. Their restricted
Lebesgue masses are `1/q`, and passage to the additive circle preserves the
normalized measure.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos522

/-- Lebesgue probability measure on the half-open unit interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

instance : IsProbabilityMeasure unitIntervalMeasure where
  measure_univ := by simp [unitIntervalMeasure, Real.volume_Ico]

/-- The `j`-th half-open cell of the uniform partition into `q` cells. -/
def unitIntervalCell {q : ℕ} (j : Fin q) : Set ℝ :=
  Ico ((j.val : ℝ) / q) (((j.val : ℝ) + 1) / q)

theorem measurableSet_unitIntervalCell {q : ℕ} (j : Fin q) :
    MeasurableSet (unitIntervalCell j) := measurableSet_Ico

/-- The lower endpoint is nonnegative, the endpoints are strictly ordered, and
    the upper endpoint is at most one. -/
theorem unitIntervalCell_endpoints {q : ℕ} (hq : 0 < q) (j : Fin q) :
    0 ≤ (j.val : ℝ) / q ∧
      (j.val : ℝ) / q < ((j.val : ℝ) + 1) / q ∧
        ((j.val : ℝ) + 1) / q ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨by positivity, (div_lt_div_iff_of_pos_right hqR).mpr (by linarith), ?_⟩
  apply (div_le_one hqR).mpr
  exact_mod_cast Nat.succ_le_of_lt j.isLt

/-- Every uniform cell is contained in the half-open unit interval. -/
theorem unitIntervalCell_subset {q : ℕ} (hq : 0 < q) (j : Fin q) :
    unitIntervalCell j ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  have hj := unitIntervalCell_endpoints hq j
  exact ⟨hj.1.trans hx.1, hx.2.trans_le hj.2.2⟩

/-- Every cell has length exactly `1/q`. -/
theorem unitIntervalCell_length {q : ℕ} (j : Fin q) :
    ((j.val : ℝ) + 1) / q - (j.val : ℝ) / q = 1 / q := by ring

/-- Distinct cells in the uniform partition are disjoint. -/
theorem pairwiseDisjoint_unitIntervalCell {q : ℕ} (hq : 0 < q) :
    Pairwise (fun i j : Fin q => Disjoint (unitIntervalCell i) (unitIntervalCell j)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdis {i j : Fin q} (hij : i < j) :
      Disjoint (unitIntervalCell i) (unitIntervalCell j) := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hbound : ((i.val : ℝ) + 1) / q ≤ (j.val : ℝ) / q := by
      apply (div_le_div_iff_of_pos_right hqR).mpr
      exact_mod_cast Nat.succ_le_of_lt hij
    exact (not_lt_of_ge hj.1) (hi.2.trans_le hbound)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hdis h
  · exact (hdis h).symm

/-- The uniform cells cover the half-open unit interval exactly. -/
theorem iUnion_unitIntervalCell {q : ℕ} (hq : 0 < q) :
    (⋃ j : Fin q, unitIntervalCell j) = Ico (0 : ℝ) 1 := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => unitIntervalCell_subset hq j
  · intro x hx
    have hcover := Ico_subset_biUnion_Ico q (fun k : ℕ => (k : ℝ) / q)
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hx' : x ∈ Ico ((0 : ℕ) / (q : ℝ)) ((q : ℝ) / q) := by
      simpa only [Nat.cast_zero, zero_div, div_self hqR] using hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx')
    apply mem_iUnion.mpr
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, ?_⟩
    simpa only [unitIntervalCell, Nat.cast_add, Nat.cast_one] using hxj

/-- The Lebesgue mass of a uniform cell is its exact length. -/
theorem volume_unitIntervalCell {q : ℕ} (j : Fin q) :
    volume (unitIntervalCell j) = ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [unitIntervalCell, Real.volume_Ico, unitIntervalCell_length]

/-- Restricting Lebesgue measure to the unit interval leaves each cell's mass
    unchanged. -/
theorem unitIntervalMeasure_cell {q : ℕ} (hq : 0 < q) (j : Fin q) :
    unitIntervalMeasure (unitIntervalCell j) = ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [unitIntervalMeasure, Measure.restrict_apply (measurableSet_unitIntervalCell j),
    Set.inter_eq_left.mpr (unitIntervalCell_subset hq j), volume_unitIntervalCell]

theorem unitIntervalMeasure_real_cell {q : ℕ} (hq : 0 < q) (j : Fin q) :
    unitIntervalMeasure.real (unitIntervalCell j) = 1 / (q : ℝ) := by
  rw [measureReal_def, unitIntervalMeasure_cell hq j, ENNReal.toReal_ofReal]
  positivity

theorem unitIntervalMeasure_real_cell_pos {q : ℕ} (hq : 0 < q) (j : Fin q) :
    0 < unitIntervalMeasure.real (unitIntervalCell j) := by
  rw [unitIntervalMeasure_real_cell hq j]
  positivity

/-- Integrating on a partition cell uses the same measure before and after the
    restriction to the unit interval. -/
theorem unitIntervalMeasure_restrict_cell {q : ℕ} (hq : 0 < q) (j : Fin q) :
    unitIntervalMeasure.restrict (unitIntervalCell j) = volume.restrict (unitIntervalCell j) := by
  rw [unitIntervalMeasure, Measure.restrict_restrict (measurableSet_unitIntervalCell j),
    Set.inter_eq_left.mpr (unitIntervalCell_subset hq j)]

/-- The quotient from the half-open unit interval preserves normalized Haar
    measure on the additive circle. -/
theorem measurePreserving_unitInterval_toCircle :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      unitIntervalMeasure AddCircle.haarAddCircle := by
  have h := UnitAddCircle.measurePreserving_mk 0
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  simpa only [unitIntervalMeasure, zero_add, restrict_Ico_eq_restrict_Ioc, hvol]
    using h

/-- An integral against normalized Haar measure equals the integral of the real
    lift on `[0,1)`, with no extra normalization factor. -/
theorem integral_unitInterval_lift_eq_haar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : AddCircle (1 : ℝ) → E) :
    (∫ x, f (x : AddCircle (1 : ℝ)) ∂unitIntervalMeasure) =
      ∫ θ, f θ ∂AddCircle.haarAddCircle := by
  have h := UnitAddCircle.integral_preimage 0 f
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  simpa only [unitIntervalMeasure, zero_add, restrict_Ico_eq_restrict_Ioc, hvol]
    using h

end Erdos522
