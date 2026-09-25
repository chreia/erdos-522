/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.UnitIntervalPartition
import Erdos522.Analysis.PartitionGrowth

/-!
# Uniform circle partitions and translation boundary loss

The half-open unit-interval partition descends to the additive circle. A
positive translation can remove at most its length from any individual cell.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- The half-open uniform cell on the circle, using its representative in `[0,1)`. -/
def circlePartitionCell {q : ℕ} (j : Fin q) : Set (AddCircle (1 : ℝ)) :=
  {θ | (AddCircle.equivIco (1 : ℝ) 0 θ).val ∈ unitIntervalCell j}

theorem measurableSet_circlePartitionCell {q : ℕ} (j : Fin q) :
    MeasurableSet (circlePartitionCell j) :=
  (measurableSet_unitIntervalCell j).preimage
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)

theorem mem_circlePartitionCell_coe {q : ℕ} (j : Fin q) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    (x : AddCircle (1 : ℝ)) ∈ circlePartitionCell j ↔ x ∈ unitIntervalCell j := by
  change (AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ))).val ∈ unitIntervalCell j ↔
    x ∈ unitIntervalCell j
  rw [AddCircle.equivIco_coe_eq (by simpa only [zero_add] using hx)]

theorem pairwiseDisjoint_circlePartitionCell {q : ℕ} (hq : 0 < q) :
    Pairwise (fun i j : Fin q => Disjoint (circlePartitionCell i) (circlePartitionCell j)) := by
  intro i j hij
  exact (pairwiseDisjoint_unitIntervalCell hq hij).preimage _

theorem iUnion_circlePartitionCell {q : ℕ} (hq : 0 < q) :
    ⋃ j : Fin q, circlePartitionCell j = univ := by
  apply Set.eq_univ_of_forall
  intro θ
  have hθ : (AddCircle.equivIco (1 : ℝ) 0 θ).val ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 θ).property
  rw [← iUnion_unitIntervalCell hq] at hθ
  obtain ⟨j, hj⟩ := mem_iUnion.mp hθ
  exact mem_iUnion.mpr ⟨j, hj⟩

/-- The one-cell partition is the entire circle. -/
theorem circlePartitionCell_one (j : Fin 1) : circlePartitionCell j = univ := by
  apply Set.eq_univ_of_forall
  intro θ
  have hj : j.val = 0 := by omega
  change (AddCircle.equivIco (1 : ℝ) 0 θ).val ∈ unitIntervalCell j
  simpa only [unitIntervalCell, hj, Nat.cast_zero, Nat.cast_one, zero_div, zero_add, div_one]
    using (AddCircle.equivIco (1 : ℝ) 0 θ).property

theorem haar_circlePartitionCell {q : ℕ} (hq : 0 < q) (j : Fin q) :
    AddCircle.haarAddCircle.real (circlePartitionCell j) = 1 / (q : ℝ) := by
  have hm := congrArg ENNReal.toReal (measurePreserving_unitInterval_toCircle.measure_preimage
    (measurableSet_circlePartitionCell j).nullMeasurableSet)
  change unitIntervalMeasure.real ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹'
    circlePartitionCell j) = AddCircle.haarAddCircle.real (circlePartitionCell j) at hm
  rw [← hm]
  change unitIntervalMeasure.real ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹'
    circlePartitionCell j) = _
  rw [unitIntervalMeasure, measureReal_restrict_apply' measurableSet_Ico]
  have heq : ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹' circlePartitionCell j) ∩
      Ico (0 : ℝ) 1 = unitIntervalCell j := by
    ext x
    constructor
    · intro hx
      exact (mem_circlePartitionCell_coe j hx.2).mp hx.1
    · intro hx
      have hunit := unitIntervalCell_subset hq j hx
      exact ⟨(mem_circlePartitionCell_coe j hunit).mpr hx, hunit⟩
  rw [heq, unitIntervalCell, Real.volume_real_Ico_of_le (unitIntervalCell_endpoints hq j).2.1.le,
    unitIntervalCell_length]

/-- A cell loses at most `t` of its normalized Haar measure under translation by `t ≥ 0`. -/
theorem circlePartitionCell_boundary_loss_le {q : ℕ} (hq : 0 < q) (j : Fin q)
    {t : ℝ} (ht : 0 ≤ t) :
    AddCircle.haarAddCircle.real (circlePartitionCell j \
      (fun θ : AddCircle (1 : ℝ) => θ + (t : AddCircle (1 : ℝ))) ⁻¹'
        circlePartitionCell j) ≤ t := by
  let S := circlePartitionCell j \
    (fun θ : AddCircle (1 : ℝ) => θ + (t : AddCircle (1 : ℝ))) ⁻¹' circlePartitionCell j
  have hS : MeasurableSet S := (measurableSet_circlePartitionCell j).diff
    ((measurableSet_circlePartitionCell j).preimage (by fun_prop))
  have hm := congrArg ENNReal.toReal (measurePreserving_unitInterval_toCircle.measure_preimage
    hS.nullMeasurableSet)
  change unitIntervalMeasure.real ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹' S) =
    AddCircle.haarAddCircle.real S at hm
  change AddCircle.haarAddCircle.real S ≤ t
  rw [← hm]
  rw [unitIntervalMeasure, measureReal_restrict_apply' measurableSet_Ico]
  have hsub : ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹' S) ∩ Ico (0 : ℝ) 1 ⊆
      Ico ((((j.val : ℝ) + 1) / q) - t) (((j.val : ℝ) + 1) / q) := by
    intro x hx
    have hxcell := (mem_circlePartitionCell_coe j hx.2).mp hx.1.1
    refine ⟨?_, hxcell.2⟩
    by_contra hn
    have hxshift : x + t ∈ unitIntervalCell j := ⟨by linarith [hxcell.1], by linarith⟩
    have hcircle := (mem_circlePartitionCell_coe j (unitIntervalCell_subset hq j hxshift)).mpr hxshift
    apply hx.1.2
    change (x : AddCircle (1 : ℝ)) + (t : AddCircle (1 : ℝ)) ∈ circlePartitionCell j
    simpa only [AddCircle.coe_add] using hcircle
  calc
    _ ≤ volume.real (Ico ((((j.val : ℝ) + 1) / q) - t) (((j.val : ℝ) + 1) / q)) :=
      measureReal_mono hsub (by simp only [Real.volume_Ico, ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true])
    _ = t := by rw [Real.volume_real_Ico_of_le (by linarith)]; ring

/-- Summing the boundary losses over the partition costs at most `q t`. -/
theorem sum_circlePartitionCell_boundary_loss_le {q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ j : Fin q, AddCircle.haarAddCircle.real (circlePartitionCell j \
      (fun θ : AddCircle (1 : ℝ) => θ + (t : AddCircle (1 : ℝ))) ⁻¹'
        circlePartitionCell j)) ≤ (q : ℝ) * t := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ)
      (fun (j : Fin q) _ => circlePartitionCell_boundary_loss_le hq j ht)

end Erdos522
