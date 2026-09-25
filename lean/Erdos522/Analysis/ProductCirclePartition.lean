/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.CirclePartition
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Dense angular cells on a finite probability product

The product partition keeps the finite random coordinate fixed while dividing
the angular coordinate into equal cells. Its total translation boundary loss
is independent of the size and atom weights of the finite probability space.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- A circle partition cell with the finite coordinate fixed. -/
def productCirclePartitionCell {Ω : Type*} {q : ℕ} (i : Ω × Fin q) :
    Set (Ω × AddCircle (1 : ℝ)) := {i.1} ×ˢ circlePartitionCell i.2

theorem measurableSet_productCirclePartitionCell {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {q : ℕ} (i : Ω × Fin q) :
    MeasurableSet (productCirclePartitionCell i) :=
  (measurableSet_singleton i.1).prod (measurableSet_circlePartitionCell i.2)

theorem pairwiseDisjoint_productCirclePartitionCell {Ω : Type*} {q : ℕ} (hq : 0 < q) :
    Pairwise (fun i j : Ω × Fin q =>
      Disjoint (productCirclePartitionCell i) (productCirclePartitionCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hfirst : i.1 = j.1 := hxi.1.symm.trans hxj.1
  have hsecond : i.2 ≠ j.2 := fun h => hij (Prod.ext hfirst h)
  exact Set.disjoint_left.mp (pairwiseDisjoint_circlePartitionCell hq hsecond) hxi.2 hxj.2

theorem iUnion_productCirclePartitionCell {Ω : Type*} {q : ℕ} (hq : 0 < q) :
    ⋃ i : Ω × Fin q, productCirclePartitionCell i = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.2 ∈ ⋃ j : Fin q, circlePartitionCell j := iUnion_circlePartitionCell hq ▸ mem_univ x.2
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨(x.1, j), ⟨rfl, hj⟩⟩

/-- Angular translation preserves an arbitrary finite-coordinate probability product. -/
theorem measurePreserving_product_angular_shift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (t : AddCircle (1 : ℝ)) :
    MeasurePreserving (fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + t))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) :=
  (MeasurePreserving.id μ).prod (measurePreserving_add_right AddCircle.haarAddCircle t)

/-- The summed boundary loss of the product partition is at most `q t`. -/
theorem sum_productCirclePartitionCell_boundary_loss_le {Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i : Ω × Fin q, (μ.prod AddCircle.haarAddCircle).real
      (productCirclePartitionCell i \
        (fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + (t : AddCircle (1 : ℝ)))) ⁻¹'
          productCirclePartitionCell i)) ≤ (q : ℝ) * t := by
  have heq (i : Ω × Fin q) : productCirclePartitionCell i \
      (fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + (t : AddCircle (1 : ℝ)))) ⁻¹'
        productCirclePartitionCell i =
      {i.1} ×ˢ (circlePartitionCell i.2 \
        (fun θ : AddCircle (1 : ℝ) => θ + (t : AddCircle (1 : ℝ))) ⁻¹'
          circlePartitionCell i.2) := by
    ext x
    simp only [productCirclePartitionCell, mem_sdiff, mem_prod, mem_singleton_iff, mem_preimage]
    tauto
  simp_rw [heq, measureReal_prod_prod]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ ω : Ω, μ.real {ω} * ((q : ℝ) * t) := by
      apply Finset.sum_le_sum
      intro ω _
      dsimp only
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_circlePartitionCell_boundary_loss_le hq ht)
        measureReal_nonneg
    _ = (q : ℝ) * t := by
      rw [← Finset.sum_mul, sum_measureReal_singleton]
      simp

/-- Dense cells capture translated mass up to `γ + q t`, uniformly over
the size of the finite probability space. -/
theorem dense_product_circle_cells_growth {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) (E : Set (Ω × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    (μ.prod AddCircle.haarAddCircle).real
        ((fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + (t : AddCircle (1 : ℝ)))) ⁻¹' E \ E) -
      γ - (q : ℝ) * t ≤
      (μ.prod AddCircle.haarAddCircle).real
        (densePartitionCells (μ.prod AddCircle.haarAddCircle)
          (productCirclePartitionCell (q := q)) E γ \ E) := by
  have hg := densePartitionCells_growth (μ.prod AddCircle.haarAddCircle)
    (productCirclePartitionCell (Ω := Ω) (q := q)) measurableSet_productCirclePartitionCell
    (pairwiseDisjoint_productCirclePartitionCell hq) (iUnion_productCirclePartitionCell hq)
    E hE hγ (measurePreserving_product_angular_shift μ (t : AddCircle (1 : ℝ)))
  have hb := sum_productCirclePartitionCell_boundary_loss_le μ hq ht
  linarith

/-- The one-cell angular partition has no translation boundary loss. -/
theorem dense_product_circle_cells_growth_one {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set (Ω × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    {γ : ℝ} (hγ : 0 ≤ γ) (t : AddCircle (1 : ℝ)) :
    (μ.prod AddCircle.haarAddCircle).real
        ((fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + t)) ⁻¹' E \ E) - γ ≤
      (μ.prod AddCircle.haarAddCircle).real
        (densePartitionCells (μ.prod AddCircle.haarAddCircle)
          (productCirclePartitionCell (q := 1)) E γ \ E) := by
  have hg := densePartitionCells_growth (μ.prod AddCircle.haarAddCircle)
    (productCirclePartitionCell (Ω := Ω) (q := 1)) measurableSet_productCirclePartitionCell
    (pairwiseDisjoint_productCirclePartitionCell (by decide : 0 < 1))
    (iUnion_productCirclePartitionCell (by decide : 0 < 1))
    E hE hγ (measurePreserving_product_angular_shift μ t)
  have hz (i : Ω × Fin 1) : productCirclePartitionCell i \
      (fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + t)) ⁻¹'
        productCirclePartitionCell i = ∅ := by
    ext x
    simp [productCirclePartitionCell, circlePartitionCell_one]
  simpa only [hz, measureReal_empty, Finset.sum_const_zero, sub_zero] using hg

end Erdos522
