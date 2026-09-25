/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-!
# Growth through cells with positive density

A measure-preserving translation can lose mass in low-density partition cells
only through their boundaries. Consequently, most of its new mass lies in
the union of cells on which the original set occupies a prescribed fraction.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- The union of cells in which `E` has relative mass at least `γ`. -/
def densePartitionCells {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (cells : ι → Set Ω) (E : Set Ω) (γ : ℝ) : Set Ω :=
  ⋃ i, if γ * μ.real (cells i) ≤ μ.real (E ∩ cells i) then cells i else ∅

theorem measurableSet_densePartitionCells {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (μ : Measure Ω) (cells : ι → Set Ω) (E : Set Ω) (γ : ℝ)
    (hc : ∀ i, MeasurableSet (cells i)) :
    MeasurableSet (densePartitionCells μ cells E γ) := by
  classical
  exact MeasurableSet.iUnion fun i => by split_ifs <;> simp_all

/-- Pulling a set back by a measure-preserving map changes its mass in a
cell by at most the mass crossing that cell's boundary. -/
theorem measure_preimage_inter_cell_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (E J : Set Ω) (hE : MeasurableSet E) (hJ : MeasurableSet J) :
    μ.real (T ⁻¹' E ∩ J) ≤ μ.real (E ∩ J) + μ.real (J \ T ⁻¹' J) := by
  have hsub : T ⁻¹' E ∩ J ⊆ T ⁻¹' (E ∩ J) ∪ (J \ T ⁻¹' J) := by
    intro x hx
    by_cases hxJ : T x ∈ J
    · exact Or.inl ⟨hx.1, hxJ⟩
    · exact Or.inr ⟨hx.2, hxJ⟩
  have hpre : μ.real (T ⁻¹' (E ∩ J)) = μ.real (E ∩ J) :=
    congrArg ENNReal.toReal (hT.measure_preimage (hE.inter hJ).nullMeasurableSet)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans_eq
    (congrArg (fun x => x + μ.real (J \ T ⁻¹' J)) hpre))

/-- New translated mass is captured by dense cells, up to the density
threshold and the total partition boundary loss. -/
theorem densePartitionCells_growth {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (cells : ι → Set Ω)
    (hc : ∀ i, MeasurableSet (cells i))
    (hdis : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hcover : ⋃ i, cells i = Set.univ) (E : Set Ω) (hE : MeasurableSet E)
    {γ : ℝ} (hγ : 0 ≤ γ) {T : Ω → Ω} (hT : MeasurePreserving T μ μ) :
    μ.real (T ⁻¹' E \ E) - γ - ∑ i, μ.real (cells i \ T ⁻¹' cells i) ≤
      μ.real (densePartitionCells μ cells E γ \ E) := by
  classical
  let W := densePartitionCells μ cells E γ
  let B (i : ι) := if γ * μ.real (cells i) ≤ μ.real (E ∩ cells i)
    then ∅ else T ⁻¹' E ∩ cells i
  have hsub : T ⁻¹' E \ E ⊆ (W \ E) ∪ ⋃ i, B i := by
    intro x hx
    have hxcover : x ∈ ⋃ i, cells i := hcover ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
    by_cases hd : γ * μ.real (cells i) ≤ μ.real (E ∩ cells i)
    · left
      refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, hx.2⟩
      simpa only [ite_eq_left hd] using hi
    · right
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [B, ite_eq_right hd]
      exact ⟨hx.1, hi⟩
  have hB (i : ι) : μ.real (B i) ≤
      γ * μ.real (cells i) + μ.real (cells i \ T ⁻¹' cells i) := by
    dsimp only [B]
    split_ifs with hd
    · simpa only [measureReal_empty] using add_nonneg
        (mul_nonneg hγ measureReal_nonneg) measureReal_nonneg
    · exact (measure_preimage_inter_cell_le μ hT E (cells i) hE (hc i)).trans
        (add_le_add (le_of_not_ge hd) le_rfl)
  have hsum : ∑ i, μ.real (cells i) = 1 := by
    rw [← measureReal_iUnion_fintype hdis hc, hcover]
    simp
  have hbound : μ.real (T ⁻¹' E \ E) ≤ μ.real (W \ E) +
      (γ + ∑ i, μ.real (cells i \ T ⁻¹' cells i)) := by
    apply (measureReal_mono hsub).trans
    apply (measureReal_union_le _ _).trans
    apply add_le_add le_rfl
    apply (measureReal_iUnion_fintype_le B).trans
    calc
      _ ≤ ∑ i, (γ * μ.real (cells i) + μ.real (cells i \ T ⁻¹' cells i)) :=
        Finset.sum_le_sum fun i _ => hB i
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one]
  linarith

end Erdos522
