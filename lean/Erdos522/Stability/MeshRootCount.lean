/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AnnularMesh

/-!
# Root counts from detected mesh cells

Finite covers count polynomial roots with their original multiplicities. A
small-derivative root outside the real sectors belongs to a detected cell, and
the local zero bound controls the multiplicity contributed by each cell.
-/

noncomputable section
open scoped BigOperators

namespace Erdos522

/-- A finite union of sets has at most the sum of their multiplicity-counted roots. -/
theorem zeroCountIn_biUnion_le (P : Polynomial ℂ) {ι : Type*} (t : Finset ι)
    (s : ι → Set ℂ) :
    zeroCountIn P (⋃ i ∈ t, s i) ≤ ∑ i ∈ t, zeroCountIn P (s i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ht =>
    rw [Finset.sum_insert hi]
    have heq : (⋃ j ∈ insert i t, s j) = s i ∪ ⋃ j ∈ t, s j := by
      ext z
      simp
    rw [heq]
    exact (zeroCountIn_union_le P _ _).trans (Nat.add_le_add_left ht _)

/-- A cover need only hold on the roots themselves; repeated roots retain their multiplicity. -/
theorem zeroCountIn_le_sum_of_root_cover (P : Polynomial ℂ) {ι : Type*} (t : Finset ι)
    (s : Set ℂ) (cells : ι → Set ℂ)
    (hcover : ∀ α ∈ P.roots, α ∈ s → ∃ i ∈ t, α ∈ cells i) :
    zeroCountIn P s ≤ ∑ i ∈ t, zeroCountIn P (cells i) := by
  classical
  have hsub : P.roots.filter (fun α => α ∈ s) ≤
      P.roots.filter (fun α => α ∈ ⋃ i ∈ t, cells i) := by
    apply Multiset.le_filter.mpr
    refine ⟨Multiset.filter_le _ _, ?_⟩
    intro α hα
    obtain ⟨hi, hs⟩ := Multiset.mem_filter.mp hα
    obtain ⟨i, hit, hic⟩ := hcover α hi hs
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hit, hic⟩⟩
  exact (Multiset.card_le_card hsub).trans (zeroCountIn_biUnion_le P t cells)

/-- Uniform local counts turn a finite root cover into a cardinality bound. -/
theorem zeroCountIn_le_card_mul_of_root_cover (P : Polynomial ℂ) {ι : Type*} (t : Finset ι)
    (s : Set ℂ) (cells : ι → Set ℂ) {B : ℝ}
    (hcover : ∀ α ∈ P.roots, α ∈ s → ∃ i ∈ t, α ∈ cells i)
    (hlocal : ∀ i ∈ t, (zeroCountIn P (cells i) : ℝ) ≤ B) :
    (zeroCountIn P s : ℝ) ≤ (t.card : ℝ) * B := by
  have hc : (zeroCountIn P s : ℝ) ≤ ∑ i ∈ t, (zeroCountIn P (cells i) : ℝ) := by
    exact_mod_cast zeroCountIn_le_sum_of_root_cover P t s cells hcover
  exact hc.trans (by simpa using Finset.sum_le_sum hlocal)

/-- Annular small-derivative roots outside the doubled real sectors. -/
def annularSmallDerivativeRegion (P : Polynomial ℂ) (N : ℕ) (K L : ℝ) : Set ℂ :=
  {α | |‖α‖ - 1| ≤ K / N ∧
    ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L ∧
    2 / Real.sqrt N ≤ realAxisAngularDistance (Complex.arg α : Real.Angle)}

/-- Mesh indices retained by the angular exclusion and the two jet thresholds. -/
def detectedAnnularMesh (P : Polynomial ℂ) (N : ℕ) (K S L : ℝ) :
    Finset (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) := by
  classical
  exact Finset.univ.filter fun i =>
    1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle (derivativeMeshSpacing N S L) i.2) ∧
    ‖P.eval (annularMeshPoint N K (derivativeMeshSpacing N S L) i)‖ / Real.sqrt N ≤
      derivativeMeshValueThreshold N S L ∧
    ‖annularMeshPoint N K (derivativeMeshSpacing N S L) i *
      P.derivative.eval (annularMeshPoint N K (derivativeMeshSpacing N S L) i)‖ /
        (N : ℝ) ^ (3 / 2 : ℝ) ≤ 3 / L

/-- Every root in the retained small-derivative region belongs to a detected closed cell. -/
theorem annular_small_derivative_root_cover (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K S L : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hKN : K + 1 ≤ (N : ℝ))
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N))
    (α : ℂ) (hroot : α ∈ P.roots) (hα : α ∈ annularSmallDerivativeRegion P N K L) :
    ∃ i ∈ detectedAnnularMesh P N K S L,
      α ∈ Metric.closedBall (annularMeshPoint N K (derivativeMeshSpacing N S L) i)
        (derivativeMeshSpacing N S L) := by
  classical
  obtain ⟨i, hnear, hretained⟩ := exists_retained_annular_root_mesh_detection P hN hK hS hL hKN
    hα.1 (Polynomial.isRoot_of_mem_roots hroot) hα.2.1 hα.2.2 hbound
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hretained⟩,
    by simpa only [Metric.mem_closedBall, dist_eq_norm] using hnear⟩

/-- Detected mesh cells bound the annular small-derivative root count, with multiplicity. -/
theorem annular_small_derivative_count_le (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K K' S L B : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hKN : K + 1 ≤ (N : ℝ)) (hK' : K + 1 ≤ 2 * K')
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N))
    (hlocal : ∀ c : ℂ, ‖c‖ = 1 →
      (zeroCountIn P (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B) :
    (zeroCountIn P (annularSmallDerivativeRegion P N K L) : ℝ) ≤
      (detectedAnnularMesh P N K S L).card * B := by
  apply zeroCountIn_le_card_mul_of_root_cover P (detectedAnnularMesh P N K S L)
    (annularSmallDerivativeRegion P N K L)
    (fun i => Metric.closedBall (annularMeshPoint N K (derivativeMeshSpacing N S L) i)
      (derivativeMeshSpacing N S L))
  · exact annular_small_derivative_root_cover P hN hK hS hL hKN hbound
  · intro i _
    exact annular_mesh_cell_zero_count_le P hN hK hS hL (by linarith) hK' hlocal i

end Erdos522
