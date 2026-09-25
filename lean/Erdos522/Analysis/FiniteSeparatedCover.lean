/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite separated sets and coverings

A maximal separated subset of a finite metric space covers it by closed
balls. A packing bound therefore gives a covering bound with the same
number of centers.
-/

noncomputable section
namespace Erdos522

/-- A finite metric set has a separated subset whose closed balls cover it. -/
theorem exists_finite_separated_cover {α : Type*} [PseudoMetricSpace α]
    (S : Finset α) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ T : Finset α, T ⊆ S ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ δ := by
  classical
  let candidates := S.powerset.filter fun T =>
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ < dist x y
  have hne : candidates.Nonempty := ⟨∅, by simp [candidates]⟩
  obtain ⟨T, hT, hmax⟩ := candidates.exists_max_image Finset.card hne
  have hTsub : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hTsep := (Finset.mem_filter.mp hT).2
  refine ⟨T, hTsub, hTsep, ?_⟩
  intro x hx
  by_contra hcover
  push Not at hcover
  have hxT : x ∉ T := by
    intro hx'
    have h := hcover x hx'
    rw [dist_self] at h
    exact (not_lt_of_ge hδ) h
  have hinsert : insert x T ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hTsub), ?_⟩
    intro y hy z hz hyz
    rcases Finset.mem_insert.mp hy with rfl | hyT
    · rcases Finset.mem_insert.mp hz with rfl | hzT
      · exact False.elim (hyz rfl)
      · exact hcover z hzT
    · rcases Finset.mem_insert.mp hz with rfl | hzT
      · simpa only [dist_comm] using hcover y hyT
      · exact hTsep y hyT z hzT hyz
  have hcard := hmax _ hinsert
  rw [Finset.card_insert_of_notMem hxT] at hcard
  omega

/-- An upper bound for separated finite subsets gives a covering by that many balls. -/
theorem exists_finite_cover_of_packing_bound {α : Type*} [PseudoMetricSpace α]
    (S : Finset α) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (hpacking : ∀ T : Finset α, T ⊆ S →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ < dist x y) → T.card ≤ n) :
    ∃ T : Finset α, T ⊆ S ∧ T.card ≤ n ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ δ := by
  obtain ⟨T, hT, hsep, hcover⟩ := exists_finite_separated_cover S hδ
  exact ⟨T, hT, hpacking T hT hsep, hcover⟩

end Erdos522
