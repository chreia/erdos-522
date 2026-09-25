/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Clipped sums and the largest entries

A subset maximizing the sum among all subsets of prescribed cardinality
contains the largest entries, with ties allowed. Clipping at its least entry
expresses the sum of the remaining entries. This gives an effective-degree
principle for finite logarithmic potentials.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- A maximizing subset of prescribed size contains entries at least as large
as every unselected entry. -/
theorem exists_subset_largest_entries {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) {d : ℕ} (hd : d ≤ I.card) :
    ∃ s ⊆ I, s.card = d ∧
      (∀ a ∈ s, ∀ b ∈ I, b ∉ s → p b ≤ p a) := by
  obtain ⟨s, hs, hmax⟩ := (I.powersetCard d).exists_max_image
    (fun t => ∑ i ∈ t, p i) (Finset.powersetCard_nonempty.mpr hd)
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
  refine ⟨s, hsub, hcard, ?_⟩
  intro a ha b hb hbs
  have hb' : b ∉ s.erase a := fun h => hbs (Finset.mem_of_mem_erase h)
  have hswap : insert b (s.erase a) ∈ I.powersetCard d := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.insert_subset hb ((Finset.erase_subset _ _).trans hsub)
    · rw [Finset.card_insert_of_notMem hb', Finset.card_erase_of_mem ha]
      have := Finset.card_pos.mpr ⟨a, ha⟩
      omega
  have h := hmax _ hswap
  rw [Finset.sum_insert hb', Finset.sum_erase_eq_sub ha] at h
  linarith

/-- At the least selected entry, clipping separates the selected cardinality
from the full sum of unselected entries. -/
theorem exists_clipped_sum_identity {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ I, 0 ≤ p i)
    {d : ℕ} (hd : 0 < d) (hdI : d ≤ I.card) :
    ∃ (s : Finset ι) (T : ℝ), s ⊆ I ∧ s.card = d ∧ 0 ≤ T ∧
      (∑ i ∈ I, min T (p i)) = d * T + ∑ i ∈ I \ s, p i := by
  obtain ⟨s, hs, hcard, hlarge⟩ := exists_subset_largest_entries I p hdI
  have hsnon : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image p hsnon
  refine ⟨s, p a, hs, hcard, hp a (hs ha), ?_⟩
  have hselected : (∑ i ∈ s, min (p a) (p i)) = d * p a := by
    calc
      _ = ∑ _i ∈ s, p a := Finset.sum_congr rfl fun i hi => min_eq_left (hmin i hi)
      _ = _ := by simp [hcard]
  have hunselected : (∑ i ∈ I \ s, min (p a) (p i)) = ∑ i ∈ I \ s, p i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hiI, his⟩ := Finset.mem_sdiff.mp hi
    exact min_eq_right (hlarge a ha i hiI his)
  have hsplit := Finset.sum_sdiff hs (f := fun i => min (p a) (p i))
  rw [hselected, hunselected] at hsplit
  linarith

/-- A uniform clipped-sum bound leaves at most `H` outside some `d` entries.
The bound counts entries rather than distinct values, so it retains ties. -/
theorem sum_le_largest_subset_add_of_clipped_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ I, 0 ≤ p i)
    {d : ℕ} (hd : 0 < d) (hdI : d ≤ I.card) {H : ℝ}
    (hclip : ∀ T : ℝ, 0 ≤ T → (∑ i ∈ I, min T (p i)) ≤ H + d * T) :
    ∃ s ⊆ I, s.card = d ∧ (∑ i ∈ I, p i) ≤ H + ∑ i ∈ s, p i := by
  obtain ⟨s, T, hs, hcard, hT, heq⟩ := exists_clipped_sum_identity I p hp hd hdI
  have h := hclip T hT
  rw [heq] at h
  have hsplit := Finset.sum_sdiff hs (f := p)
  exact ⟨s, hs, hcard, by linarith⟩

end Erdos522
