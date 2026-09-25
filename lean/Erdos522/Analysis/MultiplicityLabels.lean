/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.EquivFin

/-!
# Labels for finite multiplicities

A finite weighted set is represented by a finite labelled family, with one
label for each occurrence. Sums over the labelled family are exactly the
corresponding multiplicity-weighted sums.
-/

noncomputable section
open scoped BigOperators

namespace Erdos522

/-- One label for each occurrence in a finite set with natural multiplicities. -/
abbrev MultiplicityLabel {α : Type*} (s : Finset α) (n : α → ℕ) :=
  Σ u : s, Fin (n u)

/-- The number of multiplicity labels. -/
def multiplicityLabelCount {α : Type*} (s : Finset α) (n : α → ℕ) : ℕ :=
  Fintype.card (MultiplicityLabel s n)

/-- A finite enumeration retaining all multiplicities. -/
def multiplicityLabel {α : Type*} (s : Finset α) (n : α → ℕ) :
    Fin (multiplicityLabelCount s n) → α :=
  fun i => ((Fintype.equivFin (MultiplicityLabel s n)).symm i).1

/-- Every enumerated occurrence belongs to the original finite set. -/
theorem multiplicityLabel_mem {α : Type*} (s : Finset α) (n : α → ℕ)
    (i : Fin (multiplicityLabelCount s n)) : multiplicityLabel s n i ∈ s :=
  ((Fintype.equivFin (MultiplicityLabel s n)).symm i).1.2

/-- The number of labels is the total multiplicity. -/
theorem multiplicityLabelCount_eq_sum {α : Type*} (s : Finset α) (n : α → ℕ) :
    multiplicityLabelCount s n = ∑ u ∈ s, n u := by
  unfold multiplicityLabelCount
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_coe_sort]

/-- Enumerating occurrences turns every additive statistic into its exact
multiplicity-weighted sum. -/
theorem sum_multiplicityLabel {α M : Type*} [AddCommMonoid M]
    (s : Finset α) (n : α → ℕ) (p : α → M) :
    (∑ i, p (multiplicityLabel s n i)) = ∑ u ∈ s, n u • p u := by
  calc
    _ = ∑ i : MultiplicityLabel s n, p i.1 :=
      (Fintype.equivFin (MultiplicityLabel s n)).symm.sum_comp (fun i => p i.1)
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      exact Finset.sum_coe_sort s (fun u => n u • p u)

end Erdos522
