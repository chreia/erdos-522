/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.ZeroCount
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Choose

/-!
# Deterministic root matching, with multiplicities

A partial matching is a multiset of pairs whose projections are submultisets of
the two root multisets, preserving multiplicities. Unmatched roots contribute
the degree term. For disjoint preconnected domains containing one root of each
polynomial, only domains crossing the target circle can change membership.
-/

noncomputable section
namespace Erdos522

attribute [local instance] Classical.propDecidable

/-- Predicate counts on paired objects differ only at pairs where the predicates disagree. -/
theorem paired_count_le {α : Type*} (pairs : Multiset (α × α))
    (p : α → Prop) [DecidablePred p] :
    pairs.countP (fun z ↦ p z.1) ≤ pairs.countP (fun z ↦ p z.2) +
      pairs.countP (fun z ↦ ¬ (p z.1 ↔ p z.2)) := by
  classical
  induction pairs using Multiset.induction_on with
  | empty => simp
  | @cons z pairs ih =>
    rcases z with ⟨x, y⟩
    by_cases hx : p x <;> by_cases hy : p y <;>
      simp only [Multiset.countP_cons, hx, hy, iff_self, not_true_eq_false,
        iff_true, iff_false, not_false_eq_true, ite_true, ite_false] at * <;> omega

/-- The reverse one-sided comparison for paired predicate counts. -/
theorem paired_count_ge {α : Type*} (pairs : Multiset (α × α))
    (p : α → Prop) [DecidablePred p] :
    pairs.countP (fun z ↦ p z.2) ≤ pairs.countP (fun z ↦ p z.1) +
      pairs.countP (fun z ↦ ¬ (p z.1 ↔ p z.2)) := by
  classical
  induction pairs using Multiset.induction_on with
  | empty => simp
  | @cons z pairs ih =>
    rcases z with ⟨x, y⟩
    by_cases hx : p x <;> by_cases hy : p y <;>
      simp only [Multiset.countP_cons, hx, hy, iff_self, not_true_eq_false,
        iff_true, iff_false, not_false_eq_true, ite_true, ite_false] at * <;> omega

/-- A multiplicity-preserving partial matching controls predicate counts.
The last natural-number subtraction is the positive part of the size change. -/
theorem multiset_matching_bound {α : Type*} (u v : Multiset α)
    (pairs : Multiset (α × α)) (p : α → Prop) [DecidablePred p]
    (hleft : pairs.map Prod.fst ≤ u) (hright : pairs.map Prod.snd ≤ v) :
    Nat.dist (v.countP p) (u.countP p) ≤
      pairs.countP (fun z ↦ ¬ (p z.1 ↔ p z.2)) +
        (u.card - pairs.card) + (v.card - u.card) := by
  classical
  obtain ⟨u', hu⟩ := Multiset.le_iff_exists_add.mp hleft
  obtain ⟨v', hv⟩ := Multiset.le_iff_exists_add.mp hright
  have huc := congrArg Multiset.card hu
  have hvc := congrArg Multiset.card hv
  have hup := congrArg (Multiset.countP p) hu
  have hvp := congrArg (Multiset.countP p) hv
  simp only [Multiset.card_add, Multiset.card_map] at huc hvc
  simp only [Multiset.countP_add, Multiset.countP_map, ← Multiset.countP_eq_card_filter] at hup hvp
  have hul := Multiset.countP_le_card p u'
  have hvl := Multiset.countP_le_card p v'
  have hf := paired_count_le pairs p
  have hb := paired_count_ge pairs p
  unfold Nat.dist
  omega

/-- Root-count comparison from an explicit partial matching. Roots on the
boundary and repeated unmatched roots require no additional hypotheses. -/
theorem root_matching_bound (P Q : Polynomial ℂ) (s : Set ℂ)
    (pairs : Multiset (ℂ × ℂ))
    (hleft : pairs.map Prod.fst ≤ P.roots)
    (hright : pairs.map Prod.snd ≤ Q.roots) :
    Nat.dist (zeroCountIn Q s) (zeroCountIn P s) ≤
      pairs.countP (fun z ↦ ¬ (z.1 ∈ s ↔ z.2 ∈ s)) +
        (P.natDegree - pairs.card) + (Q.natDegree - P.natDegree) := by
  classical
  have h := multiset_matching_bound P.roots Q.roots pairs (fun z ↦ z ∈ s) hleft hright
  simpa only [zeroCountIn, ← Multiset.countP_eq_card_filter,
    IsAlgClosed.card_roots_eq_natDegree] using h

/-- A convenient closed-disk specialization with an externally bounded number
of crossing pairs. The crossing budget can include disks touching the circle. -/
theorem closed_root_matching_bound (P Q : Polynomial ℂ) (r : ℝ)
    (pairs : Multiset (ℂ × ℂ)) (c : ℕ)
    (hleft : pairs.map Prod.fst ≤ P.roots)
    (hright : pairs.map Prod.snd ≤ Q.roots)
    (hcross : pairs.countP (fun z ↦ ¬ (‖z.1‖ ≤ r ↔ ‖z.2‖ ≤ r)) ≤ c) :
    Nat.dist (closedZeroCount Q r) (closedZeroCount P r) ≤
      c + (P.natDegree - pairs.card) + (Q.natDegree - P.natDegree) := by
  classical
  have h := root_matching_bound P Q {z | ‖z‖ ≤ r} pairs hleft hright
  simp only [Set.mem_ofPred_eq] at h
  change Nat.dist (closedZeroCount Q r) (closedZeroCount P r) ≤ _ at h
  exact h.trans (by omega)

/-- A finite injective choice of roots yields a multiplicity-preserving submultiset. -/
theorem selected_roots_le {ι : Type*} [Fintype ι] (P : Polynomial ℂ)
    (z : ι → ℂ) (hinj : Function.Injective z) (hroot : ∀ i, z i ∈ P.roots) :
    (Finset.univ.val.map z) ≤ P.roots := by
  classical
  apply (Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)).mpr
  intro w hw
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hw
  exact hroot i

/-- Finite-family matching, with a specified set of exceptional indices. -/
theorem finite_root_matching_bound {ι : Type*} [Fintype ι]
    (P Q : Polynomial ℂ) (s : Set ℂ) (z w : ι → ℂ) (cross : ι → Prop)
    (hz : Function.Injective z) (hw : Function.Injective w)
    (hzroot : ∀ i, z i ∈ P.roots) (hwroot : ∀ i, w i ∈ Q.roots)
    (hagree : ∀ i, ¬ cross i → (z i ∈ s ↔ w i ∈ s)) :
    Nat.dist (zeroCountIn Q s) (zeroCountIn P s) ≤
      (Finset.univ.filter cross).card + (P.natDegree - Fintype.card ι) +
        (Q.natDegree - P.natDegree) := by
  classical
  let pairs : Multiset (ℂ × ℂ) := Finset.univ.val.map (fun i ↦ (z i, w i))
  have hleft : pairs.map Prod.fst ≤ P.roots := by
    simpa only [pairs, Multiset.map_map, Function.comp_def] using
      selected_roots_le P z hz hzroot
  have hright : pairs.map Prod.snd ≤ Q.roots := by
    simpa only [pairs, Multiset.map_map, Function.comp_def] using
      selected_roots_le Q w hw hwroot
  have hc : pairs.countP (fun a ↦ ¬ (a.1 ∈ s ↔ a.2 ∈ s)) ≤
      (Finset.univ.filter cross).card := by
    simp only [pairs, Multiset.countP_map]
    apply Multiset.card_le_card
    apply Multiset.le_filter.mpr
    refine ⟨Multiset.filter_le _ _, ?_⟩
    intro i hi
    by_contra h
    exact (Multiset.mem_filter.mp hi).2 (hagree i h)
  have h := root_matching_bound P Q s pairs hleft hright
  have hn : pairs.card = Fintype.card ι := by simp [pairs]
  rw [hn] at h
  omega

/-- On a preconnected set missing a circle, closed-disk membership is constant. -/
theorem disk_membership_constant {D : Set ℂ} (hD : IsPreconnected D) (r : ℝ)
    (hmiss : ∀ z ∈ D, ‖z‖ ≠ r) {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) :
    (‖z‖ ≤ r ↔ ‖w‖ ≤ r) := by
  have no_cross : ∀ {x y : ℂ}, x ∈ D → y ∈ D → ‖x‖ ≤ r → r < ‖y‖ → False := by
    intro x y hx hy hxr hry
    obtain ⟨v, hv, he⟩ := hD.intermediate_value hx hy continuous_norm.continuousOn
      (show r ∈ Set.Icc ‖x‖ ‖y‖ from ⟨hxr, hry.le⟩)
    exact hmiss v hv he
  constructor
  · intro hz'
    by_contra hw'
    exact no_cross hz hw hz' (lt_of_not_ge hw')
  · intro hw'
    by_contra hz'
    exact no_cross hw hz hw' (lt_of_not_ge hz')

/-- Disjoint preconnected domains containing one root of each polynomial give
a partial matching. Only domains whose closures meet the target circle can
change closed-disk membership. Unmatched roots contribute the degree term. -/
theorem disjoint_domain_root_matching {ι : Type*} [Fintype ι]
    (P Q : Polynomial ℂ) (D : ι → Set ℂ) (r : ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hconn : ∀ i, IsPreconnected (D i))
    (hP : ∀ i, zeroCountIn P (D i) = 1)
    (hQ : ∀ i, zeroCountIn Q (D i) = 1) :
    Nat.dist (closedZeroCount Q r) (closedZeroCount P r) ≤
      (Finset.univ.filter (fun i ↦ ∃ z ∈ closure (D i), ‖z‖ = r)).card +
        (P.natDegree - Fintype.card ι) + (Q.natDegree - P.natDegree) := by
  classical
  have choose_root : ∀ R : Polynomial ℂ, (∀ i, zeroCountIn R (D i) = 1) →
      ∃ z : ι → ℂ, (∀ i, z i ∈ R.roots ∧ z i ∈ D i) ∧ Function.Injective z := by
    intro R hR
    have hex : ∀ i, ∃ z, z ∈ R.roots ∧ z ∈ D i := by
      intro i
      have hc : 0 < (R.roots.filter (fun z ↦ z ∈ D i)).card := by
        change 0 < zeroCountIn R (D i)
        rw [hR i]
        exact Nat.zero_lt_one
      obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hc
      exact ⟨z, Multiset.mem_filter.mp hz⟩
    choose z hz using hex
    refine ⟨z, hz, ?_⟩
    intro i j he
    by_contra hij
    exact Set.disjoint_left.mp (hdisj i j hij) (hz i).2 (he ▸ (hz j).2)
  obtain ⟨z, hz, hzinj⟩ := choose_root P hP
  obtain ⟨w, hw, hwinj⟩ := choose_root Q hQ
  apply finite_root_matching_bound P Q {z | ‖z‖ ≤ r} z w
    (fun i ↦ ∃ z ∈ closure (D i), ‖z‖ = r) hzinj hwinj
    (fun i ↦ (hz i).1) (fun i ↦ (hw i).1)
  intro i hi
  apply disk_membership_constant (hconn i) r _ (hz i).2 (hw i).2
  intro v hv he
  exact hi ⟨v, subset_closure hv, he⟩

end Erdos522
