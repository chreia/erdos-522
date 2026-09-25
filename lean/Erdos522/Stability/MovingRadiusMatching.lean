/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AnnularRootMatching

/-!
# Root matching for moving target radii

A matched root can change membership in two different target disks only when
the original root is near the reference circle. The relevant width is the
localization radius plus the change in target radius.
-/

noncomputable section
open Set
namespace Erdos522

attribute [local instance] Classical.propDecidable

/-- A partial matching compares two different predicates with the same
unmatched-cardinality correction as a fixed-predicate matching. -/
theorem multiset_matching_bound_two_predicates {α : Type*} (u v : Multiset α)
    (pairs : Multiset (α × α)) (p q : α → Prop)
    (hleft : pairs.map Prod.fst ≤ u) (hright : pairs.map Prod.snd ≤ v) :
    Nat.dist (v.countP q) (u.countP p) ≤
      pairs.countP (fun z => ¬ (p z.1 ↔ q z.2)) +
        (u.card - pairs.card) + (v.card - u.card) := by
  classical
  let left : α → α × Bool := fun x => (x, false)
  let right : α → α × Bool := fun x => (x, true)
  let tagged : Multiset ((α × Bool) × (α × Bool)) :=
    pairs.map (fun z => (left z.1, right z.2))
  let test : α × Bool → Prop := fun x => if x.2 then q x.1 else p x.1
  have hl : tagged.map Prod.fst ≤ u.map left := by
    simpa only [tagged, Multiset.map_map, Function.comp_def] using
      (Multiset.map_le_map (f := left) hleft)
  have hr : tagged.map Prod.snd ≤ v.map right := by
    simpa only [tagged, Multiset.map_map, Function.comp_def] using
      (Multiset.map_le_map (f := right) hright)
  have h := multiset_matching_bound (u.map left) (v.map right) tagged test hl hr
  simp only [tagged, Multiset.countP_map, Multiset.card_map] at h
  simp only [test, left, right, Bool.false_eq_true, ite_false, ite_true] at h
  simpa only [Multiset.countP_eq_card_filter] using h

/-- Distinct pairs of roots compare membership in different sets. -/
theorem finite_root_matching_bound_two_sets {ι : Type*} [Fintype ι]
    (P Q : Polynomial ℂ) (s t : Set ℂ) (z v : ι → ℂ) (cross : ι → Prop)
    (hz : Function.Injective z) (hv : Function.Injective v)
    (hzroot : ∀ i, z i ∈ P.roots) (hvroot : ∀ i, v i ∈ Q.roots)
    (hagree : ∀ i, ¬ cross i → (z i ∈ s ↔ v i ∈ t)) :
    Nat.dist (zeroCountIn Q t) (zeroCountIn P s) ≤
      (Finset.univ.filter cross).card + (P.natDegree - Fintype.card ι) +
        (Q.natDegree - P.natDegree) := by
  classical
  let pairs : Multiset (ℂ × ℂ) := Finset.univ.val.map (fun i => (z i, v i))
  have hleft : pairs.map Prod.fst ≤ P.roots := by
    simpa only [pairs, Multiset.map_map, Function.comp_def] using
      selected_roots_le P z hz hzroot
  have hright : pairs.map Prod.snd ≤ Q.roots := by
    simpa only [pairs, Multiset.map_map, Function.comp_def] using
      selected_roots_le Q v hv hvroot
  have hc : pairs.countP (fun a => ¬ (a.1 ∈ s ↔ a.2 ∈ t)) ≤
      (Finset.univ.filter cross).card := by
    simp only [pairs, Multiset.countP_map]
    apply Multiset.card_le_card
    apply Multiset.le_filter.mpr
    refine ⟨Multiset.filter_le _ _, ?_⟩
    intro i hi
    by_contra h
    exact (Multiset.mem_filter.mp hi).2 (hagree i h)
  have h := multiset_matching_bound_two_predicates P.roots Q.roots pairs
    (fun z => z ∈ s) (fun z => z ∈ t) hleft hright
  have hn : pairs.card = Fintype.card ι := by simp [pairs]
  simp only [IsAlgClosed.card_roots_eq_natDegree, hn, Multiset.countP_eq_card_filter] at h
  simp only [Multiset.countP_eq_card_filter] at hc
  change Nat.dist (zeroCountIn Q t) (zeroCountIn P s) ≤ _ at h
  omega

/-- Away from the reference band, nearby points have the same membership in
the reference and moved closed disks. -/
theorem moving_disk_membership_of_not_in_band {z v : ℂ} {r r' s w : ℝ}
    (hnear : ‖v - z‖ ≤ s) (hwidth : s + |r' - r| < w)
    (hband : ¬ (r - w < ‖z‖ ∧ ‖z‖ ≤ r + w)) :
    (‖z‖ ≤ r ↔ ‖v‖ ≤ r') := by
  have hs : 0 ≤ s := (norm_nonneg _).trans hnear
  have hw : 0 < w := (add_nonneg hs (abs_nonneg _)).trans_lt hwidth
  have hnorm := abs_le.mp ((abs_norm_sub_norm_le v z).trans hnear)
  have hrad := abs_le.mp (le_refl |r' - r|)
  by_cases hlo : ‖z‖ ≤ r - w
  · have hz : ‖z‖ ≤ r := by linarith
    have hv : ‖v‖ ≤ r' := by linarith
    exact iff_of_true hz hv
  · have hhi : r + w < ‖z‖ := lt_of_not_ge (fun hz => hband ⟨lt_of_not_ge hlo, hz⟩)
    have hz : ¬ ‖z‖ ≤ r := by linarith
    have hv : ¬ ‖v‖ ≤ r' := by linarith
    exact iff_of_false hz hv

/-- A finite root matching with displacement at most `s` controls different
target radii using one reference band. -/
theorem root_matching_moving_radius_bound {ι : Type*} [Fintype ι]
    (P Q : Polynomial ℂ) (z v : ι → ℂ) (r r' : ℝ) {s w : ℝ}
    (hz : Function.Injective z) (hv : Function.Injective v)
    (hzroot : ∀ i, z i ∈ P.roots) (hvroot : ∀ i, v i ∈ Q.roots)
    (hs : 0 ≤ s) (hnear : ∀ i, ‖v i - z i‖ ≤ s) (hwidth : s + |r' - r| < w) :
    Nat.dist (closedZeroCount Q r') (closedZeroCount P r) ≤
      closedZeroCount P (r + w) - closedZeroCount P (r - w) +
        (P.natDegree - Fintype.card ι) + (Q.natDegree - P.natDegree) := by
  classical
  let band : ℂ → Prop := fun α => r - w < ‖α‖ ∧ ‖α‖ ≤ r + w
  have hcount := Multiset.countP_le_of_le band (selected_roots_le P z hz hzroot)
  rw [Multiset.countP_map] at hcount
  have hcross : (Finset.univ.filter (fun i => band (z i))).card ≤
      zeroCountIn P {α | band α} := by
    simpa only [Multiset.countP_eq_card_filter, zeroCountIn,
      Set.mem_ofPred_eq, Finset.filter_val, Finset.card] using hcount
  have hw : 0 < w := (add_nonneg hs (abs_nonneg _)).trans_lt hwidth
  have hb := closedZeroCount_sub_eq_band P (by linarith : r - w ≤ r + w)
  change closedZeroCount P (r + w) - closedZeroCount P (r - w) =
    zeroCountIn P {α | band α} at hb
  rw [← hb] at hcross
  have h := finite_root_matching_bound_two_sets P Q {α | ‖α‖ ≤ r} {α | ‖α‖ ≤ r'} z v
    (fun i => band (z i)) hz hv hzroot hvroot
    (fun i hi => moving_disk_membership_of_not_in_band (hnear i) hwidth hi)
  change Nat.dist (closedZeroCount Q r') (closedZeroCount P r) ≤ _ at h
  simp only [band] at h hcross
  omega

/-- Regular roots in a common convex domain remain matched when the target
radius moves. Only the reference radial band incurs a crossing cost. -/
theorem regular_root_moving_radius_matching_in_set (P G : Polynomial ℂ) (A : Set ℂ)
    {D : Set ℂ} {M d₀ a w : ℝ} (r r' : ℝ)
    (ha : 0 < a) (hd : 0 < d₀) (hD : Convex ℝ D)
    (hbudget : 4 * M * a ≤ d₀ ^ 2) (hwidth : 2 * a / d₀ + |r' - r| < w)
    (hdisks : ∀ α ∈ A, Metric.closedBall α (2 * a / d₀) ⊆ D)
    (hbound : ∀ z ∈ D, ‖P.derivative.derivative.eval z‖ ≤ M)
    (hG : ∀ z ∈ D, ‖G.eval z‖ < a) :
    Nat.dist (closedZeroCount (P + G) r') (closedZeroCount P r) ≤
      closedZeroCount P (r + w) - closedZeroCount P (r - w) +
        zeroCountIn P Aᶜ + zeroCountIn P {z | z ∈ A ∧ ‖P.derivative.eval z‖ ≤ d₀} +
        ((P + G).natDegree - P.natDegree) := by
  classical
  let ι := ↥(regularRootsIn P A d₀)
  let z : ι → ℂ := Subtype.val
  have hz : Function.Injective z := Subtype.val_injective
  have hzmem (i : ι) := (mem_regularRootsIn P A d₀ i.val).mp i.property
  have hroot (i : ι) : P.eval (z i) = 0 := Polynomial.isRoot_of_mem_roots (hzmem i).1
  have hderiv (i : ι) : d₀ ≤ ‖P.derivative.eval (z i)‖ := (hzmem i).2.2
  have hlocal (i : ι) : Metric.closedBall (z i) (2 * a / d₀) ⊆ D :=
    hdisks _ (hzmem i).2.1
  have hs : 0 < 2 * a / d₀ := by positivity
  have hdisj := regular_root_family_disjoint P z hD hd hz
    (fun i => hlocal i (Metric.mem_closedBall_self hs.le)) hroot hderiv hbudget hbound
  have hQ (i : ι) : zeroCountIn (P + G) (Metric.ball (z i) (2 * a / d₀)) = 1 :=
    regular_root_perturbation_count P G ha hd (hroot i) (hderiv i) hbudget
      (fun v hv => hbound v (hlocal i hv))
      (fun v hv => hG v (hlocal i (Metric.sphere_subset_closedBall hv)))
  have hex (i : ι) : ∃ v : ℂ, v ∈ (P + G).roots ∧ v ∈ Metric.ball (z i) (2 * a / d₀) := by
    have hc : 0 < ((P + G).roots.filter (fun v => v ∈ Metric.ball (z i) (2 * a / d₀))).card := by
      change 0 < zeroCountIn (P + G) (Metric.ball (z i) (2 * a / d₀))
      rw [hQ i]
      exact Nat.zero_lt_one
    obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hc
    exact ⟨v, Multiset.mem_filter.mp hv⟩
  choose v hv using hex
  have hvinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hv i).2 (hij ▸ (hv j).2)
  have hnear (i : ι) : ‖v i - z i‖ ≤ 2 * a / d₀ := by
    exact (show ‖v i - z i‖ < 2 * a / d₀ by
      simpa only [Metric.mem_ball, dist_eq_norm] using (hv i).2).le
  have hmatch := root_matching_moving_radius_bound P (P + G) z v r r' hz hvinj
    (fun i => (hzmem i).1) (fun i => (hv i).1) hs.le hnear hwidth
  have hcard : Fintype.card ι = (regularRootsIn P A d₀).card := Fintype.card_coe _
  rw [hcard] at hmatch
  have hunselected := unselected_regular_roots_le P A hd
  omega

/-- Annular localization controls a changed target radius whenever the
localization radius plus the target drift fits inside the reference band. -/
theorem annular_root_matching_moving_radius (P G : Polynomial ℂ) {N : ℕ}
    {K M d₀ a w : ℝ} (r r' : ℝ) (ha : 0 < a) (hd : 0 < d₀)
    (hbudget : 4 * M * a ≤ d₀ ^ 2) (hsmall : 2 * a / d₀ ≤ 1 / N)
    (hwidth : 2 * a / d₀ + |r' - r| < w)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N → ‖P.derivative.derivative.eval z‖ ≤ M)
    (hG : ∀ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N → ‖G.eval z‖ < a) :
    Nat.dist (closedZeroCount (P + G) r') (closedZeroCount P r) ≤
      closedZeroCount P (r + w) - closedZeroCount P (r - w) +
        zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
        zeroCountIn P {z | |‖z‖ - 1| ≤ K / N ∧ ‖P.derivative.eval z‖ ≤ d₀} +
        ((P + G).natDegree - P.natDegree) := by
  apply regular_root_moving_radius_matching_in_set P G {z | |‖z‖ - 1| ≤ K / N}
    (D := Metric.closedBall 0 (1 + (K + 1) / N)) r r' ha hd (convex_closedBall _ _)
    hbudget hwidth
  · intro α hα z hz
    change |‖α‖ - 1| ≤ K / (N : ℝ) at hα
    have hdist : ‖z - α‖ ≤ 2 * a / d₀ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hαnorm := (abs_le.mp hα).2
    have hzα := norm_sub_norm_le z α
    have hr : 1 + (K + 1) / (N : ℝ) = 1 + K / N + 1 / N := by ring
    simp only [Metric.mem_closedBall, dist_zero_right, hr]
    linarith
  · intro z hz
    exact hbound z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  · intro z hz
    exact hG z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)

end Erdos522
