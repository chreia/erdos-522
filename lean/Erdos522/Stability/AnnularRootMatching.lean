/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.PolynomialRouche
import Mathlib.Data.Finset.Card

/-!
# Annular root matching across polynomial perturbations

Regular roots in an annulus give disjoint localization disks. The roots not
selected are charged with their full multiplicity, while disks crossing a
target circle are charged to a radial band with a strict inner boundary.
-/

noncomputable section
open Set
namespace Erdos522

attribute [local instance] Classical.propDecidable

/-- Removing a subset subtracts its multiplicity-counted roots exactly. -/
theorem zeroCountIn_sdiff_of_subset (P : Polynomial ℂ) {s t : Set ℂ}
    (hst : s ⊆ t) : zeroCountIn P (t \ s) = zeroCountIn P t - zeroCountIn P s := by
  classical
  have h := Multiset.filter_add_not (fun z : ℂ => z ∈ s)
    (P.roots.filter (fun z => z ∈ t))
  have hs : (P.roots.filter (fun z => z ∈ t)).filter (fun z => z ∈ s) =
      P.roots.filter (fun z => z ∈ s) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z _
    exact ⟨And.left, fun hz => ⟨hz, hst hz⟩⟩
  have ht : (P.roots.filter (fun z => z ∈ t)).filter (fun z => z ∉ s) =
      P.roots.filter (fun z => z ∈ t \ s) := by
    simp only [Multiset.filter_filter, Set.mem_sdiff]
    apply Multiset.filter_congr
    intro z _
    exact and_comm
  rw [hs, ht] at h
  have hc := congrArg Multiset.card h
  rw [Multiset.card_add] at hc
  have hc' : zeroCountIn P s + zeroCountIn P (t \ s) = zeroCountIn P t := by
    simpa only [zeroCountIn, Set.mem_sdiff] using hc
  omega

/-- A difference of closed-disk counts includes the outer circle and excludes
the inner circle. -/
theorem closedZeroCount_sub_eq_band (P : Polynomial ℂ) {u v : ℝ} (huv : u ≤ v) :
    closedZeroCount P v - closedZeroCount P u =
      zeroCountIn P {z | u < ‖z‖ ∧ ‖z‖ ≤ v} := by
  have h := zeroCountIn_sdiff_of_subset P
    (s := {z | ‖z‖ ≤ u}) (t := {z | ‖z‖ ≤ v}) (fun _ hz => hz.trans huv)
  have he : ({z : ℂ | ‖z‖ ≤ v} \ {z | ‖z‖ ≤ u}) =
      {z | u < ‖z‖ ∧ ‖z‖ ≤ v} := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
    exact and_comm
  simpa only [he, closedZeroCount] using h.symm

/-- The distinct roots in a set whose derivatives meet a positive threshold. -/
def regularRootsIn (P : Polynomial ℂ) (A : Set ℂ) (d₀ : ℝ) : Finset ℂ := by
  classical
  exact P.roots.toFinset.filter (fun z => z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖)

theorem mem_regularRootsIn (P : Polynomial ℂ) (A : Set ℂ) (d₀ : ℝ) (z : ℂ) :
    z ∈ regularRootsIn P A d₀ ↔
      z ∈ P.roots ∧ z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖ := by
  classical
  simp only [regularRootsIn, Finset.mem_filter, Multiset.mem_toFinset]

/-- Every selected regular root has multiplicity one, so its finite-set
cardinality equals the original multiset count. -/
theorem regularRootsIn_card (P : Polynomial ℂ) (A : Set ℂ) {d₀ : ℝ} (hd : 0 < d₀) :
    (regularRootsIn P A d₀).card =
      zeroCountIn P {z | z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖} := by
  classical
  have hnodup : (P.roots.filter (fun z => z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖)).Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro z
    by_cases hz : z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖
    · rw [Multiset.count_filter, ite_eq_left hz]
      by_cases hroot : z ∈ P.roots
      · rw [Polynomial.count_roots, regular_root_multiplicity_one P
          (Polynomial.isRoot_of_mem_roots hroot) (norm_pos_iff.mp (hd.trans_le hz.2))]
      · simp [Multiset.count_eq_zero.mpr hroot]
    · rw [Multiset.count_filter, ite_eq_right hz]
      exact Nat.zero_le _
  rw [regularRootsIn, ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup hnodup]
  simp only [zeroCountIn, Set.mem_ofPred_eq]

/-- Unselected multiplicity is bounded by roots outside the chosen set and
roots at or below the derivative threshold within it. -/
theorem unselected_regular_roots_le (P : Polynomial ℂ) (A : Set ℂ) {d₀ : ℝ}
    (hd : 0 < d₀) :
    P.natDegree - (regularRootsIn P A d₀).card ≤
      zeroCountIn P Aᶜ + zeroCountIn P {z | z ∈ A ∧ ‖P.derivative.eval z‖ ≤ d₀} := by
  rw [regularRootsIn_card P A hd]
  have hcount := zeroCountIn_add_compl P {z | z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖}
  have hsub : {z : ℂ | z ∈ A ∧ d₀ ≤ ‖P.derivative.eval z‖}ᶜ ⊆
      Aᶜ ∪ {z | z ∈ A ∧ ‖P.derivative.eval z‖ ≤ d₀} := by
    intro z hz
    by_cases hA : z ∈ A
    · exact Or.inr ⟨hA, (lt_of_not_ge (fun h => hz ⟨hA, h⟩)).le⟩
    · exact Or.inl hA
  have hb := (zeroCountIn_mono P hsub).trans (zeroCountIn_union_le P _ _)
  omega

/-- A localization disk whose closure meets a target circle has its center
within the disk radius of that circle. -/
theorem norm_sub_radius_le_of_closure_ball_meets {α : ℂ} {s r : ℝ}
    (hcross : ∃ z ∈ closure (Metric.ball α s), ‖z‖ = r) : |‖α‖ - r| ≤ s := by
  obtain ⟨z, hz, hzr⟩ := hcross
  have hz' := Metric.closure_ball_subset_closedBall hz
  have hdist : ‖α - z‖ ≤ s := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz'
  simpa only [hzr] using (abs_norm_sub_norm_le α z).trans hdist

/-- Distinct selected roots whose localization disks cross a circle are
bounded by the multiplicity-counted radial band. The inner endpoint is strict. -/
theorem crossing_disks_le_closed_count_band {ι : Type*} [Fintype ι]
    (P : Polynomial ℂ) (z : ι → ℂ) (hz : Function.Injective z)
    (hroot : ∀ i, z i ∈ P.roots) {s w : ℝ} (hs : 0 ≤ s) (hsw : s < w) (r : ℝ) :
    (Finset.univ.filter (fun i => ∃ v ∈ closure (Metric.ball (z i) s), ‖v‖ = r)).card ≤
      closedZeroCount P (r + w) - closedZeroCount P (r - w) := by
  classical
  let cross : ι → Prop := fun i => ∃ v ∈ closure (Metric.ball (z i) s), ‖v‖ = r
  let band : ℂ → Prop := fun α => r - w < ‖α‖ ∧ ‖α‖ ≤ r + w
  have hsub : (Finset.univ.val.filter cross).map z ≤ P.roots.filter band := by
    apply Multiset.le_filter.mpr
    refine ⟨(Multiset.map_le_map (Multiset.filter_le cross _)).trans
      (selected_roots_le P z hz hroot), ?_⟩
    intro α hα
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hα
    have hnear := norm_sub_radius_le_of_closure_ball_meets (Multiset.mem_filter.mp hi).2
    have hnear' := abs_le.mp hnear
    exact ⟨by linarith, by linarith⟩
  have hc := Multiset.card_le_card hsub
  rw [Multiset.card_map] at hc
  rw [closedZeroCount_sub_eq_band P (by linarith : r - w ≤ r + w)]
  simpa only [Finset.filter_val, Finset.card, zeroCountIn, cross, band, Set.mem_ofPred_eq] using hc

/-- Regular roots in a common convex domain give a perturbation bound in
terms of a thin radial band and the two types of unselected multiplicity. -/
theorem regular_root_matching_bound_in_set (P G : Polynomial ℂ) (A : Set ℂ)
    {D : Set ℂ} {M d₀ a w : ℝ} (r : ℝ)
    (ha : 0 < a) (hd : 0 < d₀) (hD : Convex ℝ D)
    (hbudget : 4 * M * a ≤ d₀ ^ 2) (hw : 2 * a / d₀ < w)
    (hdisks : ∀ α ∈ A, Metric.closedBall α (2 * a / d₀) ⊆ D)
    (hbound : ∀ z ∈ D, ‖P.derivative.derivative.eval z‖ ≤ M)
    (hG : ∀ z ∈ D, ‖G.eval z‖ < a) :
    Nat.dist (closedZeroCount (P + G) r) (closedZeroCount P r) ≤
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
  have htail (i : ι) (v : ℂ) (hv : v ∈ Metric.sphere (z i) (2 * a / d₀)) :
      ‖G.eval v‖ < a := hG v (hlocal i (Metric.sphere_subset_closedBall hv))
  have hmatch := regular_root_family_matching P G z r ha hd hD hz hroot hderiv
    hbudget hlocal hbound htail
  have hcross := crossing_disks_le_closed_count_band P z hz (fun i => (hzmem i).1)
    (by positivity : 0 ≤ 2 * a / d₀) hw r
  have hunselected := unselected_regular_roots_le P A hd
  have hcard : Fintype.card ι = (regularRootsIn P A d₀).card := Fintype.card_coe _
  rw [hcard] at hmatch
  omega

/-- On the enlarged disk, all regular annular roots can be matched under one
perturbation budget, with multiplicities and the actual degree increment. -/
theorem annular_root_matching (P G : Polynomial ℂ) {N : ℕ}
    {K M d₀ a w : ℝ} (r : ℝ) (ha : 0 < a) (hd : 0 < d₀)
    (hbudget : 4 * M * a ≤ d₀ ^ 2) (hsmall : 2 * a / d₀ ≤ 1 / N)
    (hw : 2 * a / d₀ < w)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N → ‖P.derivative.derivative.eval z‖ ≤ M)
    (hG : ∀ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N → ‖G.eval z‖ < a) :
    Nat.dist (closedZeroCount (P + G) r) (closedZeroCount P r) ≤
      closedZeroCount P (r + w) - closedZeroCount P (r - w) +
        zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
        zeroCountIn P {z | |‖z‖ - 1| ≤ K / N ∧ ‖P.derivative.eval z‖ ≤ d₀} +
        ((P + G).natDegree - P.natDegree) := by
  apply regular_root_matching_bound_in_set P G {z | |‖z‖ - 1| ≤ K / N}
    (D := Metric.closedBall 0 (1 + (K + 1) / N)) r ha hd (convex_closedBall _ _)
    hbudget hw
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
