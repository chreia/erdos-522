/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AnnularRootMatching

/-!
# Zeros in sublevel components crossing a circle

A regular root belongs to a small connected sublevel component. If that
component meets a prescribed circle, the root lies in a thin radial band.
Counting the remaining roots with their original multiplicities gives a
bound by the band, small-derivative roots, and roots outside the annulus.
-/

noncomputable section
open Set
namespace Erdos522

/-- Points whose connected polynomial sublevel component meets a circle. -/
def sublevelCrossingSet (P : Polynomial ℂ) (a r : ℝ) : Set ℂ :=
  {α | ∃ z ∈ connectedComponentIn {w | ‖P.eval w‖ < a} α, ‖z‖ = r}

/-- Roots in sublevel components meeting the circle of radius `r`, counted
with their algebraic multiplicities. The zero polynomial has count zero. -/
def sublevelComponentZeroCount (P : Polynomial ℂ) (a r : ℝ) : ℕ :=
  zeroCountIn P (sublevelCrossingSet P a r)

@[simp]
theorem sublevelComponentZeroCount_zero (a r : ℝ) :
    sublevelComponentZeroCount 0 a r = 0 := zeroCountIn_zero _

/-- Increasing the sublevel threshold preserves every crossing component. -/
theorem sublevelCrossingSet_mono (P : Polynomial ℂ) {a b r : ℝ} (hab : a ≤ b) :
    sublevelCrossingSet P a r ⊆ sublevelCrossingSet P b r := by
  intro α hα
  obtain ⟨z, hz, hzr⟩ := hα
  exact ⟨z, connectedComponentIn_mono α (fun w hw => lt_of_lt_of_le hw hab) hz, hzr⟩

/-- The multiplicity-counted crossing count is monotone in the level. -/
theorem sublevelComponentZeroCount_mono (P : Polynomial ℂ) {a b r : ℝ} (hab : a ≤ b) :
    sublevelComponentZeroCount P a r ≤ sublevelComponentZeroCount P b r :=
  zeroCountIn_mono P (sublevelCrossingSet_mono P hab)

/-- A containment checked only on roots suffices for multiplicity-counted bounds. -/
theorem zeroCountIn_le_of_root_imp (P : Polynomial ℂ) {s t : Set ℂ}
    (h : ∀ z ∈ P.roots, z ∈ s → z ∈ t) : zeroCountIn P s ≤ zeroCountIn P t := by
  classical
  apply Multiset.card_le_card
  apply Multiset.le_filter.mpr
  refine ⟨Multiset.filter_le _ _, ?_⟩
  intro z hz
  obtain ⟨hzroot, hzs⟩ := Multiset.mem_filter.mp hz
  exact h z hzroot hzs

/-- A crossing sublevel component contained in an open disk has its center
strictly within that disk radius of the target circle. -/
theorem norm_sub_radius_lt_of_sublevel_crossing {P : Polynomial ℂ} {α : ℂ} {a r s : ℝ}
    (hcross : α ∈ sublevelCrossingSet P a r)
    (hlocal : connectedComponentIn {z | ‖P.eval z‖ < a} α ⊆ Metric.ball α s) :
    |‖α‖ - r| < s := by
  obtain ⟨z, hz, hzr⟩ := hcross
  have hdist : ‖α - z‖ < s := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlocal hz
  simpa only [hzr] using (abs_norm_sub_norm_le α z).trans_lt hdist

/-- Localization of regular roots bounds all crossing multiplicities. The
inner endpoint of the radial band is strict and the outer endpoint is closed. -/
theorem sublevelComponentZeroCount_le_of_localization
    (P : Polynomial ℂ) (A : Set ℂ) {a r r₀ s w d₀ : ℝ}
    (hs : 0 ≤ s) (hwindow : s + |r - r₀| < w)
    (hlocal : ∀ α ∈ P.roots, α ∈ A → d₀ ≤ ‖P.derivative.eval α‖ →
      connectedComponentIn {z | ‖P.eval z‖ < a} α ⊆ Metric.ball α s) :
    sublevelComponentZeroCount P a r ≤
      (closedZeroCount P (r₀ + w) - closedZeroCount P (r₀ - w)) +
        zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ < d₀} + zeroCountIn P Aᶜ := by
  have hw : 0 < w := lt_of_le_of_lt (add_nonneg hs (abs_nonneg _)) hwindow
  have hsub : ∀ α ∈ P.roots, α ∈ sublevelCrossingSet P a r →
      α ∈ ({z | r₀ - w < ‖z‖ ∧ ‖z‖ ≤ r₀ + w} ∪
        {z | z ∈ A ∧ ‖P.derivative.eval z‖ < d₀}) ∪ Aᶜ := by
    intro α hα hcross
    by_cases hA : α ∈ A
    · by_cases hderiv : d₀ ≤ ‖P.derivative.eval α‖
      · left
        left
        have hdist := norm_sub_radius_lt_of_sublevel_crossing hcross (hlocal α hα hA hderiv)
        have hband : |‖α‖ - r₀| < w :=
          (abs_sub_le ‖α‖ r r₀).trans_lt
            ((add_lt_add_of_lt_of_le hdist le_rfl).trans hwindow)
        obtain ⟨hl, hu⟩ := abs_lt.mp hband
        constructor <;> linarith
      · exact Or.inl (Or.inr ⟨hA, lt_of_not_ge hderiv⟩)
    · exact Or.inr hA
  have hcount := (zeroCountIn_le_of_root_imp P hsub).trans
    (zeroCountIn_union_le P _ _)
  have hinner := zeroCountIn_union_le P
    {z | r₀ - w < ‖z‖ ∧ ‖z‖ ≤ r₀ + w}
    {z | z ∈ A ∧ ‖P.derivative.eval z‖ < d₀}
  rw [closedZeroCount_sub_eq_band P (by linarith : r₀ - w ≤ r₀ + w)]
  exact hcount.trans (Nat.add_le_add_right hinner _)

/-- The same bound permits a closed small-derivative threshold. -/
theorem sublevelComponentZeroCount_le_of_localization_le
    (P : Polynomial ℂ) (A : Set ℂ) {a r r₀ s w d₀ : ℝ}
    (hs : 0 ≤ s) (hwindow : s + |r - r₀| < w)
    (hlocal : ∀ α ∈ P.roots, α ∈ A → d₀ ≤ ‖P.derivative.eval α‖ →
      connectedComponentIn {z | ‖P.eval z‖ < a} α ⊆ Metric.ball α s) :
    sublevelComponentZeroCount P a r ≤
      (closedZeroCount P (r₀ + w) - closedZeroCount P (r₀ - w)) +
        zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ ≤ d₀} + zeroCountIn P Aᶜ := by
  apply (sublevelComponentZeroCount_le_of_localization P A hs hwindow hlocal).trans
  have hbad : zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ < d₀} ≤
      zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ ≤ d₀} :=
    zeroCountIn_mono P (fun α hα => ⟨hα.1, hα.2.le⟩)
  exact Nat.add_le_add_right (Nat.add_le_add_left hbad _) _

/-- A Taylor bound at the regular roots supplies the required sublevel localization. -/
theorem sublevelComponentZeroCount_le
    (P : Polynomial ℂ) (A : Set ℂ) {a r r₀ w M d₀ : ℝ}
    (ha : 0 < a) (hd : 0 < d₀) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hwindow : 2 * a / d₀ + |r - r₀| < w)
    (hbound : ∀ α ∈ P.roots, α ∈ A → d₀ ≤ ‖P.derivative.eval α‖ →
      ∀ z ∈ Metric.closedBall α (2 * a / d₀), ‖P.derivative.derivative.eval z‖ ≤ M) :
    sublevelComponentZeroCount P a r ≤
      (closedZeroCount P (r₀ + w) - closedZeroCount P (r₀ - w)) +
        zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ < d₀} + zeroCountIn P Aᶜ := by
  apply sublevelComponentZeroCount_le_of_localization P A (by positivity) hwindow
  intro α hα hA hderiv
  exact regular_root_sublevel_component_subset_ball P ha hd
    (Polynomial.isRoot_of_mem_roots hα) hderiv hbudget (hbound α hα hA hderiv)

/-- The Taylor form with the closed small-derivative convention used by annular counts. -/
theorem sublevelComponentZeroCount_le_closed_threshold
    (P : Polynomial ℂ) (A : Set ℂ) {a r r₀ w M d₀ : ℝ}
    (ha : 0 < a) (hd : 0 < d₀) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hwindow : 2 * a / d₀ + |r - r₀| < w)
    (hbound : ∀ α ∈ P.roots, α ∈ A → d₀ ≤ ‖P.derivative.eval α‖ →
      ∀ z ∈ Metric.closedBall α (2 * a / d₀), ‖P.derivative.derivative.eval z‖ ≤ M) :
    sublevelComponentZeroCount P a r ≤
      (closedZeroCount P (r₀ + w) - closedZeroCount P (r₀ - w)) +
        zeroCountIn P {α | α ∈ A ∧ ‖P.derivative.eval α‖ ≤ d₀} + zeroCountIn P Aᶜ := by
  apply sublevelComponentZeroCount_le_of_localization_le P A (by positivity) hwindow
  intro α hα hA hderiv
  exact regular_root_sublevel_component_subset_ball P ha hd
    (Polynomial.isRoot_of_mem_roots hα) hderiv hbudget (hbound α hα hA hderiv)

end Erdos522
