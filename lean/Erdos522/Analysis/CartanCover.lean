/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Cartan covers on the real line

A finite family of complex points admits a real exceptional set of controlled
length outside which no collection of points can be too close to the same
real point. Labels retain repetitions. Vitali selection provides disjoint
intervals, and disjointness charges each label at most once.
-/

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace Erdos522

/-- Pairwise disjoint collections of labels use at most the available labels. -/
theorem sum_card_le_of_pairwiseDisjoint {N : ℕ} (s : Finset (Finset (Fin N)))
    (hdisj : (s : Set (Finset (Fin N))).PairwiseDisjoint id) :
    ∑ t ∈ s, t.card ≤ N := by
  change (∑ t ∈ s, (id t).card) ≤ N
  rw [← Finset.card_biUnion hdisj]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

/-- A complex disk cuts the real line inside the interval with the same radius
and the real part of its center. -/
theorem real_distance_re_le_complex_distance (x : ℝ) (z : ℂ) :
    dist x z.re ≤ ‖(x : ℂ) - z‖ := by
  simpa only [Real.dist_eq, Complex.sub_re, Complex.ofReal_re] using
    Complex.abs_re_le_norm ((x : ℂ) - z)

/-- Given `N` labelled complex points and `h > 0`, there are at most `N`
closed intervals with sum of radii at most `5h/2`. Outside their union, every
nonempty collection of `j` labels has a point at distance greater than
`hj/(4N)`. -/
theorem exists_finite_cartan_cover {N : ℕ} (hN : 0 < N) (w : Fin N → ℂ)
    {h : ℝ} (hh : 0 < h) :
    ∃ (u : Finset (Finset (Fin N))) (c r : Finset (Fin N) → ℝ),
      u.card ≤ N ∧ (∀ s ∈ u, 0 < r s) ∧ (∑ s ∈ u, r s) ≤ 5 * h / 2 ∧
      ∀ x : ℝ, x ∉ ⋃ s ∈ u, closedBall (c s) (r s) →
        ∀ s : Finset (Fin N), s.Nonempty →
          ∃ i ∈ s, h * s.card / (4 * N) < ‖(x : ℂ) - w i‖ := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let radius (s : Finset (Fin N)) : ℝ := h * s.card / (4 * N)
  let good (s : Finset (Fin N)) : Prop :=
    s.Nonempty ∧ ∃ x : ℝ, ∀ i ∈ s, ‖(x : ℂ) - w i‖ ≤ radius s
  let center (s : Finset (Fin N)) : ℝ :=
    if hs : good s then Classical.choose hs.2 else 0
  have hcenter (s : Finset (Fin N)) (hs : good s) :
      ∀ i ∈ s, ‖(center s : ℂ) - w i‖ ≤ radius s := by
    simpa only [center, dite_eq_left hs] using Classical.choose_spec hs.2
  have hrnonneg (s : Finset (Fin N)) : 0 ≤ radius s := by dsimp [radius]; positivity
  have hrpos (s : Finset (Fin N)) (hs : good s) : 0 < radius s := by
    have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.1.card_pos
    dsimp [radius]
    positivity
  have hrupper (s : Finset (Fin N)) : 2 * radius s ≤ h / 2 := by
    have hc : (s.card : ℝ) ≤ N := by
      exact_mod_cast (show s.card ≤ N by simpa using Finset.card_le_univ s)
    dsimp [radius]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hden : 0 < (4 : ℝ) * N := by positivity
    have hb := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hh.le)
      hden.le)
    have heq : h * (N : ℝ) / (4 * N) = h / 4 := by field_simp
    rw [heq] at hb
    linarith
  obtain ⟨v, hv, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      {s | good s} center (fun s => 2 * radius s) (h / 2)
      (fun s _ => hrupper s) 5 (by norm_num)
  let u := v.toFinite.toFinset
  have hu (s : Finset (Fin N)) : s ∈ u ↔ s ∈ v := Set.Finite.mem_toFinset _
  have hlabel (s : Finset (Fin N)) (hs : good s) {i : Fin N} (hi : i ∈ s) :
      (w i).re ∈ closedBall (center s) (2 * radius s) := by
    rw [mem_closedBall, dist_comm]
    exact ((real_distance_re_le_complex_distance _ _).trans (hcenter s hs i hi)).trans
      (by linarith [hrnonneg s])
  have hlabels : (u : Set (Finset (Fin N))).PairwiseDisjoint id := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro i his hit
    have hsv := (hu s).mp hs
    have htv := (hu t).mp ht
    exact Set.disjoint_left.mp (hdisj hsv htv hst)
      (hlabel s (hv hsv) his) (hlabel t (hv htv) hit)
  have hsum := sum_card_le_of_pairwiseDisjoint u hlabels
  have hcard : u.card ≤ N := by
    calc
      u.card = ∑ _s ∈ u, 1 := by simp
      _ ≤ ∑ s ∈ u, s.card := Finset.sum_le_sum fun s hs =>
        Finset.one_le_card.mpr (hv ((hu s).mp hs)).1
      _ ≤ N := hsum
  refine ⟨u, center, fun s => 10 * radius s, hcard, ?_, ?_, ?_⟩
  · intro s hs
    exact mul_pos (by norm_num) (hrpos s (hv ((hu s).mp hs)))
  · have hsumR : (∑ s ∈ u, (s.card : ℝ)) ≤ N := by exact_mod_cast hsum
    calc
      (∑ s ∈ u, 10 * radius s) = (10 * h / (4 * N)) * ∑ s ∈ u, (s.card : ℝ) := by
        simp only [radius, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ ≤ (10 * h / (4 * N)) * N :=
        mul_le_mul_of_nonneg_left hsumR (by positivity)
      _ = 5 * h / 2 := by field_simp; ring
  · intro x hx s hs
    by_contra! hsmall
    have hsg : good s := ⟨hs, x, hsmall⟩
    obtain ⟨i, hi⟩ := hs
    have hxc : dist x (center s) ≤ 2 * radius s := by
      calc
        dist x (center s) ≤ dist x (w i).re + dist (w i).re (center s) := dist_triangle _ _ _
        _ ≤ radius s + radius s := add_le_add
          ((real_distance_re_le_complex_distance _ _).trans (hsmall i hi))
          (by rw [dist_comm]; exact
            (real_distance_re_le_complex_distance _ _).trans (hcenter s hsg i hi))
        _ = 2 * radius s := by ring
    obtain ⟨t, ht, hsub⟩ := hcover s hsg
    have hxt := hsub (show x ∈ closedBall (center s) (2 * radius s) from hxc)
    have hxt' : x ∈ closedBall (center t) (10 * radius t) := by
      simpa only [show (5 : ℝ) * (2 * radius t) = 10 * radius t by ring] using hxt
    exact hx (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨(hu t).mpr ht, hxt'⟩⟩)

/-- The exceptional intervals in a finite Cartan cover have total length at
most `5h`. -/
theorem volume_finite_cartan_cover_le {ι : Type*} (u : Finset ι) (c r : ι → ℝ)
    {h : ℝ} (hr : ∀ s ∈ u, 0 ≤ r s) (hsum : (∑ s ∈ u, r s) ≤ 5 * h / 2) :
    volume.real (⋃ s ∈ u, closedBall (c s) (r s)) ≤ 5 * h := by
  calc
    _ ≤ ∑ s ∈ u, volume.real (closedBall (c s) (r s)) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ s ∈ u, 2 * r s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [measureReal_def, Real.volume_closedBall,
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hr s hs))]
    _ = 2 * ∑ s ∈ u, r s := (Finset.mul_sum ..).symm
    _ ≤ 5 * h := by linarith

end Erdos522
