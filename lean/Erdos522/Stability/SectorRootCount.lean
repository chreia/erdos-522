/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AngularMeshPairs
import Erdos522.Stability.MeshRootCount
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Index

/-!
# Root counts in the real sectors

Doubling angles identifies the two real sectors with one short arc. Every
fiber of doubling a finite cyclic group has at most two elements. A coarse
angular mesh therefore covers the sectors with a constant times `sqrt N`
unit-circle-centered disks.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- Every fiber of multiplication by two in a finite cyclic group has at most two elements. -/
theorem card_cyclic_double_fiber_le (J : ℕ) [NeZero J] (b : ZMod J) :
    (Finset.univ.filter fun a : ZMod J => (2 : ℕ) • a = b).card ≤ 2 := by
  classical
  by_cases hb : b ∈ Set.range (nsmulAddMonoidHom (α := ZMod J) 2)
  · have heq := AddMonoidHom.card_fiber_eq_of_mem_range
      (nsmulAddMonoidHom (α := ZMod J) 2) hb (show 0 ∈ Set.range
        (nsmulAddMonoidHom (α := ZMod J) 2) from ⟨0, by simp⟩)
    change (Finset.univ.filter fun a : ZMod J => (2 : ℕ) • a = b).card =
      (Finset.univ.filter fun a : ZMod J => (2 : ℕ) • a = 0).card at heq
    rw [heq]
    exact IsAddCyclic.card_nsmul_eq_zero_le (by norm_num)
  · have hempty : (Finset.univ.filter fun a : ZMod J => (2 : ℕ) • a = b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hb ⟨a, (Finset.mem_filter.mp ha).2⟩
    rw [hempty]
    norm_num

/-- The angular mesh has at most `4Jt/π+4` columns within angular distance `t` of the real axis. -/
theorem card_cyclic_real_sectors_le (J : ℕ) [NeZero J] {t : ℝ} (ht : 0 ≤ t) :
    ((Finset.univ.filter fun j : ZMod J => realAxisAngularDistance (cyclicAngle J j) ≤ t).card : ℝ) ≤
      4 * (J : ℝ) * t / Real.pi + 4 := by
  classical
  let s := Finset.univ.filter fun j : ZMod J => realAxisAngularDistance (cyclicAngle J j) ≤ t
  let u := Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ 2 * t
  have hm : ∀ a ∈ s, (2 : ℕ) • a ∈ u := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_nsmul]
    change ‖(2 : ℕ) • cyclicAngle J a‖ / 2 ≤ t at ha'
    linarith
  have hc : s.card ≤ 2 * u.card := by
    apply Finset.card_le_mul_card_image_of_maps_to hm 2
    intro b _
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans
      (card_cyclic_double_fiber_le J b)
  have hcr : (s.card : ℝ) ≤ 2 * (u.card : ℝ) := by exact_mod_cast hc
  have hu := card_cyclicAngle_norm_le J (show 0 ≤ 2 * t by positivity)
  change (u.card : ℝ) ≤ (J : ℝ) * (2 * t) / Real.pi + 2 at hu
  exact hcr.trans ((mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- Real-sector column counts in the actual finite angular mesh. -/
theorem annular_mesh_sector_columns_le {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun i : Fin (annularAngularSamples h) =>
      realAxisAngularDistance (annularMeshAngle h i) ≤ t).card : ℝ) ≤
      4 * (annularAngularSamples h : ℝ) * t / Real.pi + 4 := by
  classical
  have : NeZero (annularAngularSamples h) := ⟨(annularAngularSamples_pos hh).ne'⟩
  have heq : (Finset.univ.filter fun i : Fin (annularAngularSamples h) =>
      realAxisAngularDistance (annularMeshAngle h i) ≤ t).card =
      (Finset.univ.filter fun i : ZMod (annularAngularSamples h) =>
      realAxisAngularDistance (cyclicAngle (annularAngularSamples h) i) ≤ t).card := by
    apply Finset.card_bijective (ZMod.finEquiv (annularAngularSamples h))
      (ZMod.finEquiv (annularAngularSamples h)).bijective
    intro i
    simp [cyclicAngle_finEquiv, annularMeshAngle]
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  rw [heq]
  exact card_cyclic_real_sectors_le _ ht

/-- The coarse mesh uses at most `40 sqrt N` columns in sectors of width `3/sqrt N`. -/
theorem coarse_real_sector_columns_le {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.univ.filter fun i : Fin (annularAngularSamples (4 / (N : ℝ))) =>
      realAxisAngularDistance (annularMeshAngle (4 / (N : ℝ)) i) ≤ 3 / Real.sqrt N).card : ℝ) ≤
      40 * Real.sqrt N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs1 : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hNr
  have hJ' : (annularAngularSamples (4 / (N : ℝ)) : ℝ) ≤ 8 * N := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * Real.pi / (4 / (N : ℝ)))).le
    have heq : 8 * Real.pi / (4 / (N : ℝ)) = 2 * Real.pi * N := by field_simp; ring
    change (⌈8 * Real.pi / (4 / (N : ℝ))⌉₊ : ℝ) ≤ _
    rw [heq] at hceil
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hN0.le
    rw [heq]
    nlinarith
  have hc := annular_mesh_sector_columns_le (show 0 < 4 / (N : ℝ) by positivity)
    (show 0 ≤ 3 / Real.sqrt N by positivity)
  apply hc.trans
  have hfirst : 4 * (annularAngularSamples (4 / (N : ℝ)) : ℝ) * (3 / Real.sqrt N) / Real.pi ≤
      32 * Real.sqrt N := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hmul := mul_le_mul_of_nonneg_right hJ' (show 0 ≤ 4 * (3 / Real.sqrt N) by positivity)
    have heq : 8 * (N : ℝ) * (4 * (3 / Real.sqrt N)) = 96 * Real.sqrt N := by
      have hs2 := Real.sq_sqrt hN0.le
      field_simp
      nlinarith
    rw [heq] at hmul
    have hpi := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (show 0 ≤ 32 * Real.sqrt N by positivity)
    nlinarith
  linarith

/-- The real-sector portion of an annulus, including its angular and radial boundaries. -/
def annularRealSectors (N : ℕ) (K : ℝ) : Set ℂ :=
  {α | |‖α‖ - 1| ≤ K / N ∧
    realAxisAngularDistance (Complex.arg α : Real.Angle) ≤ 2 / Real.sqrt N}

/-- Every point in the real sectors lies in a coarse cell whose center is on the unit circle. -/
theorem annular_real_sector_cover {N : ℕ} (hN : 2 ≤ N) {K : ℝ} {α : ℂ}
    (hα : α ∈ annularRealSectors N K) :
    ∃ i : Fin (annularAngularSamples (4 / (N : ℝ))),
      realAxisAngularDistance (annularMeshAngle (4 / (N : ℝ)) i) ≤ 3 / Real.sqrt N ∧
      α ∈ Metric.closedBall ((annularMeshAngle (4 / (N : ℝ)) i).toCircle : ℂ) ((K + 1) / N) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  obtain ⟨i, hi, hchord⟩ := exists_near_annularMeshAngle
    (show 0 < 4 / (N : ℝ) by positivity) (Complex.arg α : Real.Angle)
  have hi' : dist (Complex.arg α : Real.Angle) (annularMeshAngle (4 / (N : ℝ)) i) ≤ 1 / N := by
    convert hi using 1
    ring
  have hinv : 1 / (N : ℝ) ≤ 1 / Real.sqrt N :=
    one_div_le_one_div_of_le hs (Real.sqrt_le_self_iff.mpr (Or.inr hNr))
  refine ⟨i, ?_, ?_⟩
  · have ha := realAxisAngularDistance_le_add_dist
      (annularMeshAngle (4 / (N : ℝ)) i) (Complex.arg α : Real.Angle)
    rw [dist_comm] at ha
    have ht := hα.2
    calc
      _ ≤ realAxisAngularDistance (Complex.arg α : Real.Angle) +
          dist (Complex.arg α : Real.Angle) (annularMeshAngle (4 / (N : ℝ)) i) := ha
      _ ≤ 2 / Real.sqrt N + 1 / (N : ℝ) := add_le_add ht hi'
      _ ≤ 2 / Real.sqrt N + 1 / Real.sqrt N := add_le_add_right hinv _
      _ = 3 / Real.sqrt N := by ring
  · let θ : Real.Angle := Complex.arg α
    let c : ℂ := (annularMeshAngle (4 / (N : ℝ)) i).toCircle
    have hpolar : α = (‖α‖ : ℂ) * (θ.toCircle : ℂ) := by
      simpa only [θ, Real.Angle.toCircle_coe, Circle.coe_exp] using
        (Complex.norm_mul_exp_arg_mul_I α).symm
    have heq : α - c = ((‖α‖ - 1 : ℝ) : ℂ) * (θ.toCircle : ℂ) + ((θ.toCircle : ℂ) - c) := by
      nth_rw 1 [hpolar]
      push_cast
      ring
    have hdist : ‖α - c‖ ≤ |‖α‖ - 1| + ‖(θ.toCircle : ℂ) - c‖ := by
      rw [heq]
      convert norm_add_le _ _ using 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖α - c‖ ≤ (K + 1) / N
    have ht := hα.1
    have hchord' : ‖(θ.toCircle : ℂ) - c‖ ≤ 1 / (N : ℝ) := by
      convert hchord using 1
      ring
    have heq' : (K + 1) / (N : ℝ) = K / N + 1 / N := by ring
    rw [heq']
    exact hdist.trans (add_le_add ht hchord')

/-- A simultaneous local count gives a multiplicity-counted sector bound of `40 B sqrt N`. -/
theorem annular_real_sector_zero_count_le (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K K' B : ℝ} (hK' : K + 1 ≤ 2 * K') (hB : 0 ≤ B)
    (hlocal : ∀ c : ℂ, ‖c‖ = 1 →
      (zeroCountIn P (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B) :
    (zeroCountIn P (annularRealSectors N K) : ℝ) ≤ 40 * B * Real.sqrt N := by
  classical
  let t := Finset.univ.filter fun i : Fin (annularAngularSamples (4 / (N : ℝ))) =>
    realAxisAngularDistance (annularMeshAngle (4 / (N : ℝ)) i) ≤ 3 / Real.sqrt N
  let cells (i : Fin (annularAngularSamples (4 / (N : ℝ)))) :=
    Metric.closedBall ((annularMeshAngle (4 / (N : ℝ)) i).toCircle : ℂ) ((K + 1) / N)
  have hcover : ∀ α ∈ P.roots, α ∈ annularRealSectors N K → ∃ i ∈ t, α ∈ cells i := by
    intro α _ hα
    obtain ⟨i, hi, hc⟩ := annular_real_sector_cover hN hα
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hc⟩
  have hc := zeroCountIn_le_card_mul_of_root_cover P t (annularRealSectors N K) cells hcover
    (fun i _ => (show (zeroCountIn P (cells i) : ℝ) ≤
        zeroCountIn P (Metric.closedBall ((annularMeshAngle (4 / (N : ℝ)) i).toCircle : ℂ)
          (2 * K' / N)) from by
      exact_mod_cast zeroCountIn_mono P (Metric.closedBall_subset_closedBall
        (div_le_div_of_nonneg_right hK' (by positivity : (0 : ℝ) ≤ N)))).trans
      (hlocal _ (Circle.norm_coe _)))
  exact hc.trans ((mul_le_mul_of_nonneg_right (coarse_real_sector_columns_le hN) hB).trans_eq (by ring))

/-- Combining detection and the real-sector cover controls every annular small-derivative root. -/
theorem full_annular_small_derivative_count_le (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K K' S L B : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hKN : K + 1 ≤ (N : ℝ)) (hK' : K + 1 ≤ 2 * K')
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N))
    (hlocal : ∀ c : ℂ, ‖c‖ = 1 →
      (zeroCountIn P (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B) :
    (zeroCountIn P {α | |‖α‖ - 1| ≤ K / N ∧
      ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L} : ℝ) ≤
      (detectedAnnularMesh P N K S L).card * B + 40 * B * Real.sqrt N := by
  have hcover : {α | |‖α‖ - 1| ≤ K / N ∧
      ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L} ⊆
      annularSmallDerivativeRegion P N K L ∪ annularRealSectors N K := by
    intro α hα
    rcases le_total (2 / Real.sqrt N) (realAxisAngularDistance (Complex.arg α : Real.Angle)) with h | h
    · exact Or.inl ⟨hα.1, hα.2, h⟩
    · exact Or.inr ⟨hα.1, h⟩
  have hc : (zeroCountIn P {α | |‖α‖ - 1| ≤ K / N ∧
      ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L} : ℝ) ≤
      (zeroCountIn P (annularSmallDerivativeRegion P N K L) : ℝ) +
        zeroCountIn P (annularRealSectors N K) := by
    exact_mod_cast (zeroCountIn_mono P hcover).trans (zeroCountIn_union_le P _ _)
  exact hc.trans (add_le_add (annular_small_derivative_count_le P hN hK hS hL hKN hK' hbound hlocal)
    (annular_real_sector_zero_count_le P hN hK' hB hlocal))

end Erdos522
