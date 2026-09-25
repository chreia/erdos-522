/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AnnularMesh
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod

/-!
# Close pairs in a uniform angular mesh

The cyclic group of angular columns makes difference and conjugate-sum
relations translations of one short-arc count. Radial indices are retained in
the pair count, including coincident points and all diagonal pairs.
-/

noncomputable section
open scoped BigOperators

namespace Erdos522

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The equally spaced angles, regarded as an additive map from a finite cyclic group. -/
def cyclicAngle (J : ℕ) [NeZero J] : ZMod J →+ Real.Angle :=
  (AddCircle.equivAddCircle (1 : ℝ) (2 * Real.pi) one_ne_zero (by positivity)).toAddMonoidHom.comp
    ZMod.toAddCircle

/-- The cyclic parametrization in real coordinates. -/
theorem cyclicAngle_apply (J : ℕ) [NeZero J] (j : ZMod J) :
    cyclicAngle J j = ((j.val / (J : ℝ) * (2 * Real.pi) : ℝ) : Real.Angle) := by
  change AddCircle.equivAddCircle (1 : ℝ) (2 * Real.pi) one_ne_zero (by positivity)
    (ZMod.toAddCircle j) = _
  rw [ZMod.toAddCircle_apply, AddCircle.equivAddCircle_apply_mk]
  simp only [inv_one, one_mul]
  rfl

/-- The circular distance of an equally spaced angle is the smaller cyclic index distance. -/
theorem cyclicAngle_norm (J : ℕ) [NeZero J] (j : ZMod J) :
    ‖cyclicAngle J j‖ = 2 * Real.pi * ((min j.val (J - j.val) : ℕ) / (J : ℝ)) := by
  rw [cyclicAngle_apply]
  change ‖((j.val / (J : ℝ) * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi))‖ = _
  rw [AddCircle.norm_div_natCast, Nat.mod_eq_of_lt (ZMod.val_lt j)]

/-- At most `floor b + 1` cyclic representatives have value at most `b`. -/
theorem card_cyclic_val_le (J : ℕ) [NeZero J] {b : ℝ} (hb : 0 ≤ b) :
    ((Finset.univ.filter fun j : ZMod J => (j.val : ℝ) ≤ b).card : ℝ) ≤ b + 1 := by
  classical
  have hc : (Finset.univ.filter fun j : ZMod J => (j.val : ℝ) ≤ b).card ≤
      (Finset.range (⌊b⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j : ZMod J => j.val)
    · intro j hj
      have hjb : (j.val : ℝ) ≤ b := (Finset.mem_filter.mp hj).2
      have hjf : j.val ≤ ⌊b⌋₊ := (Nat.le_floor_iff hb).mpr hjb
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjf)
    · intro j _ k _ hjk
      exact ZMod.val_injective J hjk
  have hcr : ((Finset.univ.filter fun j : ZMod J => (j.val : ℝ) ≤ b).card : ℝ) ≤
      (⌊b⌋₊ : ℝ) + 1 := by exact_mod_cast (by simpa only [Finset.card_range] using hc)
  exact hcr.trans (add_le_add (Nat.floor_le hb) le_rfl)

/-- The representatives close to the other endpoint have the same cardinality bound. -/
theorem card_cyclic_sub_val_le (J : ℕ) [NeZero J] {b : ℝ} (hb : 0 ≤ b) :
    ((Finset.univ.filter fun j : ZMod J => ((J - j.val : ℕ) : ℝ) ≤ b).card : ℝ) ≤ b + 1 := by
  classical
  have hc : (Finset.univ.filter fun j : ZMod J => ((J - j.val : ℕ) : ℝ) ≤ b).card ≤
      (Finset.range (⌊b⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j : ZMod J => J - j.val)
    · intro j hj
      have hjb : ((J - j.val : ℕ) : ℝ) ≤ b := (Finset.mem_filter.mp hj).2
      have hjf : J - j.val ≤ ⌊b⌋₊ := (Nat.le_floor_iff hb).mpr hjb
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjf)
    · intro j _ k _ hjk
      apply ZMod.val_injective J
      have hj := ZMod.val_lt j
      have hk := ZMod.val_lt k
      change J - j.val = J - k.val at hjk
      omega
  have hcr : ((Finset.univ.filter fun j : ZMod J => ((J - j.val : ℕ) : ℝ) ≤ b).card : ℝ) ≤
      (⌊b⌋₊ : ℝ) + 1 := by exact_mod_cast (by simpa only [Finset.card_range] using hc)
  exact hcr.trans (add_le_add (Nat.floor_le hb) le_rfl)

/-- An arc about zero contains at most `J δ/π + 2` columns, with endpoints included. -/
theorem card_cyclicAngle_norm_le (J : ℕ) [NeZero J] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      (J : ℝ) * δ / Real.pi + 2 := by
  classical
  have hJ : (0 : ℝ) < J := by exact_mod_cast (NeZero.pos J)
  let b := δ * J / (2 * Real.pi)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsub : (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ δ) ⊆
      (Finset.univ.filter fun j : ZMod J => (j.val : ℝ) ≤ b) ∪
      (Finset.univ.filter fun j : ZMod J => ((J - j.val : ℕ) : ℝ) ≤ b) := by
    intro j hj
    have hjnorm := (Finset.mem_filter.mp hj).2
    rw [cyclicAngle_norm] at hjnorm
    have hmin : ((min j.val (J - j.val) : ℕ) : ℝ) ≤ b := by
      dsimp [b]
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have hscaled := mul_le_mul_of_nonneg_right hjnorm hJ.le
      have heq : (2 * Real.pi * ((min j.val (J - j.val) : ℕ) / (J : ℝ))) * J =
          ((min j.val (J - j.val) : ℕ) : ℝ) * (2 * Real.pi) := by field_simp
      rwa [heq] at hscaled
    rw [Nat.cast_min] at hmin
    rcases min_le_iff.mp hmin with hjlo | hjhi
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlo⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjhi⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcr : ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      ((Finset.univ.filter fun j : ZMod J => (j.val : ℝ) ≤ b).card : ℝ) +
      ((Finset.univ.filter fun j : ZMod J => ((J - j.val : ℕ) : ℝ) ≤ b).card : ℝ) := by exact_mod_cast hc
  have h₁ := card_cyclic_val_le J hb
  have h₂ := card_cyclic_sub_val_le J hb
  have heq : 2 * (b + 1) = (J : ℝ) * δ / Real.pi + 2 := by dsimp [b]; ring
  linarith

/-- Translation and reflection give the same short-arc bound about every grid angle. -/
theorem card_cyclicAngle_difference_le (J : ℕ) [NeZero J] {δ : ℝ} (hδ : 0 ≤ δ) (i : ZMod J) :
    ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      (J : ℝ) * δ / Real.pi + 2 := by
  classical
  have heq : (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ).card =
      (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ δ).card := by
    apply Finset.card_bijective (Equiv.subLeft i) (Equiv.subLeft i).bijective
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subLeft_apply, map_sub]
  rw [heq]
  exact card_cyclicAngle_norm_le J hδ

/-- The conjugate angular diagonal is another translate of the same short arc. -/
theorem card_cyclicAngle_sum_le (J : ℕ) [NeZero J] {δ : ℝ} (hδ : 0 ≤ δ) (i : ZMod J) :
    ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      (J : ℝ) * δ / Real.pi + 2 := by
  classical
  have heq : (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ).card =
      (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J j‖ ≤ δ).card := by
    apply Finset.card_bijective (Equiv.addLeft i) (Equiv.addLeft i).bijective
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addLeft, map_add]
  rw [heq]
  exact card_cyclicAngle_norm_le J hδ

/-- Counting ordered pairs by their fibers preserves the number of source indices. -/
theorem card_pairs_le_of_fibers {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) [DecidablePred fun ab : α × β => p ab.1 ab.2]
    [∀ a, DecidablePred (p a)] {B : ℝ}
    (h : ∀ a, ((Finset.univ.filter (p a)).card : ℝ) ≤ B) :
    ((Finset.univ.filter fun ab : α × β => p ab.1 ab.2).card : ℝ) ≤ (Fintype.card α : ℝ) * B := by
  have heq : (Finset.univ.filter fun ab : α × β => p ab.1 ab.2).card =
      ∑ a, (Finset.univ.filter (p a)).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [heq, Nat.cast_sum]
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => h a)

/-- The two angular diagonals cost at most `2Jδ/π+4` columns in each row. -/
theorem card_cyclicAngle_close_le (J : ℕ) [NeZero J] {δ : ℝ} (hδ : 0 ≤ δ) (i : ZMod J) :
    ((Finset.univ.filter fun j : ZMod J =>
      ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ ∨ ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      2 * (J : ℝ) * δ / Real.pi + 4 := by
  classical
  have heq : (Finset.univ.filter fun j : ZMod J =>
      ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ ∨ ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ) =
      (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ) ∪
      (Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ) := by ext j; simp
  rw [heq]
  have hc : ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i - cyclicAngle J j‖ ≤ δ).card : ℝ) +
      ((Finset.univ.filter fun j : ZMod J => ‖cyclicAngle J i + cyclicAngle J j‖ ≤ δ).card : ℝ) ≤
      2 * (J : ℝ) * δ / Real.pi + 4 := by
    have h₁ := card_cyclicAngle_difference_le J hδ i
    have h₂ := card_cyclicAngle_sum_le J hδ i
    convert add_le_add h₁ h₂ using 1
    ring
  exact le_trans (by exact_mod_cast Finset.card_union_le _ _) hc

/-- Radial rows multiply the angular pair count, including all coincident indices. -/
theorem card_radial_cyclic_pairs_le (q J : ℕ) [NeZero J] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Finset.univ.filter fun p : (Fin q × ZMod J) × (Fin q × ZMod J) =>
      ‖cyclicAngle J p.1.2 - cyclicAngle J p.2.2‖ ≤ δ ∨
      ‖cyclicAngle J p.1.2 + cyclicAngle J p.2.2‖ ≤ δ).card : ℝ) ≤
      ((q : ℝ) * J) ^ 2 * (2 * δ / Real.pi + 4 / J) := by
  classical
  have hJ : (0 : ℝ) < J := by exact_mod_cast (NeZero.pos J)
  have hf (i : Fin q × ZMod J) :
      ((Finset.univ.filter fun j : Fin q × ZMod J =>
        ‖cyclicAngle J i.2 - cyclicAngle J j.2‖ ≤ δ ∨
        ‖cyclicAngle J i.2 + cyclicAngle J j.2‖ ≤ δ).card : ℝ) ≤
        (q : ℝ) * (2 * (J : ℝ) * δ / Real.pi + 4) := by
    simpa only [Fintype.card_fin] using card_pairs_le_of_fibers
      (fun (_ : Fin q) (j : ZMod J) =>
        ‖cyclicAngle J i.2 - cyclicAngle J j‖ ≤ δ ∨ ‖cyclicAngle J i.2 + cyclicAngle J j‖ ≤ δ)
      (fun _ => card_cyclicAngle_close_le J hδ i.2)
  have h := card_pairs_le_of_fibers (fun (i j : Fin q × ZMod J) =>
    ‖cyclicAngle J i.2 - cyclicAngle J j.2‖ ≤ δ ∨ ‖cyclicAngle J i.2 + cyclicAngle J j.2‖ ≤ δ) hf
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul] at h
  apply h.trans_eq
  field_simp

/-- The cyclic-group parametrization agrees with the finite angular mesh. -/
theorem cyclicAngle_finEquiv (J : ℕ) [NeZero J] (i : Fin J) :
    cyclicAngle J (ZMod.finEquiv J i) = ((2 * Real.pi * i.val / J : ℝ) : Real.Angle) := by
  have hv : (ZMod.finEquiv J i).val = i.val := by
    cases J with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [cyclicAngle_apply, hv]
  congr 1
  ring

/-- The exact mesh has a positive number of angular columns. -/
theorem annularAngularSamples_pos {h : ℝ} (hh : 0 < h) : 0 < annularAngularSamples h := by
  exact Nat.ceil_pos.mpr (by positivity)

/-- Close ordinary or conjugate angular pairs in the actual annular mesh. -/
theorem annular_mesh_close_pairs_le {N : ℕ} {K h δ : ℝ} (hh : 0 < h) (hδ : 0 ≤ δ) :
    ((Finset.univ.filter fun p : AnnularMeshIndex N K h × AnnularMeshIndex N K h =>
      ‖annularMeshAngle h p.1.2 - annularMeshAngle h p.2.2‖ ≤ δ ∨
      ‖annularMeshAngle h p.1.2 + annularMeshAngle h p.2.2‖ ≤ δ).card : ℝ) ≤
      (Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 *
        (2 * δ / Real.pi + 4 / annularAngularSamples h) := by
  classical
  let q := annularRadialIntervals N K h + 1
  let J := annularAngularSamples h
  have : NeZero J := ⟨(annularAngularSamples_pos hh).ne'⟩
  let e : AnnularMeshIndex N K h ≃ Fin q × ZMod J :=
    Equiv.prodCongr (Equiv.refl _) (ZMod.finEquiv J).toEquiv
  have he (i : AnnularMeshIndex N K h) : cyclicAngle J (e i).2 = annularMeshAngle h i.2 := by
    exact cyclicAngle_finEquiv J i.2
  have hcard : (Finset.univ.filter fun p : AnnularMeshIndex N K h × AnnularMeshIndex N K h =>
      ‖annularMeshAngle h p.1.2 - annularMeshAngle h p.2.2‖ ≤ δ ∨
      ‖annularMeshAngle h p.1.2 + annularMeshAngle h p.2.2‖ ≤ δ).card =
      (Finset.univ.filter fun p : (Fin q × ZMod J) × (Fin q × ZMod J) =>
      ‖cyclicAngle J p.1.2 - cyclicAngle J p.2.2‖ ≤ δ ∨
      ‖cyclicAngle J p.1.2 + cyclicAngle J p.2.2‖ ≤ δ).card := by
    apply Finset.card_bijective (Equiv.prodCongr e e) (Equiv.prodCongr e e).bijective
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, he]
  rw [hcard]
  simpa only [AnnularMeshIndex, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
    card_radial_cyclic_pairs_le q J hδ

/-- The derivative mesh has at least `N` angular columns. -/
theorem degree_le_derivative_mesh_columns {N : ℕ} (hN : 2 ≤ N) {S L : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) :
    (N : ℝ) ≤ annularAngularSamples (derivativeMeshSpacing N S L) := by
  obtain ⟨hh, hhN⟩ := derivativeMeshSpacing_le_inv_degree hN hS hL
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hNh : (N : ℝ) * derivativeMeshSpacing N S L ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left hhN hNr.le
    simpa only [mul_one_div_cancel hNr.ne'] using ht
  have hceil := Nat.le_ceil (8 * Real.pi / derivativeMeshSpacing N S L)
  have hscaled := (div_le_iff₀ hh).mp hceil
  apply (le_of_mul_le_mul_right (show (N : ℝ) * derivativeMeshSpacing N S L ≤
      (annularAngularSamples (derivativeMeshSpacing N S L) : ℝ) * derivativeMeshSpacing N S L from
    hNh.trans ((by nlinarith [Real.pi_gt_three] : (1 : ℝ) ≤ 8 * Real.pi).trans hscaled)) hh)

/-- At separation scale `N⁻¹/²`, at most `5 M²/√N` ordered mesh pairs are exceptional. -/
theorem derivative_mesh_close_pairs_le {N : ℕ} (hN : 2 ≤ N) {K S L : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) :
    ((Finset.univ.filter fun p :
      AnnularMeshIndex N K (derivativeMeshSpacing N S L) ×
        AnnularMeshIndex N K (derivativeMeshSpacing N S L) =>
      ‖annularMeshAngle (derivativeMeshSpacing N S L) p.1.2 -
        annularMeshAngle (derivativeMeshSpacing N S L) p.2.2‖ ≤ 1 / Real.sqrt N ∨
      ‖annularMeshAngle (derivativeMeshSpacing N S L) p.1.2 +
        annularMeshAngle (derivativeMeshSpacing N S L) p.2.2‖ ≤ 1 / Real.sqrt N).card : ℝ) ≤
      5 * (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ^ 2 /
        Real.sqrt N := by
  obtain ⟨hh, _⟩ := derivativeMeshSpacing_le_inv_degree hN hS hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hcols := degree_le_derivative_mesh_columns hN hS hL
  have hsc : Real.sqrt N ≤ annularAngularSamples (derivativeMeshSpacing N S L) :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hNr)).trans hcols
  have hinv := one_div_le_one_div_of_le hsqrt hsc
  have hpi : 2 / Real.pi ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have hfactor : 2 * (1 / Real.sqrt N) / Real.pi +
      4 / annularAngularSamples (derivativeMeshSpacing N S L) ≤ 5 / Real.sqrt N := by
    have ht := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 1 / Real.sqrt N by positivity)
    convert add_le_add ht (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)) using 1 <;> ring
  have hc := annular_mesh_close_pairs_le (N := N) (K := K) hh
    (show 0 ≤ 1 / Real.sqrt N by positivity)
  exact hc.trans ((mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)).trans_eq (by ring))

end Erdos522
