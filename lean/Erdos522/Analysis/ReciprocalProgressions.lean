/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Avoidance of reciprocal arithmetic progressions

A measurable subset of the positive real axis meets the reciprocal progression
`k/t`, with `k` a positive integer and `0 < t < τ`, on a set of parameters of
measure at most `τ²` times its own measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos522

/-- Positive integers bounded by a real number have total sum at most its square. -/
theorem sum_positive_naturals_le_sq (s : Finset ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hs : ∀ k ∈ s, 0 < k ∧ (k : ℝ) ≤ x) :
    (∑ k ∈ s, (k : ℝ)) ≤ x ^ 2 := by
  have hsubset : s ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(hs k hk).1, Nat.le_floor (hs k hk).2⟩
  have hcard : s.card ≤ ⌊x⌋₊ := by
    have h := Finset.card_le_card hsubset
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hcardReal : (s.card : ℝ) ≤ x :=
    (show (s.card : ℝ) ≤ (⌊x⌋₊ : ℝ) by exact_mod_cast hcard).trans (Nat.floor_le hx)
  calc
    _ ≤ ∑ _k ∈ s, x := Finset.sum_le_sum (fun k hk => (hs k hk).2)
    _ = s.card * x := by simp
    _ ≤ x * x := mul_le_mul_of_nonneg_right hcardReal hx
    _ = x ^ 2 := by ring

/-- The Jacobian weight for the positive-integer reciprocal progression. -/
def reciprocalProgressionDensity (τ : ℝ) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 < k ∧ (k : ℝ) / τ < x then ENNReal.ofReal ((k : ℝ) / x ^ 2) else 0

/-- Every finite sum of the reciprocal Jacobian weights is bounded by `τ²`. -/
theorem sum_reciprocalProgressionDensity_le (τ : ℝ) (hτ : 0 < τ)
    (s : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ s, reciprocalProgressionDensity τ k x) ≤ ENNReal.ofReal (τ ^ 2) := by
  classical
  let t := s.filter (fun k : ℕ => 0 < k ∧ (k : ℝ) / τ < x)
  have ht : ∀ k ∈ t, 0 < k ∧ (k : ℝ) ≤ x * τ := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    exact ⟨h.1, ((div_lt_iff₀ hτ).mp h.2).le⟩
  have hsum := sum_positive_naturals_le_sq t (mul_nonneg hx.le hτ.le) ht
  change (∑ k ∈ s, if 0 < k ∧ (k : ℝ) / τ < x then
    ENNReal.ofReal ((k : ℝ) / x ^ 2) else 0) ≤ _
  rw [← Finset.sum_filter]
  change (∑ k ∈ t, ENNReal.ofReal ((k : ℝ) / x ^ 2)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  nlinarith

/-- The full series of reciprocal Jacobian weights has the same bound. -/
theorem tsum_reciprocalProgressionDensity_le (τ : ℝ) (hτ : 0 < τ)
    {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, reciprocalProgressionDensity τ k x) ≤ ENNReal.ofReal (τ ^ 2) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s => sum_reciprocalProgressionDensity_le τ hτ s hx

/-- The reciprocal Jacobian density is measurable as a function of frequency. -/
theorem measurable_reciprocalProgressionDensity (τ : ℝ) (k : ℕ) :
    Measurable (reciprocalProgressionDensity τ k) := by
  classical
  have hset : MeasurableSet {x : ℝ | 0 < k ∧ (k : ℝ) / τ < x} := by
    by_cases hk : 0 < k
    · convert (measurableSet_Ioi (a := (k : ℝ) / τ)) using 1
      ext x
      simp only [mem_ofPred_eq, hk, true_and, mem_Ioi]
    · simp only [hk, false_and, ofPred_false, MeasurableSet.empty]
  exact Measurable.ite hset (by fun_prop) measurable_const

/-- The inversion Jacobian gives the volume of the reciprocal image of a positive set. -/
theorem volume_reciprocal_image {a : ℝ} (ha : 0 ≤ a) (G : Set ℝ)
    (hG : MeasurableSet G) (hpos : G ⊆ Ioi 0) :
    volume ((fun x : ℝ => a / x) '' G) =
      ∫⁻ x in G, ENNReal.ofReal (a / x ^ 2) := by
  have hderiv (x : ℝ) (hx : x ∈ G) :
      HasDerivWithinAt (fun y : ℝ => a / y) (-(a / x ^ 2)) G x := by
    have hx0 : x ≠ 0 := (hpos hx).ne'
    convert ((hasDerivAt_inv hx0).const_mul a).hasDerivWithinAt using 1
    simp only [div_eq_mul_inv]
    ring
  have hanti : AntitoneOn (fun x : ℝ => a / x) G := by
    intro x hx y _ hxy
    exact div_le_div_of_nonneg_left ha (hpos hx) hxy
  simpa only [neg_neg] using
    (lintegral_deriv_eq_volume_image_of_antitoneOn hG hderiv hanti).symm

/-- A single reciprocal slice has the integral of its Jacobian density. -/
theorem volume_reciprocal_slice (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (G : Set ℝ) (hG : MeasurableSet G) :
    volume ((fun x : ℝ => (k : ℝ) / x) '' (G ∩ Ioi ((k : ℝ) / τ))) =
      ∫⁻ x in G, reciprocalProgressionDensity τ k x := by
  have hpos : G ∩ Ioi ((k : ℝ) / τ) ⊆ Ioi 0 := by
    intro x hx
    exact lt_of_le_of_lt (show (0 : ℝ) ≤ (k : ℝ) / τ by positivity) hx.2
  have himage := volume_reciprocal_image (Nat.cast_nonneg k)
    (G ∩ Ioi ((k : ℝ) / τ)) (hG.inter measurableSet_Ioi) hpos
  by_cases hk : 0 < k
  · have hdensity : reciprocalProgressionDensity τ k =
        (Ioi ((k : ℝ) / τ)).indicator (fun x => ENNReal.ofReal ((k : ℝ) / x ^ 2)) := by
      ext x
      simp only [reciprocalProgressionDensity, hk, true_and, indicator, mem_Ioi]
    rw [himage, hdensity, setLIntegral_indicator measurableSet_Ioi, inter_comm]
  · have hk0 : k = 0 := by omega
    subst k
    simpa only [Nat.cast_zero, zero_div, ENNReal.ofReal_zero, lintegral_zero,
      reciprocalProgressionDensity, lt_self_iff_false, false_and, ite_false] using himage

/-- Parameters for which the reciprocal progression of positive integers meets `G`. -/
def reciprocalProgressionHits (τ : ℝ) (G : Set ℝ) : Set ℝ :=
  {t | 0 < t ∧ t < τ ∧ ∃ k : ℕ, 0 < k ∧ (k : ℝ) / t ∈ G}

/-- The reciprocal-progression hitting set has measure at most `τ² volume G`.
    The estimate already holds on the full positive interval `(0,τ)`. -/
theorem volume_reciprocalProgressionHits_le (τ : ℝ) (hτ : 0 < τ)
    (G : Set ℝ) (hG : MeasurableSet G) (hpos : G ⊆ Ioi 0) :
    volume (reciprocalProgressionHits τ G) ≤ ENNReal.ofReal (τ ^ 2) * volume G := by
  have hsubset : reciprocalProgressionHits τ G ⊆
      ⋃ k : ℕ, (fun x : ℝ => (k : ℝ) / x) '' (G ∩ Ioi ((k : ℝ) / τ)) := by
    rintro t ⟨ht0, htτ, k, hk, hkg⟩
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    refine mem_iUnion.mpr ⟨k, (k : ℝ) / t, ⟨hkg, ?_⟩, ?_⟩
    · exact div_lt_div_of_pos_left hk0 ht0 htτ
    · field_simp
  calc
    _ ≤ volume (⋃ k : ℕ, (fun x : ℝ => (k : ℝ) / x) '' (G ∩ Ioi ((k : ℝ) / τ))) :=
      measure_mono hsubset
    _ ≤ ∑' k : ℕ, volume ((fun x : ℝ => (k : ℝ) / x) '' (G ∩ Ioi ((k : ℝ) / τ))) :=
      measure_iUnion_le _
    _ = ∑' k : ℕ, ∫⁻ x in G, reciprocalProgressionDensity τ k x :=
      tsum_congr (fun k => volume_reciprocal_slice τ hτ k G hG)
    _ = ∫⁻ x in G, ∑' k : ℕ, reciprocalProgressionDensity τ k x :=
      (lintegral_tsum (fun k => (measurable_reciprocalProgressionDensity τ k).aemeasurable)).symm
    _ ≤ ∫⁻ _x in G, ENNReal.ofReal (τ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG] with x hx
      exact tsum_reciprocalProgressionDensity_le τ hτ (hpos hx)
    _ = ENNReal.ofReal (τ ^ 2) * volume G := setLIntegral_const _ _

/-- The reciprocal-progression estimate on the upper half of the time interval. -/
theorem volume_reciprocalProgressionHits_half_le (τ : ℝ) (hτ : 0 < τ)
    (G : Set ℝ) (hG : MeasurableSet G) (hpos : G ⊆ Ioi 0) :
    volume {t : ℝ | τ / 2 < t ∧ t < τ ∧ ∃ k : ℕ, 0 < k ∧ (k : ℝ) / t ∈ G} ≤
      ENNReal.ofReal (τ ^ 2) * volume G := by
  apply le_trans (measure_mono ?_) (volume_reciprocalProgressionHits_le τ hτ G hG hpos)
  rintro t ⟨ht, htτ, hk⟩
  exact ⟨by linarith, htτ, hk⟩

/-- The progression hitting set is measurable whenever the frequency set is measurable. -/
theorem measurableSet_reciprocalProgressionHits (τ : ℝ) (G : Set ℝ)
    (hG : MeasurableSet G) : MeasurableSet (reciprocalProgressionHits τ G) := by
  have heq : reciprocalProgressionHits τ G =
      Ioo 0 τ ∩ ⋃ k : ℕ, {t : ℝ | 0 < k ∧ (k : ℝ) / t ∈ G} := by
    ext t
    simp only [reciprocalProgressionHits, mem_ofPred_eq, mem_inter_iff, mem_Ioo, mem_iUnion]
    tauto
  rw [heq]
  apply measurableSet_Ioo.inter
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : 0 < k
  · convert hG.preimage (measurable_const.div measurable_id) using 1
    ext t
    simp only [mem_ofPred_eq, hk, true_and, mem_preimage]
    rfl
  · simp only [hk, false_and, ofPred_false, MeasurableSet.empty]

/-- A frequency set of measure less than `1/(2τ)` is avoided by some positive
    reciprocal progression with time parameter between `τ/2` and `τ`. -/
theorem exists_reciprocalProgression_avoiding (τ : ℝ) (hτ : 0 < τ)
    (G : Set ℝ) (hG : MeasurableSet G) (hpos : G ⊆ Ioi 0)
    (hsmall : volume G < ENNReal.ofReal (1 / (2 * τ))) :
    ∃ t ∈ Ioo (τ / 2) τ, ∀ k : ℕ, 0 < k → (k : ℝ) / t ∉ G := by
  classical
  have hmul := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hτ)) ENNReal.ofReal_ne_top hsmall
  rw [← ENNReal.ofReal_mul (sq_nonneg τ)] at hmul
  have hscale : τ ^ 2 * (1 / (2 * τ)) = τ / 2 := by field_simp
  rw [hscale] at hmul
  by_contra hnone
  push Not at hnone
  have hsubset : Ioo (τ / 2) τ ⊆ reciprocalProgressionHits τ G := by
    intro t ht
    obtain ⟨k, hk, hkg⟩ := hnone t ht
    exact ⟨by linarith [ht.1], ht.2, k, hk, hkg⟩
  have hbound := (measure_mono hsubset).trans
    (volume_reciprocalProgressionHits_le τ hτ G hG hpos)
  rw [Real.volume_Ioo, show τ - τ / 2 = τ / 2 by ring] at hbound
  exact not_lt_of_ge hbound hmul

end Erdos522
