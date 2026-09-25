/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PolynomialArcRemez
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Quantitative angular separation

Chord separation on the unit circle controls distance to the nearest integer.
The resulting short intervals give explicit bounds for near-resonant times.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522

/-- The character `exp(2π i x)`, written through the normalized additive circle. -/
def angularCharacter (x : ℝ) : ℂ := fourier 1 (x : AddCircle (1 : ℝ))

theorem angularCharacter_eq (x : ℝ) :
    angularCharacter x = unitCirclePoint (2 * Real.pi * x) := by
  rw [angularCharacter, fourier_coe_apply]
  unfold unitCirclePoint
  congr 1
  push_cast
  ring

/-- Integer translation leaves the angular character unchanged. -/
theorem angularCharacter_sub_int (x : ℝ) (k : ℤ) :
    angularCharacter (x - k) = angularCharacter x := by
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
  simp only [angularCharacter, AddCircle.coe_sub, hk, sub_zero]

/-- Chord distance dominates four times normalized geodesic distance. -/
theorem four_mul_abs_sub_round_le_chord (x : ℝ) :
    4 * |x - round x| ≤ ‖angularCharacter x - 1‖ := by
  have h := angular_separation_le_chord (u := 2 * Real.pi * (x - round x)) (v := 0) (by
    rw [sub_zero, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hr := abs_sub_round x
    nlinarith [Real.pi_pos])
  have hc : unitCirclePoint 0 = 1 := by simp [unitCirclePoint]
  rw [hc, ← angularCharacter_eq, angularCharacter_sub_int, sub_zero,
    abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h
  have heq : (2 / Real.pi) * (2 * Real.pi * |x - round x|) = 4 * |x - round x| := by
    field_simp
    ring
  rwa [heq] at h

/-- A point whose chord to one is short lies near an integer. -/
theorem abs_sub_round_le_of_chord_le {x δ : ℝ}
    (h : ‖angularCharacter x - 1‖ ≤ δ) : |x - round x| ≤ δ / 4 := by
  have hc := (four_mul_abs_sub_round_le_chord x).trans h
  linarith

/-- Chord distance controls the quotient norm at every point of the additive circle. -/
theorem four_mul_norm_le_chord (θ : AddCircle (1 : ℝ)) :
    4 * ‖θ‖ ≤ ‖fourier 1 θ - 1‖ := by
  induction θ using QuotientAddGroup.induction_on
  rename_i x
  simpa only [UnitAddCircle.norm_eq, angularCharacter] using four_mul_abs_sub_round_le_chord x

/-- The normalized Haar measure of a chord ball of radius `δ ≤ 2` is at most `δ/2`. -/
theorem haar_angular_small_ball {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2) :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).real
      {θ | ‖fourier 1 θ - 1‖ ≤ δ} ≤ δ / 2 := by
  have hsub : {θ : AddCircle (1 : ℝ) | ‖fourier 1 θ - 1‖ ≤ δ} ⊆
      Metric.closedBall 0 (δ / 4) := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := (four_mul_norm_le_chord θ).trans hθ
    linarith
  apply (measureReal_mono hsub).trans
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  rw [← hvol, measureReal_def, AddCircle.volume_closedBall]
  rw [min_eq_right (by linarith : 2 * (δ / 4) ≤ 1), ENNReal.toReal_ofReal (by positivity)]
  ring_nf
  exact le_rfl


/-- Times in `[0,τ]` at which a frequency difference is within chord distance `δ` of resonance. -/
def angularResonanceTimes (d τ δ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ τ ∧ ‖angularCharacter (d * t) - 1‖ ≤ δ}

/-- A finite interval cover of the near-resonant times, with one interval per nearest integer. -/
theorem angularResonanceTimes_subset_intervals {d τ δ : ℝ}
    (hd : 0 < d) :
    angularResonanceTimes d τ δ ⊆
      ⋃ k ∈ Finset.range (⌈d * τ⌉₊ + 1),
        Set.Icc (((k : ℝ) - δ / 4) / d) (((k : ℝ) + δ / 4) / d) := by
  intro t ht
  obtain ⟨ht0, htτ, hchord⟩ := ht
  have hx0 : 0 ≤ d * t := mul_nonneg hd.le ht0
  have hxτ : d * t ≤ d * τ := mul_le_mul_of_nonneg_left htτ hd.le
  have hround0 : 0 ≤ round (d * t) := by
    have h := sub_half_lt_round (d * t)
    have hr : (-1 : ℝ) < (round (d * t) : ℝ) := by linarith
    have hr' : (-1 : ℤ) < round (d * t) := by exact_mod_cast hr
    omega
  let k : ℕ := (round (d * t)).toNat
  have hk : (k : ℝ) = (round (d * t) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hround0
  have hklt : k < ⌈d * τ⌉₊ + 1 := by
    have hr := round_le_add_half (d * t)
    have hc := Nat.le_ceil (d * τ)
    have hreal : (k : ℝ) < ((⌈d * τ⌉₊ + 1 : ℕ) : ℝ) := by
      rw [hk, Nat.cast_add, Nat.cast_one]
      linarith
    exact_mod_cast hreal
  apply Set.mem_iUnion.mpr
  refine ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hklt, ?_⟩⟩
  have hdist := abs_sub_round_le_of_chord_le hchord
  rw [← hk] at hdist
  obtain ⟨hleft, hright⟩ := abs_le.mp hdist
  constructor
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply (le_div_iff₀ hd).mpr
    nlinarith

/-- The Lebesgue measure of near-resonant times has an explicit endpoint loss.
There are at most `⌈dτ⌉+1` intervals, each of length `δ/(2d)`. -/
theorem volume_angularResonanceTimes_le {d τ δ : ℝ}
    (hd : 0 < d) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) :
    volume.real (angularResonanceTimes d τ δ) ≤ δ * (τ + 1 / d) := by
  let I : ℕ → Set ℝ := fun k =>
    Set.Icc (((k : ℝ) - δ / 4) / d) (((k : ℝ) + δ / 4) / d)
  have hlength (k : ℕ) : volume.real (I k) = δ / (2 * d) := by
    change volume.real (Set.Icc (((k : ℝ) - δ / 4) / d) (((k : ℝ) + δ / 4) / d)) = _
    rw [Real.volume_real_Icc]
    have heq : (((k : ℝ) + δ / 4) / d) - (((k : ℝ) - δ / 4) / d) = δ / (2 * d) := by ring
    rw [heq, max_eq_left (by positivity)]
  have hfinite : volume (⋃ k ∈ Finset.range (⌈d * τ⌉₊ + 1), I k) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le _ _)
    simp [I, Real.volume_Icc]
  have hbound := (measureReal_mono (angularResonanceTimes_subset_intervals hd) hfinite).trans
    (measureReal_biUnion_finset_le (μ := volume) (Finset.range (⌈d * τ⌉₊ + 1)) I)
  simp_rw [hlength] at hbound
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  have hcount : ((⌈d * τ⌉₊ + 1 : ℕ) : ℝ) ≤ d * τ + 2 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hd.le hτ)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    _ ≤ ((⌈d * τ⌉₊ + 1 : ℕ) : ℝ) * (δ / (2 * d)) := hbound
    _ ≤ (d * τ + 2) * (δ / (2 * d)) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ δ * (τ + 1 / d) := by
      have heq : (d * τ + 2) * (δ / (2 * d)) = δ * τ / 2 + δ / d := by
        field_simp
      rw [heq]
      calc
        _ ≤ δ * τ + δ / d := by nlinarith [mul_nonneg hδ hτ]
        _ = _ := by ring


@[simp] theorem norm_angularCharacter (x : ℝ) : ‖angularCharacter x‖ = 1 := by
  rw [angularCharacter_eq, norm_unitCirclePoint]

/-- Multiplication of angular characters corresponds to addition of their arguments. -/
theorem angularCharacter_add (x y : ℝ) :
    angularCharacter (x + y) = angularCharacter x * angularCharacter y := by
  simp only [angularCharacter, fourier_one, AddCircle.coe_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- Chord length between two phases depends only on their difference. -/
theorem norm_angularCharacter_sub (x y : ℝ) :
    ‖angularCharacter x - angularCharacter y‖ = ‖angularCharacter (x - y) - 1‖ := by
  have heq : angularCharacter x - angularCharacter y =
      (angularCharacter (x - y) - 1) * angularCharacter y := by
    rw [sub_mul, one_mul, ← angularCharacter_add, sub_add_cancel]
  rw [heq, norm_mul, norm_angularCharacter, mul_one]

/-- Reversing an angle preserves its chord distance from one. -/
theorem norm_angularCharacter_neg_sub_one (x : ℝ) :
    ‖angularCharacter (-x) - 1‖ = ‖angularCharacter x - 1‖ := by
  have hz : angularCharacter 0 = 1 := by simp [angularCharacter_eq, unitCirclePoint]
  have h := norm_angularCharacter_sub 0 x
  rw [zero_sub, hz, norm_sub_rev] at h
  exact h.symm

/-- Absolute frequency differences give the same pairwise chord distance. -/
theorem norm_angularCharacter_pair (a b t : ℝ) :
    ‖angularCharacter (a * t) - angularCharacter (b * t)‖ =
      ‖angularCharacter (|a - b| * t) - 1‖ := by
  rw [norm_angularCharacter_sub, ← sub_mul]
  rcases le_or_gt 0 (a - b) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, neg_mul, norm_angularCharacter_neg_sub_one]

/-- Pairwise angular near-collisions occupy at most `δ(τ+1/|a-b|)` of `[0,τ]`. -/
theorem volume_angular_pair_collision_le {a b τ δ : ℝ}
    (hab : a ≠ b) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧
      ‖angularCharacter (a * t) - angularCharacter (b * t)‖ ≤ δ} ≤
      δ * (τ + 1 / |a - b|) := by
  simp_rw [norm_angularCharacter_pair]
  exact volume_angularResonanceTimes_le (abs_pos.mpr (sub_ne_zero.mpr hab)) hτ hδ


/-- The finite union bound for any specified collection of frequency pairs. -/
theorem volume_finite_angular_collisions_le {ι : Type*} (s : Finset (ι × ι))
    (a : ι → ℝ) {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hab : ∀ p ∈ s, a p.1 ≠ a p.2) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ p ∈ s,
      ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} ≤
      ∑ p ∈ s, δ * (τ + 1 / |a p.1 - a p.2|) := by
  have heq : {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ p ∈ s,
      ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} =
      ⋃ p ∈ s, {t | 0 ≤ t ∧ t ≤ τ ∧
        ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} := by
    ext t
    simp only [Set.mem_ofPred, Set.mem_iUnion]
    aesop
  rw [heq]
  apply (measureReal_biUnion_finset_le s _).trans
  apply Finset.sum_le_sum
  intro p hp
  exact volume_angular_pair_collision_le (hab p hp) hτ hδ

/-- If every frequency difference spans at least one turn during the interval,
the collision probability costs at most `2δτ` for each specified pair. -/
theorem volume_finite_angular_collisions_le_of_spacing {ι : Type*} (s : Finset (ι × ι))
    (a : ι → ℝ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hspacing : ∀ p ∈ s, 1 ≤ |a p.1 - a p.2| * τ) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ p ∈ s,
      ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} ≤
      (s.card : ℝ) * (2 * δ * τ) := by
  have hdiff (p : ι × ι) (hp : p ∈ s) : 0 < |a p.1 - a p.2| := by
    have h := hspacing p hp
    have hnonneg := abs_nonneg (a p.1 - a p.2)
    by_contra! hzero
    have heq := le_antisymm hzero hnonneg
    rw [heq, zero_mul] at h
    norm_num at h
  have hbase := volume_finite_angular_collisions_le s a hτ.le hδ
    (fun p hp => sub_ne_zero.mp (abs_pos.mp (hdiff p hp)))
  apply hbase.trans
  calc
    _ ≤ ∑ _p ∈ s, 2 * δ * τ := by
      apply Finset.sum_le_sum
      intro p hp
      have hrecip : 1 / |a p.1 - a p.2| ≤ τ :=
        (div_le_iff₀ (hdiff p hp)).mpr (by simpa only [mul_comm] using hspacing p hp)
      nlinarith [mul_le_mul_of_nonneg_left hrecip hδ]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


/-- A uniform positive frequency gap bounds the loss for a finite collection of pairs. -/
theorem volume_finite_angular_collisions_le_of_gap {ι : Type*} (s : Finset (ι × ι))
    (a : ι → ℝ) {τ δ gap : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hgap : 0 < gap)
    (hspacing : ∀ p ∈ s, gap ≤ |a p.1 - a p.2|) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ p ∈ s,
      ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} ≤
      (s.card : ℝ) * δ * (τ + 1 / gap) := by
  have hbase := volume_finite_angular_collisions_le s a hτ hδ
    (fun p hp => sub_ne_zero.mp (abs_pos.mp (hgap.trans_le (hspacing p hp))))
  apply hbase.trans
  calc
    _ ≤ ∑ _p ∈ s, δ * (τ + 1 / gap) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (one_div_le_one_div_of_le hgap (hspacing p hp)) τ) hδ
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- For a finite family of gap-separated frequencies, the total angular collision
loss is bounded by the square of the family size times the per-pair estimate. -/
theorem volume_angular_collisions_le_card_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {τ δ gap : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hgap : 0 < gap)
    (hspacing : ∀ i j, i ≠ j → gap ≤ |a i - a j|) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ i j, i ≠ j ∧
      ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖ ≤ δ} ≤
      (Fintype.card ι : ℝ) ^ 2 * δ * (τ + 1 / gap) := by
  classical
  let s : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hbase := volume_finite_angular_collisions_le_of_gap s a hτ hδ hgap
    (fun p hp => hspacing p.1 p.2 (Finset.mem_filter.mp hp).2)
  have heq : {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ i j, i ≠ j ∧
      ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖ ≤ δ} =
      {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ p ∈ s,
        ‖angularCharacter (a p.1 * t) - angularCharacter (a p.2 * t)‖ ≤ δ} := by
    ext t
    simp only [Set.mem_ofPred, s, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.exists]
  rw [heq]
  have hcard : (s.card : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
    have h := Finset.card_le_card (show s ⊆ (Finset.univ : Finset (ι × ι)) from Finset.filter_subset _ _)
    simp only [Finset.card_univ, Fintype.card_prod] at h
    rw [pow_two]
    exact_mod_cast h
  exact hbase.trans (by gcongr)


/-- The strict pair-collision event obeys the same finite-family estimate. -/
theorem volume_strict_angular_collisions_le_card_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {τ δ gap : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hgap : 0 < gap)
    (hspacing : ∀ i j, i ≠ j → gap ≤ |a i - a j|) :
    volume.real {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ i j, i ≠ j ∧
      ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖ < δ} ≤
      (Fintype.card ι : ℝ) ^ 2 * δ * (τ + 1 / gap) := by
  apply le_trans _ (volume_angular_collisions_le_card_sq a hτ hδ hgap hspacing)
  apply measureReal_mono
  · rintro t ⟨ht0, htτ, i, j, hij, hdist⟩
    exact ⟨ht0, htτ, i, j, hij, hdist.le⟩
  · apply measure_ne_top_of_subset (s := Set.Icc 0 τ)
    · intro t ht
      exact ⟨ht.1, ht.2.1⟩
    · simp [Real.volume_Icc]

end Erdos522
