/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ReciprocalProgressions
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Separation of short spectral intervals

The difference set of finitely many short intervals has small measure. Its
reflection symmetry halves the measure needed to exclude positive reciprocal
progressions, yielding one time at which all nonzero progression differences
are avoided.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators Pointwise

namespace Erdos522

/-- Closed intervals of a common radius around a finite set of real centers. -/
def finiteIntervalUnion (T : Finset ℝ) (r : ℝ) : Set ℝ :=
  ⋃ c ∈ T, Icc (c - r) (c + r)

/-- Membership means being within the radius of one of the centers. -/
theorem mem_finiteIntervalUnion_iff {T : Finset ℝ} {r x : ℝ} :
    x ∈ finiteIntervalUnion T r ↔ ∃ c ∈ T, |x - c| ≤ r := by
  simp only [finiteIntervalUnion, mem_iUnion, mem_Icc, abs_le]
  constructor <;> rintro ⟨c, hc, h₁, h₂⟩ <;>
    exact ⟨c, hc, by constructor <;> linarith⟩

/-- The complement consists of points farther than the radius from every center. -/
theorem not_mem_finiteIntervalUnion_iff {T : Finset ℝ} {r x : ℝ} :
    x ∉ finiteIntervalUnion T r ↔ ∀ c ∈ T, r < |x - c| := by
  simp only [mem_finiteIntervalUnion_iff, not_exists, not_and, not_le]

/-- A finite union of closed intervals is measurable. -/
theorem measurableSet_finiteIntervalUnion (T : Finset ℝ) (r : ℝ) :
    MeasurableSet (finiteIntervalUnion T r) :=
  T.measurableSet_biUnion (fun _ _ => measurableSet_Icc)

/-- The total interval length bounds the measure of the finite union. -/
theorem volume_finiteIntervalUnion_le (T : Finset ℝ) {r : ℝ} (_hr : 0 ≤ r) :
    volume (finiteIntervalUnion T r) ≤ ENNReal.ofReal (2 * r * T.card) := by
  calc
    _ ≤ ∑ c ∈ T, volume (Icc (c - r) (c + r)) := measure_biUnion_finset_le _ _
    _ = ∑ _c ∈ T, ENNReal.ofReal (2 * r) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Real.volume_Icc]
      congr 1
      ring
    _ = ENNReal.ofReal (2 * r * T.card) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

/-- A symmetric set has at most half its measure on the positive half-line. -/
theorem volume_positive_part_le_half {S : Set ℝ} (hS : MeasurableSet S)
    (hneg : ∀ x ∈ S, -x ∈ S) {B : ℝ} (hB : 0 ≤ B)
    (hbound : volume S ≤ ENNReal.ofReal B) :
    volume (S ∩ Ioi 0) ≤ ENNReal.ofReal (B / 2) := by
  let G := S ∩ Ioi (0 : ℝ)
  let H := (fun x : ℝ => -x) ⁻¹' G
  have hG : MeasurableSet G := hS.inter measurableSet_Ioi
  have hH : MeasurableSet H := hG.preimage measurable_neg
  have hreflection : volume H = volume G := by
    simpa [H] using Real.volume_preimage_mul_left (a := -1) (by norm_num) G
  have hdisjoint : Disjoint G H := by
    apply disjoint_left.mpr
    intro x hx hxH
    have hpos : 0 < x := hx.2
    have hnegpos : 0 < -x := hxH.2
    linarith
  have hsubset : G ∪ H ⊆ S := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · simpa only [neg_neg] using hneg (-x) hx.1
  have hsum : volume G + volume G ≤ ENNReal.ofReal B := by
    calc
      _ = volume (G ∪ H) := by rw [measure_union hdisjoint hH, hreflection]
      _ ≤ volume S := measure_mono hsubset
      _ ≤ _ := hbound
  have hfinite : volume G ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono inter_subset_left).trans hbound)
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hfinite, hfinite⟩) ENNReal.ofReal_ne_top).mpr hsum
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal hB] at hreal
  apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  linarith

/-- A difference of two points in the interval union lies in the corresponding
    doubled-radius interval union around differences of centers. -/
theorem sub_mem_finiteIntervalUnion {T : Finset ℝ} {r x y : ℝ}
    (hx : x ∈ finiteIntervalUnion T r) (hy : y ∈ finiteIntervalUnion T r) :
    x - y ∈ finiteIntervalUnion (T - T) (2 * r) := by
  classical
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  obtain ⟨d, hd, hyd⟩ := mem_iUnion₂.mp hy
  refine mem_iUnion₂.mpr ⟨c - d, Finset.sub_mem_sub hc hd, ?_⟩
  constructor <;> linarith [hxc.1, hxc.2, hyd.1, hyd.2]

/-- The interval union around differences of centers is invariant under reflection. -/
theorem neg_mem_finiteIntervalUnion_sub {T : Finset ℝ} {r x : ℝ}
    (hx : x ∈ finiteIntervalUnion (T - T) r) :
    -x ∈ finiteIntervalUnion (T - T) r := by
  classical
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hc
  refine mem_iUnion₂.mpr ⟨b - a, Finset.sub_mem_sub hb ha, ?_⟩
  constructor <;> linarith [hxc.1, hxc.2]

/-- The positive half of the difference cover has the required quadratic cardinality bound. -/
theorem volume_positive_difference_cover_le (T : Finset ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (finiteIntervalUnion (T - T) (4 * r) ∩ Ioi 0) ≤
      ENNReal.ofReal (4 * r * (T.card : ℝ) ^ 2) := by
  classical
  have hcard : ((T - T).card : ℝ) ≤ (T.card : ℝ) ^ 2 := by
    simpa only [pow_two, Nat.cast_mul] using
      (show ((T - T).card : ℝ) ≤ (T.card * T.card : ℕ) by
        exact_mod_cast (Finset.card_sub_le (s := T) (t := T)))
  have hbound : volume (finiteIntervalUnion (T - T) (4 * r)) ≤
      ENNReal.ofReal (8 * r * (T.card : ℝ) ^ 2) := by
    apply (volume_finiteIntervalUnion_le (T - T) (show 0 ≤ 4 * r by positivity)).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have h := volume_positive_part_le_half (measurableSet_finiteIntervalUnion _ _)
    (fun _ hx => neg_mem_finiteIntervalUnion_sub hx) (by positivity) hbound
  convert h using 1
  congr 1
  ring

/-- If the positive difference cover is short enough, one reciprocal progression
    separates every pair of points in the finite interval union. -/
theorem exists_time_separating_finiteIntervalUnion (T : Finset ℝ) (τ r : ℝ)
    (hτ : 0 < τ) (hr : 0 ≤ r) (hsize : 4 * r * (T.card : ℝ) ^ 2 < 1 / (2 * τ)) :
    ∃ t ∈ Ioo (τ / 2) τ, ∀ x ∈ finiteIntervalUnion T (2 * r),
      ∀ y ∈ finiteIntervalUnion T (2 * r), ∀ k : ℤ, k ≠ 0 → x - y ≠ (k : ℝ) / t := by
  classical
  let D := finiteIntervalUnion (T - T) (4 * r)
  let G := D ∩ Ioi (0 : ℝ)
  have hG : MeasurableSet G := (measurableSet_finiteIntervalUnion _ _).inter measurableSet_Ioi
  have hsmall : volume G < ENNReal.ofReal (1 / (2 * τ)) :=
    (volume_positive_difference_cover_le T hr).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsize)
  obtain ⟨t, ht, havoid⟩ := exists_reciprocalProgression_avoiding τ hτ G hG
    inter_subset_right hsmall
  have ht0 : 0 < t := by linarith [ht.1]
  have hpositive (x : ℝ) (hx : x ∈ finiteIntervalUnion T (2 * r))
      (y : ℝ) (hy : y ∈ finiteIntervalUnion T (2 * r)) (k : ℕ) (hk : 0 < k) :
      x - y ≠ (k : ℝ) / t := by
    intro heq
    apply havoid k hk
    have hmem : x - y ∈ D := by
      simpa only [D, show 2 * (2 * r) = 4 * r by ring] using sub_mem_finiteIntervalUnion hx hy
    refine ⟨heq ▸ hmem, ?_⟩
    exact div_pos (by exact_mod_cast hk) ht0
  refine ⟨t, ht, ?_⟩
  intro x hx y hy k hk heq
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · have hmpos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      simp only [hm0, Int.natCast_zero] at hm
      exact hk hm
    apply hpositive x hx y hy m hmpos
    simpa only [hm, Int.cast_natCast] using heq
  · have hmpos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      simp only [hm0, Int.natCast_zero, neg_zero] at hm
      exact hk hm
    apply hpositive y hy x hx m hmpos
    rw [hm, Int.cast_neg, Int.cast_natCast, neg_div] at heq
    linarith

/-- The explicit spectral radius `1/(8(n+1)²τ)` gives a separating time for at
    most `n` centers. This includes the empty set of centers. -/
theorem exists_time_separating_short_spectral_intervals (T : Finset ℝ) (n : ℕ)
    (hcard : T.card ≤ n) (τ : ℝ) (hτ : 0 < τ) :
    let r : ℝ := 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ)
    ∃ t ∈ Ioo (τ / 2) τ, ∀ x ∈ finiteIntervalUnion T (2 * r),
      ∀ y ∈ finiteIntervalUnion T (2 * r), ∀ k : ℤ, k ≠ 0 → x - y ≠ (k : ℝ) / t := by
  let r : ℝ := 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ)
  have hr : 0 < r := by dsimp [r]; positivity
  apply exists_time_separating_finiteIntervalUnion T τ r hτ hr.le
  have hcardReal : (T.card : ℝ) ≤ n := by exact_mod_cast hcard
  calc
    _ ≤ 4 * r * (n : ℝ) ^ 2 := by gcongr
    _ < 1 / (2 * τ) := by
      dsimp [r]
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have hden : 0 < 8 * ((n : ℝ) + 1) ^ 2 * τ := by positivity
      field_simp
      nlinarith [sq_nonneg (n : ℝ)]

/-- Avoidance on doubled intervals leaves a quantitative progression gap between
    a point in an original interval and any representative in the doubled union. -/
theorem progression_gap_of_interval_separation {T : Finset ℝ} {r t x ξ : ℝ}
    (hsep : ∀ u ∈ finiteIntervalUnion T (2 * r),
      ∀ v ∈ finiteIntervalUnion T (2 * r), ∀ k : ℤ, k ≠ 0 → u - v ≠ (k : ℝ) / t)
    (hx : x ∈ finiteIntervalUnion T r) (hξ : ξ ∈ finiteIntervalUnion T (2 * r))
    (k : ℤ) (hk : k ≠ 0) : r < |x - (ξ + (k : ℝ) / t)| := by
  by_contra h
  have habs : |x - (ξ + (k : ℝ) / t)| ≤ r := le_of_not_gt h
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  have htranslated : ξ + (k : ℝ) / t ∈ finiteIntervalUnion T (2 * r) := by
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hdist := abs_le.mp habs
    constructor <;> linarith [hxc.1, hxc.2, hdist.1, hdist.2]
  exact hsep _ htranslated ξ hξ k hk (by ring)

end Erdos522
