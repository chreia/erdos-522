/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularBlockMatching
import Erdos522.Limits.SparseToDense

/-!
# Interpolating radial root-count limits

For Rademacher prefixes, annular matching reduces an all-degree radial limit
to its sparse limit, vanishing mass in the matching window, and tightness of
the sparse root measures at the scale `1/N` around the unit circle.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The fraction of zeros in a closed disk for a prefix of the infinite sign sequence. -/
def rademacherRadialFraction (ω : RademacherSequence) (N : ℕ) (r : ℝ) : ℝ :=
  (closedZeroCount (rademacherPolynomial N (rademacherPrefix N ω)) r : ℝ) / N

/-- The fraction of sparse-degree roots outside a closed annulus of width `K/N`. -/
def sparseAnnularTailFraction (ω : RademacherSequence) (K j : ℕ) : ℝ :=
  (zeroCountIn (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
    {z | |‖z‖ - 1| ≤ (K : ℝ) / (j ^ 8 : ℕ)}ᶜ : ℝ) / ((j ^ 8 : ℕ) : ℝ)

/-- The sparse-degree root mass in the matching window, including the outer circle
    and excluding the inner circle. -/
def sparseRadialBandFraction (ω : RademacherSequence) (r : ℝ) (j : ℕ) : ℝ :=
  let P := rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)
  ((closedZeroCount P (r + radialMatchingWindow (j ^ 8)) -
    closedZeroCount P (r - radialMatchingWindow (j ^ 8)) : ℕ) : ℝ) / ((j ^ 8 : ℕ) : ℝ)

/-- Natural distance becomes the absolute difference after casting to the reals. -/
theorem nat_dist_cast_eq_abs (n m : ℕ) : (Nat.dist n m : ℝ) = |(n : ℝ) - m| := by
  rcases le_total n m with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- The normalized unmatched-root and degree-increment terms tend to zero. -/
theorem tendsto_annular_matching_remainder :
    Tendsto (fun j : ℕ => ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) / ((j ^ 8 : ℕ) : ℝ) +
      (eighthPowerBlockLength j : ℝ) / ((j ^ 8 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hp := (tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 32)).comp
    (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
  have hp' : Tendsto (fun j : ℕ => ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) /
      ((j ^ 8 : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hn : (0 : ℝ) < (j ^ 8 : ℕ) := by positivity
    dsimp only [Function.comp_def]
    nth_rw 3 [← Real.rpow_one ((j ^ 8 : ℕ) : ℝ)]
    rw [← Real.rpow_sub hn]
    congr 1
    norm_num
  simpa only [add_zero] using hp'.add tendsto_eighthPowerBlockLength_div

/-- A sparse radial limit extends to all degrees once the matching band has vanishing
    mass and the sparse root measures are tight on the annular scale. -/
theorem ae_radial_count_limit_of_sparse_bounds (r c : ℝ)
    (hsparse : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8) r) atTop (𝓝 c))
    (hband : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (sparseRadialBandFraction ω r) atTop (𝓝 0))
    (htight : ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω K j ≤ ε) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherRadialFraction ω n r) atTop (𝓝 c) := by
  filter_upwards [hsparse, hband, htight, ae_forall_annular_block_count_bound]
    with ω hωs hωb hωt hωm
  let X : ℕ → ℝ := fun n =>
    closedZeroCount (rademacherPolynomial n (rademacherPrefix n ω)) r
  let a : ℕ → ℝ := fun h => 1 / ((h : ℝ) + 1)
  let b : ℕ → ℝ := fun j => sparseRadialBandFraction ω r j +
    (((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) / ((j ^ 8 : ℕ) : ℝ) +
      (eighthPowerBlockLength j : ℝ) / ((j ^ 8 : ℕ) : ℝ))
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [add_zero] using hωb.add tendsto_annular_matching_remainder
  apply tendsto_normalized_of_parameter_bounds (X := X) (a := a) (b := fun _ => b)
    strictMono_eighth_power tendsto_eighth_power_degree_ratio hωs ha (fun _ => hb)
  intro h
  obtain ⟨K, hK⟩ := hωt (a h) (by dsimp [a]; positivity)
  filter_upwards [hωm K, hK, eventually_ge_atTop 1] with j hjM hjK hj1
  intro n hNn hnN
  let N := j ^ 8
  let m := n - N
  have hNm : N + m = n := Nat.add_sub_of_le hNn
  have hm : m ≤ eighthPowerBlockLength j := by
    have he := eighthPowerBlockLength_endpoint j
    dsimp [m, N]
    omega
  have hn : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmatch := hjM m hm r
  change (Nat.dist (closedZeroCount
    (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r)
      (closedZeroCount (rademacherPolynomial N (rademacherPrefix N ω)) r) : ℝ) ≤ _ at hmatch
  rw [hNm, nat_dist_cast_eq_abs] at hmatch
  have hdiv := div_le_div_of_nonneg_right hmatch hn.le
  have hm' : (m : ℝ) / N ≤ (eighthPowerBlockLength j : ℝ) / N := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hn.le
  change |X n - X N| / (N : ℝ) ≤ a h + b j
  dsimp only [X, a, b, sparseAnnularTailFraction, sparseRadialBandFraction] at *
  simp only [add_div] at hdiv
  linarith

/-- The band mass is the difference of its two normalized closed-disk counts. -/
theorem sparseRadialBandFraction_eq_sub (ω : RademacherSequence) (r : ℝ) (j : ℕ) :
    sparseRadialBandFraction ω r j =
      rademacherRadialFraction ω (j ^ 8) (r + radialMatchingWindow (j ^ 8)) -
      rademacherRadialFraction ω (j ^ 8) (r - radialMatchingWindow (j ^ 8)) := by
  have hw : 0 ≤ radialMatchingWindow (j ^ 8) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmono := closedZeroCount_mono
    (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
      (show r - radialMatchingWindow (j ^ 8) ≤ r + radialMatchingWindow (j ^ 8) by linarith)
  simp only [sparseRadialBandFraction, rademacherRadialFraction, Nat.cast_sub hmono, sub_div]

/-- Convergence at the two sides of the matching window supplies both the central sparse
    limit and the vanishing band mass needed for interpolation. -/
theorem ae_radial_count_limit_of_two_radius_bounds (r c : ℝ)
    (hminus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (r - radialMatchingWindow (j ^ 8))) atTop (𝓝 c))
    (hplus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (r + radialMatchingWindow (j ^ 8))) atTop (𝓝 c))
    (htight : ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω K j ≤ ε) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherRadialFraction ω n r) atTop (𝓝 c) := by
  apply ae_radial_count_limit_of_sparse_bounds r c ?_ ?_ htight
  · filter_upwards [hminus, hplus] with ω hωm hωp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hωm hωp
    · intro j
      dsimp only [rademacherRadialFraction]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Nat.cast_le.mpr <| closedZeroCount_mono
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
          (show r - radialMatchingWindow (j ^ 8) ≤ r by
            have := Real.rpow_nonneg (Nat.cast_nonneg (j ^ 8)) (-1 - 1 / 64 : ℝ)
            change 0 ≤ radialMatchingWindow (j ^ 8) at this
            linarith)
    · intro j
      dsimp only [rademacherRadialFraction]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Nat.cast_le.mpr <| closedZeroCount_mono
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
          (show r ≤ r + radialMatchingWindow (j ^ 8) by
            have := Real.rpow_nonneg (Nat.cast_nonneg (j ^ 8)) (-1 - 1 / 64 : ℝ)
            change 0 ≤ radialMatchingWindow (j ^ 8) at this
            linarith)
  · filter_upwards [hminus, hplus] with ω hωm hωp
    have heq : sparseRadialBandFraction ω r = fun j =>
        rademacherRadialFraction ω (j ^ 8) (r + radialMatchingWindow (j ^ 8)) -
        rademacherRadialFraction ω (j ^ 8) (r - radialMatchingWindow (j ^ 8)) :=
      funext (sparseRadialBandFraction_eq_sub ω r)
    rw [heq]
    simpa only [sub_self] using hωp.sub hωm

/-- The four-radius annular tail coefficient yields tightness after a countable
    intersection over annular widths. -/
theorem ae_annular_tightness_of_tail_bounds
    (htail : ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω (K + 1) j ≤
        2 * Real.log 2 / ((K : ℝ) + 1) + ε) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω K j ≤ ε := by
  filter_upwards [htail] with ω hω
  intro ε hε
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * Real.log 2)
  simp only [mul_zero] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (ht.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity))
  refine ⟨K + 1, ?_⟩
  filter_upwards [hω K (ε / 2) (by positivity)] with j hj
  have hb := hK K le_rfl
  rw [← mul_div_assoc, mul_one] at hb
  linarith

end Erdos522
