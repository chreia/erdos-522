/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AdmissibleMovingRootMatching
import Erdos522.Probability.AdmissibleSparseRadialProfile
import Erdos522.Probability.RealPowerAnnularTightness
import Erdos522.Probability.MovingRadialProfile

/-!
# Radial interpolation along arbitrary admissible real powers

The sparse radial profile, a vanishing doubled matching band, and annular
tightness give all-degree convergence. The proof retains the chosen real
degree exponent throughout the block interpolation.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The doubled sparse band that absorbs both roots and target radii. -/
def realPowerRadialBandFraction (q κ : ℝ) (ω : RademacherSequence) (x : ℝ) (j : ℕ) : ℝ :=
  let N := realPowerDegree q j
  let P := rademacherPolynomial N (rademacherPrefix N ω)
  let r := 1 + x / N
  let w := (N : ℝ) ^ (-1 - κ)
  ((closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) : ℕ) : ℝ) / N

theorem realPowerRadialBandFraction_eq_sub (q κ : ℝ) (ω : RademacherSequence) (x : ℝ) (j : ℕ) :
    realPowerRadialBandFraction q κ ω x j =
      rademacherRadialFraction ω (realPowerDegree q j)
        (1 + x / realPowerDegree q j + 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ)) -
      rademacherRadialFraction ω (realPowerDegree q j)
        (1 + x / realPowerDegree q j - 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ)) := by
  have hw := Real.rpow_nonneg (Nat.cast_nonneg (realPowerDegree q j)) (-1 - κ)
  have hmono := closedZeroCount_mono
    (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
    (show 1 + x / realPowerDegree q j - 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ) ≤
      1 + x / realPowerDegree q j + 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ) by linarith)
  simp only [realPowerRadialBandFraction, rademacherRadialFraction, Nat.cast_sub hmono, sub_div]

/-- The degree increment and unmatched-root threshold both have vanishing relative mass. -/
theorem tendsto_real_power_matching_remainder {q d : ℝ} (hq : 1 < q) (hd : 0 < d) :
    Tendsto (fun j : ℕ => (realPowerDegree q j : ℝ) ^ (1 - d) / realPowerDegree q j +
      (realPowerBlockLength q j : ℝ) / realPowerDegree q j) atTop (𝓝 0) := by
  have ht := tendsto_realPowerDegree (show 0 < q by linarith)
  have hp := (tendsto_nat_rpow_neg hd).comp ht
  have hp' : Tendsto (fun j : ℕ => (realPowerDegree q j : ℝ) ^ (1 - d) /
      realPowerDegree q j) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [ht.eventually_ge_atTop 1] with j hj
    have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast (show 0 < realPowerDegree q j by omega)
    dsimp only [Function.comp_def]
    nth_rw 3 [← Real.rpow_one (realPowerDegree q j : ℝ)]
    rw [← Real.rpow_sub hn]
    congr 1
    ring
  simpa only [add_zero] using hp'.add (tendsto_realPowerBlockLength_div hq)

/-- The full radial law follows from sparse control along any admissible real-power schedule. -/
theorem ae_radial_limit_of_admissible_sparse_bounds {q t ℓ d κ : ℝ}
    (hscale : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (x c : ℝ)
    (hsparse : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherScaledRadialFraction ω (realPowerDegree q j) x) atTop (𝓝 c))
    (hband : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (realPowerRadialBandFraction q κ ω x) atTop (𝓝 0))
    (htight : ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, realPowerAnnularTailFraction q ω K j ≤ ε) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x) atTop (𝓝 c) := by
  have hq2 := two_lt_of_occupation_summability hq hscale.logarithmic_pos hscale.occupation_summability
  have hq1 : 1 < q := by linarith
  have hmatching := ae_all_iff.mpr (fun K : ℕ =>
    ae_admissible_moving_block_count_bound hscale hq K (Nat.cast_nonneg K))
  filter_upwards [hsparse, hband, htight, hmatching] with ω hωs hωb hωt hωm
  let X : ℕ → ℝ := fun n =>
    closedZeroCount (rademacherPolynomial n (rademacherPrefix n ω)) (1 + x / n)
  let a : ℕ → ℝ := fun h => 1 / ((h : ℝ) + 1)
  let b : ℕ → ℝ := fun j => 2 * realPowerRadialBandFraction q κ ω x j +
    ((realPowerDegree q j : ℝ) ^ (1 - d) / realPowerDegree q j +
      (realPowerBlockLength q j : ℝ) / realPowerDegree q j)
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hωb.const_mul 2).add
      (tendsto_real_power_matching_remainder hq1 hscale.count_pos)
  apply tendsto_normalized_of_parameter_bounds (X := X) (a := a) (b := fun _ => b)
    (strictMono_realPowerDegree hq1.le) (tendsto_realPowerDegree_ratio hq1) hωs ha (fun _ => hb)
  intro h
  obtain ⟨K, hK⟩ := hωt (a h) (by dsimp [a]; positivity)
  filter_upwards [hωm K x, hK, (tendsto_realPowerDegree hq).eventually_ge_atTop 1]
    with j hjM hjK hj1
  intro n hNn hnN
  let N := realPowerDegree q j
  let m := n - N
  have hNm : N + m = n := Nat.add_sub_of_le hNn
  have hm : m ≤ realPowerBlockLength q j := by
    have he := realPowerBlockLength_endpoint hq1.le j
    dsimp [m, N]
    omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hmatch := hjM m hm
  change (Nat.dist (closedZeroCount
    (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
      (closedZeroCount (rademacherPolynomial N (rademacherPrefix N ω)) (1 + x / N)) : ℝ) ≤ _ at hmatch
  rw [hNm, nat_dist_cast_eq_abs] at hmatch
  have hdiv := div_le_div_of_nonneg_right hmatch hn.le
  have hm' : (m : ℝ) / N ≤ (realPowerBlockLength q j : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) hn.le
  change |X n - X N| / (N : ℝ) ≤ a h + b j
  dsimp only [X, a, b, realPowerAnnularTailFraction, realPowerRadialBandFraction] at *
  simp only [add_div, mul_div_assoc] at hdiv
  linarith

/-- The fixed-coordinate radial profile assembled through any admissible
rounded real-power schedule. -/
theorem ae_radial_profile_via_admissible_degrees {q t ℓ d κ : ℝ}
    (hscale : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (x : ℝ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x) atTop (𝓝 (kacRadialProfile x)) := by
  have hq2 := two_lt_of_occupation_summability hq hscale.logarithmic_pos hscale.occupation_summability
  have hprobe (s : ℝ) := ae_admissible_sparse_radial_profile hq2 hscale.logarithmic_pos
    hscale.occupation_summability (fun N => 1 + x / N + s * (N : ℝ) ^ (-1 - κ)) x
      (tendsto_scaled_moving_radius x s hscale.window_pos)
  have hsparse : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherScaledRadialFraction ω (realPowerDegree q j) x)
        atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [rademacherScaledRadialFraction, zero_mul, add_zero] using hprobe 0
  have hband : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (realPowerRadialBandFraction q κ ω x) atTop (𝓝 0) := by
    filter_upwards [hprobe (-2), hprobe 2] with ω hminus hplus
    have heq : realPowerRadialBandFraction q κ ω x = fun j =>
        rademacherRadialFraction ω (realPowerDegree q j)
          (1 + x / realPowerDegree q j + 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ)) -
        rademacherRadialFraction ω (realPowerDegree q j)
          (1 + x / realPowerDegree q j - 2 * (realPowerDegree q j : ℝ) ^ (-1 - κ)) :=
      funext (realPowerRadialBandFraction_eq_sub q κ ω x)
    rw [heq]
    simpa only [sub_self, neg_mul, sub_eq_add_neg] using hplus.sub hminus
  exact ae_radial_limit_of_admissible_sparse_bounds hscale hq x (kacRadialProfile x)
    hsparse hband (ae_real_power_annular_tightness hq2)

/-- Every real sparse-degree exponent greater than two supports the full radial-profile
argument after the explicit retuning of the logarithmic and derivative scales. -/
theorem ae_radial_profile_via_real_power_degrees (q : ℝ) (hq : 2 < q) (x : ℝ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x) atTop (𝓝 (kacRadialProfile x)) :=
  ae_radial_profile_via_admissible_degrees (admissible_sparse_degree_scales hq)
    (by linarith) x

/-- The fixed exponents `t=d=1/32` and `ℓ=κ=1/64` support every schedule
in the open interval `8/3 < q < 16`. -/
theorem ae_radial_profile_via_fixed_degree_scales (q : ℝ)
    (hq : 8 / 3 < q) (hq16 : q < 16) (x : ℝ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x) atTop (𝓝 (kacRadialProfile x)) :=
  ae_radial_profile_via_admissible_degrees (admissible_fixed_sparse_degree_scales hq hq16)
    (by linarith) x

end Erdos522
