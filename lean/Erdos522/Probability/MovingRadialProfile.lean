/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseRadialProfile
import Erdos522.Probability.MovingRadialBlockMatching

/-!
# The full-sequence profile at a fixed radial coordinate

Moving-radius matching absorbs both polynomial perturbation and the drift
from `1 + x/N` to `1 + x/n` within a degree block.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The empirical radial distribution function in the coordinate `N (|z| - 1)`. -/
def rademacherScaledRadialFraction (ω : RademacherSequence) (N : ℕ) (x : ℝ) : ℝ :=
  rademacherRadialFraction ω N (1 + x / N)

def sparseScaledRadialBandFraction (ω : RademacherSequence) (x : ℝ) (j : ℕ) : ℝ :=
  sparseRadialBandFraction ω (1 + x / (j ^ 8 : ℕ)) j

/-- Sparse convergence, a vanishing moving band, and annular tightness extend
the profile to all degrees. -/
theorem ae_scaled_radial_limit_of_sparse_bounds (x c : ℝ)
    (hsparse : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherScaledRadialFraction ω (j ^ 8) x) atTop (𝓝 c))
    (hband : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (sparseScaledRadialBandFraction ω x) atTop (𝓝 0))
    (htight : ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω K j ≤ ε) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x) atTop (𝓝 c) := by
  filter_upwards [hsparse, hband, htight, ae_forall_moving_radial_block_count_bound]
    with ω hωs hωb hωt hωm
  let X : ℕ → ℝ := fun n =>
    closedZeroCount (rademacherPolynomial n (rademacherPrefix n ω)) (1 + x / n)
  let a : ℕ → ℝ := fun h => 1 / ((h : ℝ) + 1)
  let b : ℕ → ℝ := fun j => sparseScaledRadialBandFraction ω x j +
    (((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) / ((j ^ 8 : ℕ) : ℝ) +
      (eighthPowerBlockLength j : ℝ) / ((j ^ 8 : ℕ) : ℝ))
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [add_zero] using hωb.add tendsto_annular_matching_remainder
  apply tendsto_normalized_of_parameter_bounds (X := X) (a := a) (b := fun _ => b)
    strictMono_eighth_power tendsto_eighth_power_degree_ratio hωs ha (fun _ => hb)
  intro h
  obtain ⟨K, hK⟩ := hωt (a h) (by dsimp [a]; positivity)
  filter_upwards [hωm K x, hK, eventually_ge_atTop 1] with j hjM hjK hj1
  intro n hNn hnN
  let N := j ^ 8
  let m := n - N
  have hNm : N + m = n := Nat.add_sub_of_le hNn
  have hm : m ≤ eighthPowerBlockLength j := by
    have he := eighthPowerBlockLength_endpoint j
    dsimp [m, N]
    omega
  have hn : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmatch := hjM m hm
  change (Nat.dist (closedZeroCount
    (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
      (closedZeroCount (rademacherPolynomial N (rademacherPrefix N ω)) (1 + x / N)) : ℝ) ≤ _ at hmatch
  rw [hNm, nat_dist_cast_eq_abs] at hmatch
  have hdiv := div_le_div_of_nonneg_right hmatch hn.le
  have hm' : (m : ℝ) / N ≤ (eighthPowerBlockLength j : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) hn.le
  change |X n - X N| / (N : ℝ) ≤ a h + b j
  dsimp only [X, a, b, sparseAnnularTailFraction, sparseScaledRadialBandFraction,
    sparseRadialBandFraction] at *
  simp only [add_div] at hdiv
  linarith

/-- The full radial profile holds at each fixed scaled coordinate. -/
theorem ae_scaled_radial_profile_of_harmonic_restriction {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (x : ℝ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun n : ℕ => rademacherScaledRadialFraction ω n x)
        atTop (𝓝 (kacRadialProfile x)) := by
  have hsparse : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherScaledRadialFraction ω (j ^ 8) x)
        atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [rademacherScaledRadialFraction, zero_mul, add_zero] using
      ae_sparse_moving_radius_profile hC hR x 0 (by norm_num : (0 : ℝ) < 1 / 64)
  have hminus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8))) atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [radialMatchingWindow, neg_one_mul, sub_eq_add_neg] using
      ae_sparse_moving_radius_profile hC hR x (-1) (by norm_num : (0 : ℝ) < 1 / 64)
  have hplus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8))) atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [radialMatchingWindow, one_mul] using
      ae_sparse_moving_radius_profile hC hR x 1 (by norm_num : (0 : ℝ) < 1 / 64)
  have hband : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (sparseScaledRadialBandFraction ω x) atTop (𝓝 0) := by
    filter_upwards [hminus, hplus] with ω hωm hωp
    have heq : sparseScaledRadialBandFraction ω x = fun j =>
        rademacherRadialFraction ω (j ^ 8) (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8)) -
        rademacherRadialFraction ω (j ^ 8) (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8)) := by
      funext j
      exact sparseRadialBandFraction_eq_sub ω (1 + x / (j ^ 8 : ℕ)) j
    rw [heq]
    simpa only [sub_self] using hωp.sub hωm
  exact ae_scaled_radial_limit_of_sparse_bounds x (kacRadialProfile x) hsparse hband
    (ae_sparse_annular_tightness_of_harmonic_restriction hC hR)

end Erdos522
