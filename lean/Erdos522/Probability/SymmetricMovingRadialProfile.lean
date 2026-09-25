/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricSparseRadialProfile
import Erdos522.Probability.BoundedRootMatching
import Erdos522.Limits.LogarithmicDegreeCorrection

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
def coefficientScaledRadialFraction (ω : (ℕ → ℂ)) (N : ℕ) (x : ℝ) : ℝ :=
  coefficientRadialFraction ω N (1 + x / N)

/-- Sparse bounded symmetric coefficient mass in a matching window, with the outer boundary included. -/
def coefficientSparseRadialBandFraction (ω : ℕ → ℂ) (r : ℝ) (j : ℕ) : ℝ :=
  let P := Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)
  ((closedZeroCount P (r + radialMatchingWindow (j ^ 8)) -
    closedZeroCount P (r - radialMatchingWindow (j ^ 8)) : ℕ) : ℝ) / ((j ^ 8 : ℕ) : ℝ)

/-- The moving band's mass is the difference of its endpoint distribution values. -/
theorem coefficientSparseRadialBandFraction_eq_sub (ω : ℕ → ℂ) (r : ℝ) (j : ℕ) :
    coefficientSparseRadialBandFraction ω r j =
      coefficientRadialFraction ω (j ^ 8) (r + radialMatchingWindow (j ^ 8)) -
      coefficientRadialFraction ω (j ^ 8) (r - radialMatchingWindow (j ^ 8)) := by
  have hw : 0 ≤ radialMatchingWindow (j ^ 8) := by
    unfold radialMatchingWindow
    positivity
  have hmono := closedZeroCount_mono
    (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)) (by linarith :
      r - radialMatchingWindow (j ^ 8) ≤ r + radialMatchingWindow (j ^ 8))
  simp only [coefficientSparseRadialBandFraction, coefficientRadialFraction,
    Nat.cast_sub hmono, sub_div]

def coefficientSparseScaledRadialBandFraction (ω : (ℕ → ℂ)) (x : ℝ) (j : ℕ) : ℝ :=
  coefficientSparseRadialBandFraction ω (1 + x / (j ^ 8 : ℕ)) j

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {B : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hsecond

/-- Sparse convergence, a vanishing moving band, and annular tightness extend
the profile to all degrees. -/
theorem ae_bounded_scaled_radial_limit_of_sparse_bounds (x c : ℝ)
    (hsparse : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientScaledRadialFraction ω (j ^ 8) x) atTop (𝓝 c))
    (hband : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (coefficientSparseScaledRadialBandFraction ω x) atTop (𝓝 0))
    (htight : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, coefficientSparseAnnularTailFraction ω K j ≤ ε) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun n : ℕ => coefficientScaledRadialFraction ω n x) atTop (𝓝 c) := by
  filter_upwards [hsparse, hband, htight, ae_forall_bounded_moving_radial_block_count_bound μ hB hbound hsecond]
    with ω hωs hωb hωt hωm
  let X : ℕ → ℝ := fun n =>
    closedZeroCount (Polynomial.ofFn (n + 1) (coefficientPrefix n ω)) (1 + x / n)
  let a : ℕ → ℝ := fun h => 1 / ((h : ℝ) + 1)
  let b : ℕ → ℝ := fun j => coefficientSparseScaledRadialBandFraction ω x j +
    (((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) / ((j ^ 8 : ℕ) : ℝ) +
      (eighthPowerBlockLength j : ℝ) / ((j ^ 8 : ℕ) : ℝ)) +
      (⌈zeroRunLogarithmicConstant μ * Real.log (j ^ 8 + 1 : ℕ)⌉₊ : ℝ) / ((j ^ 8 : ℕ) : ℝ)
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 0) := by
    have hcorrection := (tendsto_zero_run_degree_correction μ hsecond).comp
      (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
    simpa only [b, add_zero, Function.comp_def] using (hωb.add tendsto_annular_matching_remainder).add hcorrection
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
    (Polynomial.ofFn (N + m + 1) (coefficientPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
      (closedZeroCount (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)) (1 + x / N)) : ℝ) ≤ _ at hmatch
  rw [hNm, nat_dist_cast_eq_abs] at hmatch
  have hdiv := div_le_div_of_nonneg_right hmatch hn.le
  have hm' : (m : ℝ) / N ≤ (eighthPowerBlockLength j : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) hn.le
  change |X n - X N| / (N : ℝ) ≤ a h + b j
  dsimp only [X, a, b, coefficientSparseAnnularTailFraction, coefficientSparseScaledRadialBandFraction,
    coefficientSparseRadialBandFraction] at *
  simp only [add_div] at hdiv
  linarith

/-- The full radial profile holds at each fixed scaled coordinate. -/
theorem ae_bounded_scaled_radial_profile (x : ℝ) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun n : ℕ => coefficientScaledRadialFraction ω n x)
        atTop (𝓝 (kacRadialProfile x)) := by
  have hsparse : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientScaledRadialFraction ω (j ^ 8) x)
        atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [coefficientScaledRadialFraction, zero_mul, add_zero] using
      ae_symmetric_sparse_moving_radius_profile μ B (zero_lt_one.trans_le hB) hbound hsecond x 0 (by norm_num : (0 : ℝ) < 1 / 64)
  have hminus : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8))) atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [radialMatchingWindow, neg_one_mul, sub_eq_add_neg] using
      ae_symmetric_sparse_moving_radius_profile μ B (zero_lt_one.trans_le hB) hbound hsecond x (-1) (by norm_num : (0 : ℝ) < 1 / 64)
  have hplus : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8))) atTop (𝓝 (kacRadialProfile x)) := by
    simpa only [radialMatchingWindow, one_mul] using
      ae_symmetric_sparse_moving_radius_profile μ B (zero_lt_one.trans_le hB) hbound hsecond x 1 (by norm_num : (0 : ℝ) < 1 / 64)
  have hband : ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (coefficientSparseScaledRadialBandFraction ω x) atTop (𝓝 0) := by
    filter_upwards [hminus, hplus] with ω hωm hωp
    have heq : coefficientSparseScaledRadialBandFraction ω x = fun j =>
        coefficientRadialFraction ω (j ^ 8) (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8)) -
        coefficientRadialFraction ω (j ^ 8) (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8)) := by
      funext j
      exact coefficientSparseRadialBandFraction_eq_sub ω (1 + x / (j ^ 8 : ℕ)) j
    rw [heq]
    simpa only [sub_self] using hωp.sub hωm
  exact ae_bounded_scaled_radial_limit_of_sparse_bounds μ hB hbound hsecond x (kacRadialProfile x) hsparse hband
    (ae_symmetric_sparse_annular_tightness μ B (zero_lt_one.trans_le hB) hbound hsecond)

end Erdos522
