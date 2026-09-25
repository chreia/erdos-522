/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseRadialLimits

/-!
# The Rademacher radial strong law from harmonic restriction

The finite coefficient-uniform harmonic restriction estimate supplies
logarithmic concentration. Sparse thin-band limits and annular tightness then
combine with root matching to give the strong law for the full nested sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- A perturbation of order `N^(-1-κ)` has vanishing displacement on the radial scale. -/
theorem tendsto_scaled_power_radius (s : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((1 + s * (N : ℝ) ^ (-1 - κ)) - 1)) atTop (𝓝 0) := by
  have ht := (tendsto_nat_rpow_neg hκ).const_mul s
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (N : ℝ) * (N : ℝ) ^ (-1 - κ) = (N : ℝ) ^ (-κ) := by
    nth_rw 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    s * (N : ℝ) ^ (-κ) = s * ((N : ℝ) * (N : ℝ) ^ (-1 - κ)) := by rw [hp]
    _ = _ := by ring

/-- Sparse closed-disk fractions converge at every fixed signed power-scale perturbation. -/
theorem ae_sparse_power_radius_fraction_limit {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (s : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 + s * ((j ^ 8 : ℕ) : ℝ) ^ (-1 - κ))) atTop (𝓝 (1 / 2 : ℝ)) :=
  ae_sparse_radial_fraction_limit_of_scaled_radius_zero hC hR
    (fun N => 1 + s * (N : ℝ) ^ (-1 - κ)) (tendsto_scaled_power_radius s hκ)

/-- Harmonic restriction implies the radial strong law for multiplicity-counted
zeros in the closed unit disk, using one infinite Rademacher sequence. -/
theorem erdos_522_of_harmonic_restriction {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix (fun k => sign (ω k)) (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  have hminus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 - radialMatchingWindow (j ^ 8))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [radialMatchingWindow, neg_one_mul, sub_eq_add_neg] using
      ae_sparse_power_radius_fraction_limit hC hR (-1) (by norm_num : (0 : ℝ) < 1 / 64)
  have hplus : ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 + radialMatchingWindow (j ^ 8))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [radialMatchingWindow, one_mul] using
      ae_sparse_power_radius_fraction_limit hC hR 1 (by norm_num : (0 : ℝ) < 1 / 64)
  have ht := ae_radial_count_limit_of_two_radius_bounds 1 (1 / 2) hminus hplus
    (ae_sparse_annular_tightness_of_harmonic_restriction hC hR)
  simpa only [rademacherRadialFraction, rademacherPrefix_polynomial] using ht

end Erdos522
