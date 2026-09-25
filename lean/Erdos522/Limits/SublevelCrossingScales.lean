/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.RootLocalizationScales

/-!
# Radial scales for crossing sublevel components

The localization window is negligible on the reciprocal-degree scale. It
therefore absorbs both a regular root's localization radius and any target
radius whose scaled displacement from the unit circle tends to zero.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The matching window is smaller than every fixed reciprocal-degree width. -/
theorem tendsto_scaled_radialMatchingWindow :
    Tendsto (fun N : ℕ => (N : ℝ) * radialMatchingWindow N) atTop (𝓝 0) := by
  have h := tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 64)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold radialMatchingWindow
  nth_rw 2 [← Real.rpow_one (N : ℝ)]
  rw [← Real.rpow_add hn]
  congr 1
  norm_num

/-- The window and the target displacement together fit inside any prescribed
positive reciprocal-degree band. -/
theorem eventually_sublevel_crossing_window {δ : ℝ} (hδ : 0 < δ)
    (r : ℕ → ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      radialMatchingWindow N + |r N - 1| < δ / (2 * N) := by
  have htotal := tendsto_scaled_radialMatchingWindow.add hr.abs
  simp only [abs_zero, add_zero] at htotal
  filter_upwards [htotal.eventually_lt_const (by positivity : (0 : ℝ) < δ / 2),
    eventually_ge_atTop 1] with N hsmall hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [abs_mul, abs_of_pos hn] at hsmall
  calc
    _ < (δ / 2) / N := by
      apply (lt_div_iff₀ hn).mpr
      nlinarith
    _ = _ := by ring

/-- All Taylor-localization conditions hold along eighth-power blocks with
the moving target inside a prescribed reciprocal-degree band. -/
theorem eventually_eighth_power_sublevel_crossing_scales (K K₀ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℕ → ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 0)) :
    ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let a := TailSupremum.tailAmplitude N (eighthPowerBlockLength j) K₀
      let d := regularDerivativeThreshold N
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧
        2 * a / d + |r N - 1| < δ / (2 * N) := by
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [eventually_eighth_power_root_localization K K₀,
    hp.eventually (eventually_sublevel_crossing_window hδ r hr)] with j hlocal hwindow
  dsimp only at hlocal hwindow ⊢
  refine ⟨hlocal.1, hlocal.2.1, hlocal.2.2.1, hlocal.2.2.2.1, ?_⟩
  exact (add_lt_add_of_lt_of_le hlocal.2.2.2.2 le_rfl).trans hwindow

/-- Finitely many moving circles share one deterministic localization cutoff. -/
theorem eventually_eighth_power_sublevel_crossing_scales_finite
    {ι : Type*} [Finite ι] (K K₀ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (r : ℕ → ι → ℝ)
    (hr : ∀ i, Tendsto (fun N : ℕ => (N : ℝ) * (r N i - 1)) atTop (𝓝 0)) :
    ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let a := TailSupremum.tailAmplitude N (eighthPowerBlockLength j) K₀
      let d := regularDerivativeThreshold N
      0 < a ∧ 0 < d ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧
        ∀ i, 2 * a / d + |r N i - 1| < δ / (2 * N) := by
  have hall := eventually_all.mpr (fun i =>
    eventually_eighth_power_sublevel_crossing_scales K K₀ hδ (fun N => r N i) (hr i))
  filter_upwards [eventually_eighth_power_root_localization K K₀, hall] with j hlocal hscales
  dsimp only at hlocal hscales ⊢
  exact ⟨hlocal.1, hlocal.2.1, hlocal.2.2.1, hlocal.2.2.2.1,
    fun i => (hscales i).2.2.2.2⟩

end Erdos522
