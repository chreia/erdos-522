/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.MovingRadialScales

/-!
# Root localization with a bounded coefficient scale

A fixed coefficient bound multiplies both the curvature and appended-tail
envelopes. Logarithmic shifts of their width parameters absorb these factors
exactly, preserving the vanishing displacement at the same derivative cutoff.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- A logarithmic width shift multiplies the second-derivative envelope by `B`. -/
theorem secondDerivativeEnvelope_add_log {B : ℝ} (hB : 0 < B) (N : ℕ) (K : ℝ) :
    DerivativeSupremum.secondDerivativeEnvelope N (K + Real.log B) =
      B * DerivativeSupremum.secondDerivativeEnvelope N K := by
  unfold DerivativeSupremum.secondDerivativeEnvelope
  rw [show K + Real.log B + 4 = (K + 4) + Real.log B by ring,
    Real.exp_add, Real.exp_log hB]
  ring

/-- A half-logarithmic width shift multiplies the appended-tail envelope by `B`. -/
theorem tailAmplitude_add_half_log {B : ℝ} (hB : 0 < B) (N M : ℕ) (K : ℝ) :
    TailSupremum.tailAmplitude N M (K + Real.log B / 2) =
      B * TailSupremum.tailAmplitude N M K := by
  unfold TailSupremum.tailAmplitude
  rw [show 2 * (K + Real.log B / 2) = 2 * K + Real.log B by ring,
    Real.exp_add, Real.exp_log hB]
  ring

/-- Bounded coefficient envelopes satisfy every root-isolation inequality
eventually along eighth-power blocks. -/
theorem eventually_eighth_power_bounded_root_localization {B : ℝ} (hB : 0 < B)
    (K K' : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let a := B * TailSupremum.tailAmplitude N (eighthPowerBlockLength j) K'
      let d := regularDerivativeThreshold N
      0 < a ∧ 0 < d ∧
        4 * (B * DerivativeSupremum.secondDerivativeEnvelope N K) * a ≤ d ^ 2 ∧
        2 * a / d ≤ 1 / N ∧ 2 * a / d < radialMatchingWindow N := by
  simpa only [secondDerivativeEnvelope_add_log hB, tailAmplitude_add_half_log hB] using
    eventually_eighth_power_root_localization (K + Real.log B) (K' + Real.log B / 2)

/-- The bounded-coefficient localization radius and the moving radial target
fit inside one thin reference band throughout each late block. -/
theorem eventually_eighth_power_bounded_moving_radius_window {B : ℝ} (hB : 0 < B)
    (K' x : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
      2 * (B * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K') /
          regularDerivativeThreshold (j ^ 8) +
        |(1 + x / (j ^ 8 + m : ℕ)) - (1 + x / (j ^ 8 : ℕ))| <
          radialMatchingWindow (j ^ 8) := by
  simpa only [tailAmplitude_add_half_log hB] using
    eventually_eighth_power_moving_radius_window (K' + Real.log B / 2) x

end Erdos522
