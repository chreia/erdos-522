/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SublevelCrossingProbability
import Erdos522.Probability.RademacherStrongLaw
import Erdos522.Limits.BlockTailAmplitude

/-!
# Sublevel components meeting the nearby inner and outer circles

The two circles `1 ± N^(-1-κ)` have vanishing scaled displacement for every
positive `κ`. For each level sequence below a fixed maximal-tail amplitude,
one deterministic envelope controls both crossing counts with summable
exceptions. In particular, every fixed sublevel threshold has this property.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The nearby outer and inner radii, indexed by a Boolean sign. -/
def nearbyCircleRadius (κ : ℝ) (N : ℕ) (outer : Bool) : ℝ :=
  1 + (if outer then 1 else -1) * (N : ℝ) ^ (-1 - κ)

theorem tendsto_scaled_nearbyCircleRadius {κ : ℝ} (hκ : 0 < κ) (outer : Bool) :
    Tendsto (fun N : ℕ => (N : ℝ) * (nearbyCircleRadius κ N outer - 1)) atTop (𝓝 0) :=
  tendsto_scaled_power_radius (if outer then 1 else -1) hκ

/-- The two nearby circles have one vanishing crossing-count envelope with
summable exceptions, for every sublevel sequence below a fixed block amplitude. -/
theorem nearby_circle_sublevel_counts_summable (K₀ : ℝ) (a : ℕ → ℝ)
    (ha : ∀ᶠ j : ℕ in atTop,
      a (j ^ 8) ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 ≤ ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      Summable (fun j : ℕ => rademacherSequenceMeasure.real {ω | ∃ outer : Bool,
        ε j < (sublevelComponentZeroCount
          (polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) (j ^ 8))
          (a (j ^ 8)) (nearbyCircleRadius κ (j ^ 8) outer) : ℝ) / (j ^ 8 : ℕ)}) := by
  simpa only [rademacherPrefix_polynomial] using
    exists_summable_sublevel_crossing_envelope K₀ a ha (nearbyCircleRadius κ)
      (tendsto_scaled_nearbyCircleRadius hκ)

/-- Every fixed sublevel threshold has negligible crossing root fractions
outside one summable exceptional sequence, simultaneously at both nearby circles. -/
theorem fixed_level_nearby_circle_sublevel_counts_summable (a₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 ≤ ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      Summable (fun j : ℕ => rademacherSequenceMeasure.real {ω | ∃ outer : Bool,
        ε j < (sublevelComponentZeroCount
          (polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) (j ^ 8))
          a₀ (nearbyCircleRadius κ (j ^ 8) outer) : ℝ) / (j ^ 8 : ℕ)}) :=
  nearby_circle_sublevel_counts_summable 0 (fun _ => a₀)
    (eventually_const_le_eighth_power_tailAmplitude a₀ 0) hκ

/-- The normalized crossing counts at both circles tend to zero almost surely. -/
theorem ae_nearby_circle_sublevel_counts_tendsto_zero (K₀ : ℝ) (a : ℕ → ℝ)
    (ha : ∀ᶠ j : ℕ in atTop,
      a (j ^ 8) ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ outer : Bool,
      Tendsto (fun j : ℕ => (sublevelComponentZeroCount
        (polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) (j ^ 8))
        (a (j ^ 8)) (nearbyCircleRadius κ (j ^ 8) outer) : ℝ) / (j ^ 8 : ℕ)) atTop (𝓝 0) := by
  simpa only [rademacherPrefix_polynomial] using
    ae_sublevel_crossing_fractions_tendsto_zero K₀ a ha (nearbyCircleRadius κ)
      (tendsto_scaled_nearbyCircleRadius hκ)

end Erdos522
