/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianMovingRadialProfile
import Erdos522.Probability.MonotoneProfileConvergence

/-!
# The almost-sure radial profile

For one infinite circular complex Gaussian sequence, the empirical distribution of
`N (|z| - 1)` converges at every real coordinate to the derivative of the Kac
logarithmic variance profile. The convergence is uniform on compact sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- Each empirical scaled radial distribution is nondecreasing, including degree zero. -/
theorem monotone_circularGaussianScaledRadialFraction (ω : (ℕ → ℂ)) (N : ℕ) :
    Monotone (circularGaussianScaledRadialFraction ω N) := by
  exact scaled_closedZeroCount_mono (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)) N

/-- Fixed-coordinate convergence on a single probability-one event for every rational coordinate. -/
theorem ae_circularGaussian_rational_radial_profile :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ q : ℚ,
      Tendsto (fun N : ℕ => circularGaussianScaledRadialFraction ω N q) atTop (𝓝 (kacRadialProfile q)) := by
  apply ae_all_iff.mpr
  intro q
  exact ae_circularGaussian_scaled_radial_profile q

/-- Almost surely, the scaled radial root distribution converges at every real coordinate. -/
theorem circularGaussian_radial_profile :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ x : ℝ,
      Tendsto (fun N : ℕ => circularGaussianScaledRadialFraction ω N x) atTop (𝓝 (kacRadialProfile x)) := by
  exact ae_tendsto_of_monotone_rational_convergence
    circularGaussianScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_circularGaussianScaledRadialFraction) continuous_kacRadialProfile
    (ae_all_iff.mp (ae_circularGaussian_rational_radial_profile))

/-- Almost surely, the full radial profile converges uniformly on every compact real set. -/
theorem circularGaussian_radial_profile_compact_uniform :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (circularGaussianScaledRadialFraction ω) kacRadialProfile atTop s := by
  exact ae_tendstoUniformlyOn_of_monotone_pointwise
    circularGaussianScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_circularGaussianScaledRadialFraction) continuous_kacRadialProfile
    (circularGaussian_radial_profile)

/-- The compact-uniform statement in explicit multiplicity-counted polynomial notation. -/
theorem circularGaussian_radial_profile_compact_uniform_prefixes :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s := by
  have hprofile := circularGaussian_radial_profile_compact_uniform
  unfold circularGaussianScaledRadialFraction circularGaussianRadialFraction at hprofile
  simpa only [coefficientPrefix_polynomial] using hprofile

/-- For one infinite circular complex Gaussian sequence, half the zeros lie in the closed
unit disk asymptotically, with algebraic multiplicity. -/
theorem circularGaussian_zero_distribution :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  filter_upwards [circularGaussian_radial_profile] with ω hω
  simpa only [circularGaussianScaledRadialFraction, circularGaussianRadialFraction,
    zero_div, add_zero, kacRadialProfile_zero, coefficientPrefix_polynomial] using hω 0

end Erdos522
