/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianMovingRadialProfile
import Erdos522.Probability.MonotoneProfileConvergence

/-!
# The almost-sure radial profile

For one infinite real Gaussian sequence, the empirical distribution of
`N (|z| - 1)` converges at every real coordinate to the derivative of the Kac
logarithmic variance profile. The convergence is uniform on compact sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- Each empirical scaled radial distribution is nondecreasing, including degree zero. -/
theorem monotone_gaussianScaledRadialFraction (ω : (ℕ → ℝ)) (N : ℕ) :
    Monotone (gaussianScaledRadialFraction ω N) := by
  exact scaled_closedZeroCount_mono (gaussianPolynomial N (gaussianPrefix N ω)) N

/-- Fixed-coordinate convergence on a single probability-one event for every rational coordinate. -/
theorem ae_gaussian_rational_radial_profile :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ q : ℚ,
      Tendsto (fun N : ℕ => gaussianScaledRadialFraction ω N q) atTop (𝓝 (kacRadialProfile q)) := by
  apply ae_all_iff.mpr
  intro q
  exact ae_gaussian_scaled_radial_profile q

/-- Almost surely, the scaled radial root distribution converges at every real coordinate. -/
theorem gaussian_radial_profile :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ x : ℝ,
      Tendsto (fun N : ℕ => gaussianScaledRadialFraction ω N x) atTop (𝓝 (kacRadialProfile x)) := by
  exact ae_tendsto_of_monotone_rational_convergence
    gaussianScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_gaussianScaledRadialFraction) continuous_kacRadialProfile
    (ae_all_iff.mp (ae_gaussian_rational_radial_profile))

/-- Almost surely, the full radial profile converges uniformly on every compact real set. -/
theorem gaussian_radial_profile_compact_uniform :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (gaussianScaledRadialFraction ω) kacRadialProfile atTop s := by
  exact ae_tendstoUniformlyOn_of_monotone_pointwise
    gaussianScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_gaussianScaledRadialFraction) continuous_kacRadialProfile
    (gaussian_radial_profile)

/-- The compact-uniform statement in explicit multiplicity-counted polynomial notation. -/
theorem gaussian_radial_profile_compact_uniform_prefixes :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => (ω k : ℂ)) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s := by
  have hprofile := gaussian_radial_profile_compact_uniform
  unfold gaussianScaledRadialFraction gaussianRadialFraction at hprofile
  simpa only [gaussianPrefix_polynomial] using hprofile

/-- For one infinite real Gaussian sequence, half the zeros lie in the closed
unit disk asymptotically, with algebraic multiplicity. -/
theorem gaussian_zero_distribution :
    ∀ᵐ ω ∂gaussianSequenceMeasure,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix (fun k => (ω k : ℂ)) (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  filter_upwards [gaussian_radial_profile] with ω hω
  simpa only [gaussianScaledRadialFraction, gaussianRadialFraction,
    zero_div, add_zero, kacRadialProfile_zero, gaussianPrefix_polynomial] using hω 0

end Erdos522
