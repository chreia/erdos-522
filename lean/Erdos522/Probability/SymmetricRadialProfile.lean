/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricMovingRadialProfile
import Erdos522.Probability.MonotoneProfileConvergence

/-!
# The almost-sure radial profile

For one infinite bounded centrally symmetric coefficient sequence, the empirical distribution of
`N (|z| - 1)` converges at every real coordinate to the derivative of the Kac
logarithmic variance profile. The convergence is uniform on compact sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- Each empirical scaled radial distribution is nondecreasing, including degree zero. -/
theorem monotone_coefficientScaledRadialFraction (ω : (ℕ → ℂ)) (N : ℕ) :
    Monotone (coefficientScaledRadialFraction ω N) := by
  exact scaled_closedZeroCount_mono (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)) N

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {B : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hsecond

/-- Fixed-coordinate convergence on a single probability-one event for every rational coordinate. -/
theorem ae_bounded_rational_radial_profile :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ q : ℚ,
      Tendsto (fun N : ℕ => coefficientScaledRadialFraction ω N q) atTop (𝓝 (kacRadialProfile q)) := by
  apply ae_all_iff.mpr
  intro q
  exact ae_bounded_scaled_radial_profile μ hB hbound hsecond q

/-- Almost surely, the scaled radial root distribution converges at every real coordinate. -/
theorem bounded_symmetric_radial_profile :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ x : ℝ,
      Tendsto (fun N : ℕ => coefficientScaledRadialFraction ω N x) atTop (𝓝 (kacRadialProfile x)) := by
  exact ae_tendsto_of_monotone_rational_convergence
    coefficientScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_coefficientScaledRadialFraction) continuous_kacRadialProfile
    (ae_all_iff.mp (ae_bounded_rational_radial_profile μ hB hbound hsecond))

/-- Almost surely, the full radial profile converges uniformly on every compact real set. -/
theorem bounded_symmetric_radial_profile_compact_uniform :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (coefficientScaledRadialFraction ω) kacRadialProfile atTop s := by
  exact ae_tendstoUniformlyOn_of_monotone_pointwise
    coefficientScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_coefficientScaledRadialFraction) continuous_kacRadialProfile
    (bounded_symmetric_radial_profile μ hB hbound hsecond)

/-- The compact-uniform statement in explicit multiplicity-counted polynomial notation. -/
theorem bounded_symmetric_radial_profile_compact_uniform_prefixes :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s := by
  have hprofile := bounded_symmetric_radial_profile_compact_uniform μ hB hbound hsecond
  unfold coefficientScaledRadialFraction coefficientRadialFraction at hprofile
  simpa only [coefficientPrefix_polynomial] using hprofile

/-- For one infinite bounded centrally symmetric coefficient sequence, half the zeros lie in the closed
unit disk asymptotically, with algebraic multiplicity. -/
theorem bounded_symmetric_zero_distribution :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  filter_upwards [bounded_symmetric_radial_profile μ hB hbound hsecond] with ω hω
  simpa only [coefficientScaledRadialFraction, coefficientRadialFraction,
    zero_div, add_zero, kacRadialProfile_zero, coefficientPrefix_polynomial] using hω 0

end Erdos522
