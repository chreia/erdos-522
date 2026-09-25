/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.MovingRadialProfile
import Erdos522.Probability.MonotoneProfileConvergence
import Erdos522.Analysis.HarmonicRestriction

/-!
# The almost-sure radial profile

For one infinite Rademacher sequence, the empirical distribution of
`N (|z| - 1)` converges at every real coordinate to the derivative of the Kac
logarithmic variance profile. The convergence is uniform on compact sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- Each empirical scaled radial distribution is nondecreasing, including degree zero. -/
theorem monotone_rademacherScaledRadialFraction (ω : RademacherSequence) (N : ℕ) :
    Monotone (rademacherScaledRadialFraction ω N) := by
  exact scaled_closedZeroCount_mono (rademacherPolynomial N (rademacherPrefix N ω)) N

/-- Fixed-coordinate convergence on a single probability-one event for every rational coordinate. -/
theorem ae_rational_radial_profile :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ q : ℚ,
      Tendsto (fun N : ℕ => rademacherScaledRadialFraction ω N q) atTop (𝓝 (kacRadialProfile q)) := by
  apply ae_all_iff.mpr
  intro q
  exact ae_scaled_radial_profile_of_harmonic_restriction
    one_le_harmonicRestrictionConstant harmonic_l2_restriction q

/-- Almost surely, the scaled radial root distribution converges at every real coordinate. -/
theorem radial_profile :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ x : ℝ,
      Tendsto (fun N : ℕ => rademacherScaledRadialFraction ω N x) atTop (𝓝 (kacRadialProfile x)) := by
  exact ae_tendsto_of_monotone_rational_convergence
    rademacherScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_rademacherScaledRadialFraction) continuous_kacRadialProfile
    (ae_all_iff.mp (ae_rational_radial_profile))

/-- Almost surely, the full radial profile converges uniformly on every compact real set. -/
theorem radial_profile_compact_uniform :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (rademacherScaledRadialFraction ω) kacRadialProfile atTop s := by
  exact ae_tendstoUniformlyOn_of_monotone_pointwise
    rademacherScaledRadialFraction kacRadialProfile
    (ae_of_all _ monotone_rademacherScaledRadialFraction) continuous_kacRadialProfile
    (radial_profile)

/-- The compact-uniform statement in explicit multiplicity-counted polynomial notation. -/
theorem radial_profile_compact_uniform_prefixes :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s := by
  have hprofile := radial_profile_compact_uniform
  unfold rademacherScaledRadialFraction rademacherRadialFraction at hprofile
  simpa only [rademacherPrefix_polynomial] using hprofile

end Erdos522
