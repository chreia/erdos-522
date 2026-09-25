/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AdmissibleSparseRadialProfile

/-!
# Radial profiles along rounded real-power degrees

For every real `q > 8/3`, logarithmic concentration and Jensen secants give
the radial profile on the schedule `⌊j^q⌋`. The target radius may move with
the degree, provided its scaled displacement has a limit.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The sparse radial profile holds at every deterministic asymptotic scaled radius. -/
theorem ae_real_power_radial_profile_of_scaled_radius_limit {q : ℝ}
    (hq : 8 / 3 < q) (r : ℕ → ℝ) (x : ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (realPowerDegree q j) (r (realPowerDegree q j)))
        atTop (𝓝 (kacRadialProfile x)) :=
  ae_real_power_radial_profile (by linarith : 2 < q) r x hr

end Erdos522
