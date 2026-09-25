/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.MonotoneProfileLimits
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Almost-sure convergence of monotone profiles

A countable intersection makes rational-point convergence simultaneous.
Monotonicity and continuity then extend convergence to all real coordinates
and make it uniform on every compact set, on one event of full measure.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Erdos522

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Almost-sure convergence at each rational coordinate determines a continuous
limit at every real coordinate on one event of full measure. -/
theorem ae_tendsto_of_monotone_rational_convergence
    (f : Ω → ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hmono : ∀ᵐ ω ∂μ, ∀ n, Monotone (f ω n)) (hg : Continuous g)
    (hq : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q))) :
    ∀ᵐ ω ∂μ, ∀ x : ℝ, Tendsto (fun n => f ω n x) atTop (𝓝 (g x)) := by
  filter_upwards [hmono, ae_all_iff.mpr hq] with ω hω hqω
  exact tendsto_monotone_of_rational_convergence (f ω) g hω hg hqω

/-- Almost-sure pointwise convergence of monotone profiles to a continuous limit
is uniform on every compact set on the same event of full measure. -/
theorem ae_tendstoUniformlyOn_of_monotone_pointwise
    (f : Ω → ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hmono : ∀ᵐ ω ∂μ, ∀ n, Monotone (f ω n)) (hg : Continuous g)
    (hpoint : ∀ᵐ ω ∂μ, ∀ x : ℝ,
      Tendsto (fun n => f ω n x) atTop (𝓝 (g x))) :
    ∀ᵐ ω ∂μ, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (f ω) g atTop s := by
  filter_upwards [hmono, hpoint] with ω hω hpointω
  intro s hs
  exact tendstoUniformlyOn_of_monotone_pointwise (f ω) g hω hg hpointω hs

end Erdos522
