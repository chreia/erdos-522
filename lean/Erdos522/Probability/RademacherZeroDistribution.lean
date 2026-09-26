/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RadialProfile

/-!
# The almost-sure unit-disk law for Rademacher polynomials

For the polynomial prefixes of one infinite sequence of independent fair
signs, the fraction of zeros in the closed unit disk converges almost surely
to one half. The zero count includes algebraic multiplicities. The law is the
radial profile at the coordinate zero, where the Kac profile equals one half.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Almost surely, one half of the zeros of the nested Rademacher polynomial
prefixes lie in the closed unit disk in the limit. -/
theorem erdos_522 :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  filter_upwards [radial_profile] with ω hω
  simpa only [rademacherScaledRadialFraction, rademacherRadialFraction,
    zero_div, add_zero, kacRadialProfile_zero, rademacherPrefix_polynomial] using hω 0

end Erdos522
