/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HarmonicRestriction
import Erdos522.Probability.RademacherStrongLaw

/-!
# The almost-sure unit-disk law for Rademacher polynomials

For the polynomial prefixes of one infinite sequence of independent fair
signs, the fraction of zeros in the closed unit disk converges almost surely
to one half. The zero count includes algebraic multiplicities.
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
        atTop (𝓝 (1 / 2 : ℝ)) :=
  erdos_522_of_harmonic_restriction one_le_harmonicRestrictionConstant harmonic_l2_restriction

end Erdos522
