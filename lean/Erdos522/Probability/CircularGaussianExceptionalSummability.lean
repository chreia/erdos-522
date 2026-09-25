/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianExceptionalSummability
import Erdos522.Probability.AnnularSmallDerivativeSummability
import Erdos522.Limits.PowerBlocks

/-!
# Summable circular Gaussian exceptional probabilities

The two real Gaussian coordinates contribute two energy exceptions and two
coefficient-truncation exceptions. Their exponential tails remain explicit
alongside the polynomial annular mesh failure.
-/

noncomputable section
open Filter
namespace Erdos522

/-- The complete circular Gaussian annular derivative failure envelope. -/
def circularGaussianAnnularDerivativeFailure (C : ℝ) (N : ℕ) : ℝ :=
  1 / (N : ℝ) ^ 3 + 2 / (N : ℝ) ^ 10 +
    C * (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 +
    2 * Real.exp (-3 * (N + 1 : ℝ) / 32) +
    4 * (N + 1) * Real.exp (-(N : ℝ) ^ 2 / 2)

/-- The full circular Gaussian envelope is summable along eighth-power degrees. -/
theorem summable_eighth_power_circularGaussian_annular_derivative_failure (C : ℝ) :
    Summable (fun j : ℕ => circularGaussianAnnularDerivativeFailure C (j ^ 8)) := by
  have hpoly := summable_annular_failure_envelope C
  have hpow : Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10) := by
    convert summable_inverse_nat_power 80 (by norm_num) using 1
    ext j
    push_cast
    ring
  have henergy := (summable_gaussian_lower_energy_failure.comp_injective
    strictMono_eighth_power.injective).mul_left 2
  have htrunc := (summable_gaussian_coefficient_truncation_failure.comp_injective
    strictMono_eighth_power.injective).mul_left 2
  apply (((hpoly.add hpow).add henergy).add htrunc).congr
  intro j
  unfold circularGaussianAnnularDerivativeFailure
  dsimp only [Function.comp_def]
  ring

end Erdos522
