/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RealPowerRootMatching
import Erdos522.Probability.AnnularDerivativePowerRate

/-!
# Matching with admissible sparse-degree scales

The retuned annular derivative estimate and deterministic localization give
simultaneous root-count comparisons throughout every late degree block.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Every admissible tuple gives an actual block comparison, uniformly over the
partial block and the target radius. -/
theorem ae_eventually_admissible_block_count_bound {q t ℓ d κ : ℝ}
    (hscale : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := (N : ℝ) ^ (-1 - κ)
      ∀ m : ℕ, m ≤ realPowerBlockLength q j → ∀ r : ℝ,
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (1 - d) + m := by
  have hq2 := two_lt_of_occupation_summability hq hscale.logarithmic_pos hscale.occupation_summability
  have hq1 : 1 < q := by linarith
  filter_upwards [ae_eventually_real_power_root_matching hq1 hscale.window_pos.le
      hscale.isolation hscale.displacement_window K hK,
    ae_eventually_admissible_annular_derivative_count hscale hq K hK] with ω hM hB
  filter_upwards [hM, hB,
    (tendsto_realPowerDegree hq).eventually_ge_atTop 1] with j hjM hjB hN
  dsimp only at hjM ⊢
  intro m hm r
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast (show 0 < realPowerDegree q j by omega)
  have hthreshold : (realPowerDegree q j : ℝ) ^ (3 / 2 - ℓ) =
      (realPowerDegree q j : ℝ) ^ (3 / 2 : ℝ) /
        (realPowerDegree q j : ℝ) ^ ℓ := Real.rpow_sub hn _ _
  have h := hjM m hm r
  rw [hthreshold] at h
  change Nat.dist _ _ ≤ _ + _ + annularSmallDerivativeZeroCount _ _ _ _ + m at h
  have hr : (Nat.dist (closedZeroCount
      (rademacherPolynomial (realPowerDegree q j + m)
        (rademacherPrefix (realPowerDegree q j + m) ω)) r)
      (closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω)) r) : ℝ) ≤
      (closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          (r + (realPowerDegree q j : ℝ) ^ (-1 - κ)) -
       closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          (r - (realPowerDegree q j : ℝ) ^ (-1 - κ)) : ℕ) +
      (zeroCountIn (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          {z | |‖z‖ - 1| ≤ K / realPowerDegree q j}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
          (realPowerDegree q j) K ((realPowerDegree q j : ℝ) ^ ℓ) : ℝ) + m := by
    exact_mod_cast h
  linarith

end Erdos522
