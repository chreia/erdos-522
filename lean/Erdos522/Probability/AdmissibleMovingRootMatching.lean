/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AdmissibleRootMatching
import Erdos522.Limits.RealPowerRadialShift
import Erdos522.Stability.RadialCountTransport

/-!
# Moving-radius matching at admissible sparse-degree scales

The root motion and target drift fit within a doubled sparse radial band.
The probability-one event supplies every fixed real radial coordinate.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Matching at `1+x/n` throughout a real-power degree block. -/
theorem ae_admissible_moving_block_count_bound {q t ℓ d κ : ℝ}
    (hscale : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let r := 1 + x / N
      let w := (N : ℝ) ^ (-1 - κ)
      ∀ m : ℕ, m ≤ realPowerBlockLength q j →
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) : ℝ) ≤
          2 * (closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (1 - d) + m := by
  have hq2 := two_lt_of_occupation_summability hq hscale.logarithmic_pos hscale.occupation_summability
  have hq1 : 1 < q := by linarith
  have hκ : κ < 1 / q := by
    have hℓ := hscale.derivative_pos
    have h := hscale.displacement_window
    have hi : 0 < 1 / q := by positivity
    rw [show 1 / (2 * q) = (1 / q) / 2 by ring] at h
    linarith
  filter_upwards [ae_eventually_real_power_root_matching hq1 hscale.window_pos.le
      hscale.isolation hscale.displacement_window K hK,
    ae_eventually_admissible_annular_derivative_count hscale hq K hK] with ω hM hB
  intro x
  filter_upwards [hM, hB, eventually_real_power_radial_shift_le hq1 hκ x,
    (tendsto_realPowerDegree hq).eventually_ge_atTop 1] with j hjM hjB hjshift hN
  dsimp only at hjM ⊢
  intro m hm
  let N := realPowerDegree q j
  let P := rademacherPolynomial N (rademacherPrefix N ω)
  let Q := rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)
  let r := 1 + x / N
  let s := 1 + x / (N + m : ℕ)
  let w := (N : ℝ) ^ (-1 - κ)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hthreshold : (N : ℝ) ^ (3 / 2 - ℓ) = (N : ℝ) ^ (3 / 2 : ℝ) / (N : ℝ) ^ ℓ :=
    Real.rpow_sub hn _ _
  have hmatch := hjM m hm s
  rw [hthreshold] at hmatch
  change Nat.dist (closedZeroCount Q s) (closedZeroCount P s) ≤
    closedZeroCount P (s + w) - closedZeroCount P (s - w) +
      zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ + annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ ℓ) + m
        at hmatch
  have hmatch' : Nat.dist (closedZeroCount Q s) (closedZeroCount P s) ≤
      closedZeroCount P (s + w) - closedZeroCount P (s - w) +
        (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ + annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ ℓ) + m) := by
    omega
  have htransport := closedZeroCount_transport_bound P Q
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hjshift m hm) hmatch'
  have hr : (Nat.dist (closedZeroCount Q s) (closedZeroCount P r) : ℝ) ≤
      2 * (closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) : ℕ) +
        ((zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) +
          (annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ ℓ) : ℝ) + m) := by
    dsimp only [s, r, w, N] at *
    exact_mod_cast htransport
  have hbad : (annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ ℓ) : ℝ) ≤ (N : ℝ) ^ (1 - d) := hjB
  change (Nat.dist (closedZeroCount Q s) (closedZeroCount P r) : ℝ) ≤ _
  change (Nat.dist (closedZeroCount Q s) (closedZeroCount P r) : ℝ) ≤
    2 * (closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) : ℕ) +
      (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (1 - d) + m
  linarith

end Erdos522
