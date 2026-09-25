/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeAlmostSure
import Erdos522.Probability.TailSupremum
import Erdos522.Limits.PowerBlocks

/-!
# Almost-sure derivative and tail bounds on a shared coin sequence

The finite-degree supremum estimates have summable failures. The derivative
bound holds eventually at every degree; the maximal appended-tail bound holds
through every sufficiently late eighth-power block. Both statements use the
same infinite sequence and retain the finite-degree constants.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Almost every infinite sign sequence satisfies the derivative envelope at all sufficiently
    large degrees, for each fixed enlarged-disk width. -/
theorem ae_eventually_second_derivative_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(rademacherPolynomial N (rademacherPrefix N ω)).derivative.derivative.eval z‖ ≤
        DerivativeSupremum.secondDerivativeEnvelope N K := by
  let E (N : ℕ) : Set (LogMoments.SignVector N) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(rademacherPolynomial N v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (LogMoments.signMeasure N).real (E N)) := by
    apply (summable_inverse_nat_power 10 (by norm_num)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact DerivativeSupremum.second_derivative_supremum N hN hK hKN
  filter_upwards [ae_eventually_rademacherPrefix_notMem id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- Maximal tail failures are summable over consecutive eighth-power degree blocks. -/
theorem summable_eighth_power_tail_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (LogMoments.signMeasure (j ^ 8 + eighthPowerBlockLength j)).real {v |
        ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
            ‖(TailSupremum.appendedTailPolynomial
              (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}) := by
  have hsum : Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10) := by
    convert summable_inverse_nat_power 80 (by norm_num) using 1
    ext j
    push_cast
    ring
  apply hsum.of_norm_bounded_eventually_nat
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  have htr := (tendsto_natCast_atTop_atTop (R := ℝ)).comp ht
  filter_upwards [eventually_ge_atTop 60, ht.eventually_ge_atTop 4,
    htr.eventually_ge_atTop K] with j hj hN hKN
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact TailSupremum.appended_tail_supremum (j ^ 8) (eighthPowerBlockLength j) hN
    (eighthPowerBlockLength_pos j) (eighthPowerBlockLength_le_degree j hj) hK hKN

/-- Every partial appended tail in every sufficiently late block is strictly below its
    common amplitude, simultaneously throughout the closed disk. -/
theorem ae_eventually_eighth_power_tail_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(TailSupremum.appendedTailPolynomial
          (j ^ 8) (eighthPowerBlockLength j) m
          (rademacherPrefix (j ^ 8 + eighthPowerBlockLength j) ω)).eval z‖ <
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  let E (j : ℕ) : Set (LogMoments.SignVector (j ^ 8 + eighthPowerBlockLength j)) := {v |
    ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
        ‖(TailSupremum.appendedTailPolynomial
          (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}
  have h := ae_eventually_indexed_rademacherPrefix_notMem
    (fun j => j ^ 8 + eighthPowerBlockLength j) E (summable_eighth_power_tail_failures K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  exact lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)

/-- The maximal estimate controls the difference of the actual nested polynomial prefixes. -/
theorem ae_eventually_eighth_power_prefix_difference (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(rademacherPolynomial (j ^ 8 + m) (rademacherPrefix (j ^ 8 + m) ω)).eval z -
          (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)).eval z‖ <
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  filter_upwards [ae_eventually_eighth_power_tail_supremum K hK] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht := hj m hm z hz
  unfold rademacherPrefix at ht
  rw [TailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [rademacherPrefix_polynomial, rademacherPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (by omega : j ^ 8 ≤ j ^ 8 + m),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

end Erdos522
