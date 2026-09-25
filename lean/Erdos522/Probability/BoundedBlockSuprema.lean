/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CoefficientSequence
import Erdos522.Probability.AnnularSmallDerivativeSummability
import Erdos522.Probability.BoundedTailSupremum
import Erdos522.Limits.PowerBlocks

/-!
# Almost-sure derivative and appended-tail bounds for bounded coefficients

The polynomial envelopes for bounded mean-zero coefficients hold on one infinite coefficient sequence.
Their boundary-grid and annular mesh exceptional probabilities are
summable along the chosen degree blocks.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hmean : (∫ z, z ∂μ) = 0)

include hB hbound hmean

/-- Second derivatives obey the uniform envelope eventually at every degree. -/
theorem ae_eventually_bounded_second_derivative_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).derivative.derivative.eval z‖ ≤
        B * DerivativeSupremum.secondDerivativeEnvelope N K := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ B * DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(Polynomial.ofFn (N + 1) v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E N)) := by
    apply (summable_inverse_nat_power 10 (by norm_num)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have h := BoundedPolynomialSuprema.second_derivative_supremum N hN
      (fun _ => μ) hB hK hKN (fun _ => hbound) (fun _ => hmean)
    exact h
  filter_upwards [ae_eventually_indexed_coefficientPrefix_notMem μ id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- The maximal-tail failures are summable on eighth-power blocks. -/
theorem summable_eighth_power_bounded_tail_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (Measure.pi (fun _ : Fin (j ^ 8 + eighthPowerBlockLength j + 1) => μ)).real {g |
        ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
          B * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
            ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m g).eval z‖}) := by
  have hpow : Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10) := by
    convert summable_inverse_nat_power 80 (by norm_num) using 1
    ext j
    push_cast
    ring
  apply hpow.of_norm_bounded_eventually_nat
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [eventually_ge_atTop 60, ht.eventually_ge_atTop 4,
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht).eventually_ge_atTop K] with j hj hN hKN
  have hM := eighthPowerBlockLength_le_degree j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hp := BoundedTailSupremum.appended_tail_supremum
    (j ^ 8) (eighthPowerBlockLength j) hN
    (eighthPowerBlockLength_pos j) hM (fun _ => μ)
    hB hK hKN (fun _ => hbound) (fun _ => hmean)
  exact hp

/-- Every prefix difference is controlled throughout the enlarged disk,
simultaneously over all partial tails in every sufficiently late degree block. -/
theorem ae_eventually_eighth_power_bounded_prefix_difference (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(Polynomial.ofFn ((j ^ 8 + m) + 1) (coefficientPrefix (j ^ 8 + m) ω)).eval z -
          (Polynomial.ofFn ((j ^ 8) + 1) (coefficientPrefix (j ^ 8) ω)).eval z‖ <
          B * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  let E (j : ℕ) : Set (Fin (j ^ 8 + eighthPowerBlockLength j + 1) → ℂ) := {v |
    ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
      B * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
        ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}
  have h := ae_eventually_indexed_coefficientPrefix_notMem μ
    (fun j => j ^ 8 + eighthPowerBlockLength j) E (summable_eighth_power_bounded_tail_failures μ hB hbound hmean K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht : ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m
      (coefficientPrefix (j ^ 8 + eighthPowerBlockLength j) ω)).eval z‖ <
      B * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold coefficientPrefix at ht
  rw [BoundedTailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [coefficientPrefix_polynomial, coefficientPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (by omega : j ^ 8 ≤ j ^ 8 + m),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht


end Erdos522
