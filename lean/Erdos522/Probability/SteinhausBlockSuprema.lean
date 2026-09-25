/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausSequence
import Erdos522.Probability.SteinhausAnnularSmallDerivativeRate
import Erdos522.Probability.AnnularSmallDerivativeSummability
import Erdos522.Probability.BoundedTailSupremum
import Erdos522.Limits.PowerBlocks

/-!
# Almost-sure Steinhaus derivative and appended-tail bounds

The Steinhaus polynomial envelopes hold on one infinite coefficient sequence.
Their boundary-grid and annular mesh exceptional probabilities are
summable along the chosen degree blocks.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Steinhaus second derivatives obey the uniform envelope eventually at every degree. -/
theorem ae_eventually_steinhaus_second_derivative_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).derivative.derivative.eval z‖ ≤
        DerivativeSupremum.secondDerivativeEnvelope N K := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(Polynomial.ofFn (N + 1) v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E N)) := by
    apply (summable_inverse_nat_power 10 (by norm_num)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have h := BoundedPolynomialSuprema.second_derivative_supremum N hN
      (fun _ => steinhausMeasure) (B := 1) (by norm_num) hK hKN
      (fun _ => ae_norm_steinhaus_eq_one.mono fun _ hz => hz.le)
      (fun _ => integral_steinhaus)
    simpa only [one_mul] using h
  filter_upwards [ae_eventually_indexed_steinhausPrefix_notMem id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- The Steinhaus maximal-tail failures are summable on eighth-power blocks. -/
theorem summable_eighth_power_steinhaus_tail_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (Measure.pi (fun _ : Fin (j ^ 8 + eighthPowerBlockLength j + 1) => steinhausMeasure)).real {g |
        ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
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
    (eighthPowerBlockLength_pos j) hM (fun _ => steinhausMeasure)
    (B := 1) (by norm_num) hK hKN
    (fun _ => ae_norm_steinhaus_eq_one.mono fun _ hz => hz.le)
    (fun _ => integral_steinhaus)
  simpa only [one_mul] using hp

/-- Every Steinhaus prefix difference is controlled throughout the enlarged disk,
simultaneously over all partial tails in every sufficiently late degree block. -/
theorem ae_eventually_eighth_power_steinhaus_prefix_difference (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(Polynomial.ofFn ((j ^ 8 + m) + 1) (coefficientPrefix (j ^ 8 + m) ω)).eval z -
          (Polynomial.ofFn ((j ^ 8) + 1) (coefficientPrefix (j ^ 8) ω)).eval z‖ <
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  let E (j : ℕ) : Set (Fin (j ^ 8 + eighthPowerBlockLength j + 1) → ℂ) := {v |
    ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
        ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}
  have h := ae_eventually_indexed_steinhausPrefix_notMem
    (fun j => j ^ 8 + eighthPowerBlockLength j) E (summable_eighth_power_steinhaus_tail_failures K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht : ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m
      (coefficientPrefix (j ^ 8 + eighthPowerBlockLength j) ω)).eval z‖ <
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold coefficientPrefix at ht
  rw [BoundedTailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [coefficientPrefix_polynomial, coefficientPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (by omega : j ^ 8 ≤ j ^ 8 + m),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

/-- Steinhaus annular small-derivative counts obey the quantitative sparse bound almost surely. -/
theorem ae_eventually_steinhaus_annular_small_derivative_count (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount (Polynomial.ofFn ((j ^ 8) + 1) (coefficientPrefix (j ^ 8) ω))
        (j ^ 8) K (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {g | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) g) N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}
  have hs : Summable (fun j : ℕ => (Measure.pi (fun _ : Fin (j ^ 8 + 1) => steinhausMeasure)).real (E (j ^ 8))) := by
    obtain ⟨C, _, hC⟩ := eventually_steinhaus_annular_small_derivative_probability
      K (K + 2) hK le_rfl
    apply (summable_annular_failure_envelope C).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually hC]
      with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  filter_upwards [ae_eventually_indexed_steinhausPrefix_notMem (fun j => j ^ 8) (fun j => E (j ^ 8)) hs] with ω hω
  exact hω.mono (fun _ hj => le_of_not_gt hj)

end Erdos522
