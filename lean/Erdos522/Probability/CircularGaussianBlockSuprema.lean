/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianSequence
import Erdos522.Probability.CircularGaussianAnnularSmallDerivative
import Erdos522.Probability.CircularGaussianSuprema
import Erdos522.Limits.PowerBlocks

/-!
# Almost-sure circular Gaussian derivative and appended-tail bounds

The circular Gaussian polynomial envelopes hold on one infinite coefficient sequence.
Their extra energy and truncation probabilities are summable, as are the
polynomial failures in the boundary-grid estimates.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Circular Gaussian second derivatives obey the uniform envelope eventually at every degree. -/
theorem ae_eventually_circularGaussian_second_derivative_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).derivative.derivative.eval z‖ ≤
        2 * DerivativeSupremum.secondDerivativeEnvelope N K := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ 2 * DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(Polynomial.ofFn (N + 1) v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (E N)) := by
    have hsum := ((summable_inverse_nat_power 10 (by norm_num)).add
      summable_gaussian_coefficient_truncation_failure).mul_left 2
    apply hsum.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (circularGaussian_second_derivative_supremum N hN hK hKN).trans_eq (by ring)
  filter_upwards [ae_eventually_indexed_circularGaussianPrefix_notMem id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- The circular Gaussian maximal-tail failures are summable on eighth-power blocks. -/
theorem summable_eighth_power_circularGaussian_tail_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (Measure.pi (fun _ : Fin (j ^ 8 + eighthPowerBlockLength j + 1) => circularComplexGaussian)).real {g |
        ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
          2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
            ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m g).eval z‖}) := by
  have hpow : Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10) := by
    convert summable_inverse_nat_power 80 (by norm_num) using 1
    ext j
    push_cast
    ring
  have htrunc := (summable_gaussian_coefficient_truncation_failure.comp_injective
    strictMono_eighth_power.injective).mul_left 4
  apply ((hpow.mul_left 2).add htrunc).of_norm_bounded_eventually_nat
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [eventually_ge_atTop 60, ht.eventually_ge_atTop 4,
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht).eventually_ge_atTop K] with j hj hN hKN
  have hM := eighthPowerBlockLength_le_degree j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hp := circularGaussian_appended_tail_supremum (j ^ 8) (eighthPowerBlockLength j) hN
    (eighthPowerBlockLength_pos j) hM hK hKN
  apply hp.trans
  have hM' : (eighthPowerBlockLength j : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) := by exact_mod_cast hM
  have he := Real.exp_nonneg (-((j ^ 8 : ℕ) : ℝ) ^ 2 / 2)
  dsimp only [Function.comp_def]
  calc
    2 / ((j ^ 8 : ℕ) : ℝ) ^ 10 +
        4 * (((j ^ 8 : ℕ) : ℝ) + eighthPowerBlockLength j + 1) *
          Real.exp (-((j ^ 8 : ℕ) : ℝ) ^ 2 / 2) ≤
      2 / ((j ^ 8 : ℕ) : ℝ) ^ 10 +
        4 * (2 * (((j ^ 8 : ℕ) : ℝ) + 1)) *
          Real.exp (-((j ^ 8 : ℕ) : ℝ) ^ 2 / 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ he
      linarith
    _ = _ := by ring

/-- Every circular Gaussian prefix difference is controlled throughout the enlarged disk,
simultaneously over all partial tails in every sufficiently late degree block. -/
theorem ae_eventually_eighth_power_circularGaussian_prefix_difference (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(Polynomial.ofFn (j ^ 8 + m + 1) (coefficientPrefix (j ^ 8 + m) ω)).eval z -
          (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)).eval z‖ <
          2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  let E (j : ℕ) : Set (Fin (j ^ 8 + eighthPowerBlockLength j + 1) → ℂ) := {v |
    ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
      2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
        ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}
  have h := ae_eventually_indexed_circularGaussianPrefix_notMem
    (fun j => j ^ 8 + eighthPowerBlockLength j) E (summable_eighth_power_circularGaussian_tail_failures K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht : ‖(BoundedTailSupremum.appendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m
      (coefficientPrefix (j ^ 8 + eighthPowerBlockLength j) ω)).eval z‖ <
      2 * TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold coefficientPrefix at ht
  rw [BoundedTailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [coefficientPrefix_polynomial, coefficientPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (by omega : j ^ 8 ≤ j ^ 8 + m),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

/-- Circular Gaussian annular small-derivative counts obey the quantitative sparse bound almost surely. -/
theorem ae_eventually_circularGaussian_annular_small_derivative_count (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
        (j ^ 8) K (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {g | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) g) N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}
  have hs : Summable (fun j : ℕ => (Measure.pi (fun _ : Fin (j ^ 8 + 1) => circularComplexGaussian)).real (E (j ^ 8))) := by
    apply (summable_eighth_power_circularGaussian_annular_derivative_failure
      (circularGaussianAnnularFailureConstant K)).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually
      (eventually_circularGaussian_annular_small_derivative_probability K hK)] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  filter_upwards [ae_eventually_indexed_circularGaussianPrefix_notMem (fun j => j ^ 8) (fun j => E (j ^ 8)) hs] with ω hω
  exact hω.mono (fun _ hj => le_of_not_gt hj)

end Erdos522
