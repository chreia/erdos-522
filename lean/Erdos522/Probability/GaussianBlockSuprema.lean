/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianSequence
import Erdos522.Probability.GaussianExceptionalSummability
import Erdos522.Probability.GaussianTailSupremum
import Erdos522.Limits.PowerBlocks

/-!
# Almost-sure Gaussian derivative and appended-tail bounds

The Gaussian polynomial envelopes hold on one infinite coefficient sequence.
Their extra energy and truncation probabilities are summable, as are the
polynomial failures in the boundary-grid estimates.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Gaussian second derivatives obey the uniform envelope eventually at every degree. -/
theorem ae_eventually_gaussian_second_derivative_supremum (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(gaussianPolynomial N (gaussianPrefix N ω)).derivative.derivative.eval z‖ ≤
        DerivativeSupremum.secondDerivativeEnvelope N K := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℝ) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(gaussianPolynomial N v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (gaussianCoefficientMeasure (N + 1)).real (E N)) := by
    apply ((summable_inverse_nat_power 10 (by norm_num)).add
      summable_gaussian_coefficient_truncation_failure).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1)] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact gaussian_second_derivative_supremum N hN hK hKN
  filter_upwards [ae_eventually_indexed_gaussianPrefix_notMem id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- The Gaussian maximal-tail failures are summable on eighth-power blocks. -/
theorem summable_eighth_power_gaussian_tail_failures (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (gaussianCoefficientMeasure (j ^ 8 + eighthPowerBlockLength j + 1)).real {g |
        ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
            ‖(gaussianAppendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m g).eval z‖}) := by
  have hpow : Summable (fun j : ℕ => 1 / ((j ^ 8 : ℕ) : ℝ) ^ 10) := by
    convert summable_inverse_nat_power 80 (by norm_num) using 1
    ext j
    push_cast
    ring
  have htrunc := (summable_gaussian_coefficient_truncation_failure.comp_injective
    strictMono_eighth_power.injective).mul_left 2
  apply (hpow.add htrunc).of_norm_bounded_eventually_nat
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [eventually_ge_atTop 60, ht.eventually_ge_atTop 4,
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht).eventually_ge_atTop K] with j hj hN hKN
  have hM := eighthPowerBlockLength_le_degree j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hp := gaussian_appended_tail_supremum (j ^ 8) (eighthPowerBlockLength j) hN
    (eighthPowerBlockLength_pos j) hM hK hKN
  apply hp.trans
  have hM' : (eighthPowerBlockLength j : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) := by exact_mod_cast hM
  have he := Real.exp_nonneg (-((j ^ 8 : ℕ) : ℝ) ^ 2 / 2)
  dsimp only [Function.comp_def]
  nlinarith

/-- Every Gaussian prefix difference is controlled throughout the enlarged disk,
simultaneously over all partial tails in every sufficiently late degree block. -/
theorem ae_eventually_eighth_power_gaussian_prefix_difference (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) →
        ‖(gaussianPolynomial (j ^ 8 + m) (gaussianPrefix (j ^ 8 + m) ω)).eval z -
          (gaussianPolynomial (j ^ 8) (gaussianPrefix (j ^ 8) ω)).eval z‖ <
          TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K := by
  let E (j : ℕ) : Set (Fin (j ^ 8 + eighthPowerBlockLength j + 1) → ℝ) := {v |
    ∃ m : ℕ, m ≤ eighthPowerBlockLength j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / (j ^ 8 : ℕ) ∧
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K ≤
        ‖(gaussianAppendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m v).eval z‖}
  have h := ae_eventually_indexed_gaussianPrefix_notMem
    (fun j => j ^ 8 + eighthPowerBlockLength j) E (summable_eighth_power_gaussian_tail_failures K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht : ‖(gaussianAppendedTailPolynomial (j ^ 8) (eighthPowerBlockLength j) m
      (gaussianPrefix (j ^ 8 + eighthPowerBlockLength j) ω)).eval z‖ <
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold gaussianPrefix at ht
  rw [gaussianAppendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [gaussianPrefix_polynomial, gaussianPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (by omega : j ^ 8 ≤ j ^ 8 + m),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

/-- Gaussian annular small-derivative counts obey the quantitative sparse bound almost surely. -/
theorem ae_eventually_gaussian_annular_small_derivative_count (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount (gaussianPolynomial (j ^ 8) (gaussianPrefix (j ^ 8) ω))
        (j ^ 8) K (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℝ) := {g | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (gaussianPolynomial N g) N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}
  have hs : Summable (fun j : ℕ => (gaussianCoefficientMeasure (j ^ 8 + 1)).real (E (j ^ 8))) := by
    apply (summable_eighth_power_gaussian_annular_derivative_failure
      (annularSmallDerivativeFailureConstant 1 K (K + 3))).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually
      (eventually_gaussian_annular_small_derivative_probability K hK)] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  filter_upwards [ae_eventually_indexed_gaussianPrefix_notMem (fun j => j ^ 8) (fun j => E (j ^ 8)) hs] with ω hω
  exact hω.mono (fun _ hj => le_of_not_gt hj)

end Erdos522
