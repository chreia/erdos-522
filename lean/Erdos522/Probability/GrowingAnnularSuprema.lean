/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GrowingAnnularDerivativeCount
import Erdos522.Probability.BlockSupremaAlmostSure

/-!
# Derivative and tail suprema at varying annular widths

The finite supremum bounds have width-independent exceptional probabilities.
Consequently their almost-sure forms apply to deterministic width sequences
whenever the finite degree conditions hold eventually.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Second derivatives obey their finite envelope for an admissible varying width. -/
theorem ae_eventually_second_derivative_supremum_of_width_sequence (K : ℕ → ℝ)
    (hK : ∀ᶠ N : ℕ in atTop, 0 ≤ K N ∧ K N + 1 ≤ N) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖ ≤ 1 + (K N + 1) / N →
      ‖(rademacherPolynomial N (rademacherPrefix N ω)).derivative.derivative.eval z‖ ≤
        DerivativeSupremum.secondDerivativeEnvelope N (K N) := by
  let E (N : ℕ) : Set (LogMoments.SignVector N) := {v | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K N + 1) / N ∧ DerivativeSupremum.secondDerivativeEnvelope N (K N) <
      ‖(rademacherPolynomial N v).derivative.derivative.eval z‖}
  have hs : Summable (fun N => (LogMoments.signMeasure N).real (E N)) := by
    apply (summable_inverse_nat_power 10 (by norm_num)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 2, hK] with N hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact DerivativeSupremum.second_derivative_supremum N hN hKN.1 hKN.2
  filter_upwards [ae_eventually_rademacherPrefix_notMem id E hs] with ω hω
  filter_upwards [hω] with N hN
  intro z hz
  exact le_of_not_gt (fun hlarge => hN ⟨z, hz, hlarge⟩)

/-- Every partial block obeys the maximal tail bound for an admissible varying width. -/
theorem ae_eventually_real_power_prefix_difference_of_width_sequence {q : ℝ} (hq : 1 < q)
    (K : ℕ → ℝ) (hK : ∀ᶠ N : ℕ in atTop, 0 ≤ K N ∧ K N ≤ N) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      ∀ m : ℕ, m ≤ realPowerBlockLength q j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K N / N →
        ‖(rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)).eval z -
          (rademacherPolynomial N (rademacherPrefix N ω)).eval z‖ <
          TailSupremum.tailAmplitude N (realPowerBlockLength q j) (K N) := by
  let E (j : ℕ) : Set (LogMoments.SignVector (realPowerDegree q j + realPowerBlockLength q j)) := {v |
    ∃ m : ℕ, m ≤ realPowerBlockLength q j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K (realPowerDegree q j) / realPowerDegree q j ∧
      TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) (K (realPowerDegree q j)) ≤
        ‖(TailSupremum.appendedTailPolynomial (realPowerDegree q j) (realPowerBlockLength q j) m v).eval z‖}
  have hq0 : 0 < q := by linarith
  have hs : Summable (fun j : ℕ =>
      (LogMoments.signMeasure (realPowerDegree q j + realPowerBlockLength q j)).real (E j)) := by
    have hsum : Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 10) := by
      simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_ofNat, one_div] using
        summable_realPowerDegree_rpow hq0 (a := -(10 : ℝ)) (by linarith)
    apply hsum.of_norm_bounded_eventually_nat
    have ht := tendsto_realPowerDegree hq0
    filter_upwards [eventually_realPowerBlockLength_le_degree hq, ht.eventually_ge_atTop 4,
      ht.eventually hK] with j hj hN hKN
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact TailSupremum.appended_tail_supremum _ _ hN (realPowerBlockLength_pos hq.le j) hj hKN.1 hKN.2
  have h := ae_eventually_indexed_rademacherPrefix_notMem
    (fun j => realPowerDegree q j + realPowerBlockLength q j) E hs
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  dsimp only
  intro m hm z hz
  have ht : ‖(TailSupremum.appendedTailPolynomial
      (realPowerDegree q j) (realPowerBlockLength q j) m
      (rademacherPrefix (realPowerDegree q j + realPowerBlockLength q j) ω)).eval z‖ <
      TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) (K (realPowerDegree q j)) :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold rademacherPrefix at ht
  rw [TailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [rademacherPrefix_polynomial, rademacherPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (Nat.le_add_right _ _),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

/-- The enlarged logarithmic width satisfies every derivative and tail degree condition. -/
theorem eventually_logarithmicAnnularWidth_add_one_le_degree :
    ∀ᶠ N : ℕ in atTop, logarithmicAnnularWidth N + 1 ≤ N := by
  have ht := tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 1)
    (by norm_num) (by norm_num) 1 0
  simp only [pow_one, pow_zero, zero_mul, Real.exp_zero, mul_one, Real.rpow_one] at ht
  filter_upwards [eventually_ge_atTop 1,
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN hratio
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ((div_lt_one hn).mp hratio).le

end Erdos522
